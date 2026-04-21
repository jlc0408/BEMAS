import tkinter as tk
from tkinter import messagebox, scrolledtext
try:
    from tkinter import simpledialog
except ImportError:
    simpledialog = None
import configparser
import os
import sys
import csv
import re
import datetime
import threading
import time
import shutil
import subprocess
import socket
from collections import defaultdict
from playwright.sync_api import sync_playwright


# =====================================================
# データディレクトリ（.exe / .py と同じフォルダ）
# =====================================================
# PyInstaller でビルドした .exe の場合: sys.executable の親フォルダ
# 通常の .py 実行の場合      : __file__ の親フォルダ
# → どちらも「起動ファイルと同じ場所」に統一する
#
# GitHubにはコード (.py / .ini テンプレート) のみ置き、
# config.ini / rules/ / pdfs/ / processed/ / log/ はこのフォルダに格納する。
if getattr(sys, 'frozen', False):
    # PyInstaller .exe
    DATA_DIR = os.path.dirname(sys.executable)
else:
    # 通常の Python 実行
    DATA_DIR = os.path.dirname(os.path.abspath(__file__))

def data_path(*parts) -> str:
    """DATA_DIR 基準の絶対パスを返す。例: data_path('rules', 'west.ini')"""
    return os.path.join(DATA_DIR, *parts)


# =====================================================
# 設定読み込み
# =====================================================

def load_config():
    config = configparser.ConfigParser(interpolation=None)
    path = data_path('config.ini')
    if not os.path.exists(path):
        messagebox.showerror("エラー", f"config.ini が見つかりません。\n({path})")
        return None
    config.read(path, encoding='utf-8')
    return config['BEAMS']


def save_config(url, account, password):
    config = configparser.ConfigParser(interpolation=None)
    path = data_path('config.ini')
    if os.path.exists(path):
        config.read(path, encoding='utf-8')
    if 'BEAMS' not in config:
        config['BEAMS'] = {}
    config['BEAMS']['URL']      = url
    config['BEAMS']['ACCOUNT']  = account
    config['BEAMS']['PASSWORD'] = password
    with open(path, 'w', encoding='utf-8') as f:
        config.write(f)


def load_field_ids():
    config = configparser.ConfigParser(interpolation=None)
    path = data_path('field_ids.ini')
    if not os.path.exists(path):
        messagebox.showerror("エラー", f"field_ids.ini が見つかりません。\n({path})")
        return None
    config.read(path, encoding='utf-8')
    return config


def load_pdf_layout():
    config = configparser.ConfigParser(interpolation=None)
    path = data_path('pdf_layout.ini')
    if not os.path.exists(path):
        messagebox.showerror("エラー", f"pdf_layout.ini が見つかりません。\n({path})")
        return None
    config.read(path, encoding='utf-8')
    return config


def load_all_rules() -> dict:
    """
    rules/ フォルダ内の全 .ini ファイルを自動認識して読み込む。
    戻り値: { "ファイル名（拡張子なし）": ConfigParser, ... }

    フォルダが存在しない場合や ini がない場合は空辞書を返す。
    後方互換: livecamera_west.ini が rules/ の外（DATA_DIR直下）に
    直置きされている場合も読み込む。
    """
    rules_dir = data_path("rules")
    os.makedirs(rules_dir, exist_ok=True)

    loaded = {}

    for fname in sorted(os.listdir(rules_dir)):
        if not fname.lower().endswith(".ini"):
            continue
        key = os.path.splitext(fname)[0]
        cfg = configparser.ConfigParser(interpolation=None)
        cfg.read(os.path.join(rules_dir, fname), encoding='utf-8')
        loaded[key] = cfg

    # 後方互換: DATA_DIR直下に livecamera_west.ini があれば追加読み込み
    legacy = data_path("livecamera_west.ini")
    if os.path.exists(legacy) and "livecamera_west" not in loaded:
        cfg = configparser.ConfigParser(interpolation=None)
        cfg.read(legacy, encoding='utf-8')
        loaded["livecamera_west"] = cfg

    return loaded


def get_active_rule(all_rules: dict) -> tuple:
    """
    ロード済みルール辞書から「最初の1件」をアクティブルールとして返す。
    戻り値: (rule_name: str, config: ConfigParser) or (None, None)
    将来的に複数ルール切り替えUIを追加する際の拡張ポイント。
    """
    for name, cfg in all_rules.items():
        return name, cfg
    return None, None


def ensure_dirs():
    for d in ("pdfs", "processed", "log", "rules"):
        os.makedirs(data_path(d), exist_ok=True)


# =====================================================
# 住所の全角変換
# =====================================================

# 半角→全角変換テーブル（記号・数字・英字）
# 半角ASCII (0x21-0x7E) を全角 (0xFF01-0xFF5E) に変換するテーブル
# 空白(0x20)は全角スペース(0x3000)に対応するが住所では不要なので除外
_HAN2ZEN = {i: i - 0x20 + 0xFF00 for i in range(0x21, 0x7F)}

def clean_text(text: str) -> str:
    """
    PDF抽出文字列から不可視制御文字を除去する。
    ゼロ幅スペース(U+200B)・BOM(U+FEFF)・ソフトハイフン(U+00AD)などが
    Salesforceの詳細入力画面で □ として表示される問題を防ぐ。
    """
    if not text:
        return text
    # 除去する不可視文字の範囲:
    #   U+0000-U+0008: 制御文字（改行・タブ以外）
    #   U+000B-U+000C: 垂直タブ・改ページ
    #   U+000E-U+001F: 制御文字
    #   U+00AD: ソフトハイフン
    #   U+200B-U+200F: ゼロ幅スペース等
    #   U+2028-U+2029: ライン/パラグラフセパレータ
    #   U+FEFF: BOM / ゼロ幅ノーブレークスペース
    _INVISIBLE = re.compile(
        r'[\x00-\x08\x0b\x0c\x0e-\x1f\xad\u200b-\u200f\u2028\u2029\ufeff]'
    )
    return _INVISIBLE.sub('', text)


def to_fullwidth(text: str) -> str:
    """
    住所フィールド向けに半角記号・数字を全角に変換する。
    ただし郵便番号のハイフンは変換しない（呼び出し元で使い分け）。
    """
    if not text:
        return text
    return text.translate(_HAN2ZEN)


def normalize_address(text: str) -> str:
    """
    番地・建物フィールド用の全角正規化。
    '-'（ハイフン）と '−'（全角マイナス）を全角ハイフン '－' に統一し、
    数字も全角にする。
    """
    if not text:
        return text
    # まず全角化
    result = text.translate(_HAN2ZEN)
    # 半角ハイフン variants → 全角ハイフン
    result = re.sub(r'[-－ｰ—–−—–]', '－', result)
    return result


# =====================================================
# HeartRails Geo API：郵便番号 → 町域名（丁目含む）
# =====================================================

def fetch_town_by_zip(zip_code: str) -> str:
    import urllib.request
    import json

    zip_clean = re.sub(r'[^\d]', '', zip_code)
    if len(zip_clean) != 7:
        return ""
    try:
        url = (f"https://geoapi.heartrails.com/api/json"
               f"?method=searchByPostal&postal={zip_clean}")
        with urllib.request.urlopen(url, timeout=5) as resp:
            result = json.loads(resp.read().decode("utf-8"))
        locations = result.get("response", {}).get("location", [])
        if locations:
            return locations[0].get("town", "")
    except Exception:
        pass
    return ""


# =====================================================
# 住所分割（大字通称名基準）
# =====================================================

def split_after_oaza(full_address: str, oaza: str) -> dict:
    result = {"azacho": "", "banchi": "", "building": ""}

    idx = full_address.find(oaza)
    if idx == -1:
        result["banchi"] = full_address
        return result

    remain = full_address[idx + len(oaza):]

    aza_patterns = [
        re.compile(r'^([0-9０-９]+丁目)'),
        re.compile(r'^([^0-9０-９]+丁目)'),
        re.compile(r'^([^0-9０-９]+)(?=[0-9０-９])'),
    ]

    pure_number  = re.match(r'^[0-9０-９]', remain)
    starts_chome = re.match(r'^[0-9０-９]+丁目', remain)

    if pure_number and not starts_chome:
        # 番地＋建物名をすべて banchi に入れる（building フィールドは使わない）
        result["banchi"] = remain.strip()
    else:
        for pat in aza_patterns:
            m = pat.match(remain)
            if m:
                result["azacho"] = m.group(1).strip()
                remain = remain[m.end():]
                break
        # 番地＋建物名をすべて banchi に入れる
        result["banchi"] = remain.strip()

    return result


# =====================================================
# CSV ロガー
# =====================================================

class CsvLogger:
    COLUMNS = [
        "処理日時", "ファイル名",
        "申込日",
        "会社名(カナ)", "会社名(漢字)",
        "担当者名カナ", "担当者名漢字",
        "連絡先電話番号",
        "郵便番号", "住所(元)", "大字通称名",
        "字名丁目", "番地", "建物",
        "申込商品1", "申込商品2",
        "販売パートナー名",
        "料金請求方法", "請求先郵便番号", "請求先住所", "請求先建物",
        "請求先CMR番号", "請求先氏名カナ", "請求先氏名",
        "支払い方法", "工事費請求方法",
        "REQ番号",
        "ステータス", "備考",
    ]

    def __init__(self, log_dir=None):
        self.log_dir = log_dir or data_path("log")
        date_str = datetime.date.today().strftime("%Y%m%d")
        self.csv_path = os.path.join(self.log_dir, f"beams_log_{date_str}.csv")
        self._ensure_header()

    def _ensure_header(self):
        if not os.path.exists(self.csv_path):
            with open(self.csv_path, "w", newline="", encoding="utf-8-sig") as f:
                csv.writer(f).writerow(self.COLUMNS)

    def write(self, filename: str, pdf_data: dict, status: str, note: str = "", req_number: str = ""):
        ap = pdf_data.get("address_parts", {})
        row = [
            datetime.datetime.now().strftime("%Y/%m/%d %H:%M:%S"),
            filename,
            pdf_data.get("apply_date", ""),
            pdf_data.get("company_kana", ""),
            pdf_data.get("company_name", ""),
            pdf_data.get("staff_kana", ""),
            pdf_data.get("staff_name", ""),
            pdf_data.get("phone", ""),
            pdf_data.get("zip_code", ""),
            pdf_data.get("address", ""),
            pdf_data.get("oaza", ""),
            ap.get("azacho", ""),
            ap.get("banchi", ""),
            ap.get("building", ""),
            pdf_data.get("plan1", ""),
            pdf_data.get("plan2", ""),
            pdf_data.get("partner_name", ""),
            pdf_data.get("billing_method", ""),
            pdf_data.get("billing_zip", ""),
            pdf_data.get("billing_address", ""),
            pdf_data.get("billing_building", ""),
            pdf_data.get("billing_cmr", ""),
            pdf_data.get("billing_name_kana", ""),
            pdf_data.get("billing_name", ""),
            pdf_data.get("payment_method", ""),
            pdf_data.get("construction_billing", ""),
            req_number,
            status,
            note,
        ]
        with open(self.csv_path, "a", newline="", encoding="utf-8-sig") as f:
            csv.writer(f).writerow(row)


# =====================================================
# PDF 解析（label_top 方式）
# =====================================================

class PdfExtractor:
    def __init__(self, layout_config: configparser.ConfigParser):
        self.rules = self._parse_rules(layout_config)

    def _parse_rules(self, config) -> list:
        rules = []
        if 'FIELDS' not in config:
            return rules
        for key, val in config['FIELDS'].items():
            rule = {"key": key, "label_top": None, "page": None,
                    "tolerance": 6.0, "x0_min": 130.0, "x0_max": 460.0,
                    "strip_suffix": "様"}
            for part in val.split(','):
                part = part.strip()
                if '=' not in part:
                    continue
                k, v = part.split('=', 1)
                k, v = k.strip().lower(), v.strip()
                if k == 'label_top':      rule['label_top'] = float(v)
                elif k == 'page':         rule['page'] = int(v)
                elif k == 'tolerance':    rule['tolerance'] = float(v)
                elif k == 'x0_min':       rule['x0_min'] = float(v)
                elif k == 'x0_max':       rule['x0_max'] = float(v)
                elif k == 'strip_suffix': rule['strip_suffix'] = v
            if rule['label_top'] is not None:
                rules.append(rule)
        return rules

    def extract(self, pdf_path: str) -> dict:
        import pdfplumber

        pages_words = []
        with pdfplumber.open(pdf_path) as pdf:
            for page in pdf.pages:
                pages_words.append(page.extract_words())

        all_words = [w for pw in pages_words for w in pw]

        data = {}
        for rule in self.rules:
            key, anchor, tol = rule["key"], rule["label_top"], rule["tolerance"]

            if rule["page"] is not None:
                page_idx = rule["page"] - 1
                target_words = pages_words[page_idx] if page_idx < len(pages_words) else []
            else:
                target_words = all_words

            row = [w for w in target_words
                   if abs(w['top'] - anchor) <= tol
                   and rule["x0_min"] <= w['x0'] < rule["x0_max"]]

            row.sort(key=lambda w: w['x0'])
            if key in ('staff_kana', 'staff_name'):
                value = " ".join(w['text'] for w in row).strip()
            else:
                value = "".join(w['text'] for w in row).strip()

            sfx = rule["strip_suffix"]
            if sfx and value.endswith(sfx):
                value = value[:-len(sfx)].strip()

            if key == 'zip_code':
                value = value.replace("〒", "").strip()
            if key == 'company_kana':
                value = value.replace("　", "").replace(" ", "").strip()
            if key == 'phone':
                if '：' in value: value = value.split('：', 1)[1].strip()
                if '（' in value: value = value.split('（')[0].strip()

            # 不可視制御文字を除去（Salesforce表示で□になる問題対策）
            data[key] = clean_text(value)

        # address の直下行（建物名・階数など）を結合する
        # PDFによっては住所が2行に分かれる（例: 2丁目2-55 / 手塚ビル1階）
        addr_rule = next((r for r in self.rules if r['key'] == 'address'), None)
        if addr_rule and data.get('address'):
            addr_top    = addr_rule['label_top']
            addr_x0_min = addr_rule['x0_min']
            addr_x0_max = addr_rule['x0_max']
            addr_page_i = (addr_rule['page'] or 1) - 1
            tgt_words   = pages_words[addr_page_i] if addr_page_i < len(pages_words) else []
            # 直下行: top が addr_top + 7〜15 の範囲・同じ x0 エリア
            next_row = sorted(
                [w for w in tgt_words
                 if 7 <= w['top'] - addr_top <= 15
                 and addr_x0_min <= w['x0'] < addr_x0_max],
                key=lambda w: w['x0']
            )
            if next_row:
                extra = " ".join(w['text'] for w in next_row).strip()
                data['address'] = (data['address'] + extra).strip()

        addr = data.get("address", "")
        oaza = data.get("oaza", "")

        if addr:
            if oaza == addr or not oaza:
                m = re.search(r'(大字[^\d０-９]+?(?:甲|乙|丙|丁)?(?=[0-9０-９]|$))', addr)
                if m:
                    oaza = m.group(1)
                else:
                    m2 = re.search(r'(?:市|区|郡|町|村)(.+?)(?=[0-9０-９])', addr)
                    oaza = m2.group(1).strip() if m2 else ""
                data["oaza"] = oaza

            if oaza:
                data["address_parts"] = split_after_oaza(addr, oaza)
            else:
                data["address_parts"] = {"azacho": "", "banchi": addr, "building": ""}

        data.update(self.extract_page2(pdf_path))

        return data

    def extract_page2(self, pdf_path: str) -> dict:
        import pdfplumber

        result = {
            "billing_method": "", "billing_zip": "", "billing_address": "",
            "billing_building": "", "billing_cmr": "", "billing_name_kana": "",
            "billing_name": "", "payment_method": "", "construction_billing": "",
        }

        TOL   = 6.0
        X_MIN = 420.0

        TOPS = {
            "billing_method":        133.3,
            "billing_zip":           151.3,
            "billing_address":       160.3,
            "billing_building":      169.3,
            "billing_cmr":           169.3,
            "billing_name_kana":     178.3,
            "billing_name":          187.3,
            "payment_method":        196.3,
            "construction_billing":  205.3,
        }

        with pdfplumber.open(pdf_path) as pdf:
            if len(pdf.pages) < 2:
                return result
            words = pdf.pages[1].extract_words()

        def get_row_text(target_top, x0_min=X_MIN, x0_max=9999.0):
            matched = [w for w in words
                       if abs(w['top'] - target_top) <= TOL
                       and x0_min <= w['x0'] < x0_max]
            matched.sort(key=lambda w: w['x0'])
            return "".join(w['text'] for w in matched).strip()

        def after_colon(text):
            if '：' in text: return clean_text(text.split('：', 1)[1].strip())
            if ':' in text:  return clean_text(text.split(':', 1)[1].strip())
            return clean_text(text)

        result["billing_method"]       = after_colon(get_row_text(TOPS["billing_method"]))
        result["billing_zip"]          = clean_text(get_row_text(TOPS["billing_zip"]).replace("〒", "").strip())
        result["billing_address"]      = clean_text(get_row_text(TOPS["billing_address"]))
        result["billing_building"]     = clean_text(get_row_text(TOPS["billing_building"], x0_max=510.0))
        result["billing_cmr"]          = clean_text(get_row_text(TOPS["billing_cmr"],      x0_min=510.0))
        result["billing_name_kana"]    = after_colon(get_row_text(TOPS["billing_name_kana"]))
        result["billing_name"]         = after_colon(get_row_text(TOPS["billing_name"]))
        result["payment_method"]       = after_colon(get_row_text(TOPS["payment_method"]))
        result["construction_billing"] = after_colon(get_row_text(TOPS["construction_billing"]))

        return result


# =====================================================
# BEAMS 操作
# =====================================================

class BeamsOperator:
    def __init__(self, page, today_str: str,
                 field_ids: configparser.ConfigParser, log_func,
                 live_config: configparser.ConfigParser = None,
                 on_req_acquired=None):
        self.page = page
        self.today_str = today_str
        self.fids = field_ids
        self.log = log_func
        self.live = live_config  # livecamera_west.ini
        self.on_req_acquired = on_req_acquired  # REQ番号取得時のコールバック(str) -> None

    def _popup_with_retry(self, open_fn, work_fn, label="", max_retry=2):
        """
        ポップアップを開いて操作する汎用リトライラッパー。

        open_fn()  : ポップアップを開く処理。戻り値 = popup page オブジェクト
        work_fn(p) : ポップアップ page を受け取って操作する処理
        label      : ログ識別用ラベル
        max_retry  : 失敗時の最大リトライ回数

        フォーカス喪失・DOM消失・タイムアウトが起きた場合:
          1. ポップアップを閉じる（あれば）
          2. メインページをフロントに持ってくる
          3. open_fn() からやり直す
        """
        popup = None
        for attempt in range(1, max_retry + 2):  # 1〜max_retry+1回試行
            try:
                # メインページのフォーカスを確保してからポップアップを開く
                try:
                    self.page.bring_to_front()
                    self.page.wait_for_timeout(300)
                except Exception:
                    pass

                popup = open_fn()

                # ポップアップ自身にフォーカスを移す
                try:
                    popup.bring_to_front()
                    popup.wait_for_timeout(300)
                except Exception:
                    pass

                # 操作実行
                work_fn(popup)
                return  # 成功

            except Exception as e:
                err_short = str(e)[:120]
                if attempt <= max_retry:
                    self.log(f"  [{label}] [試行{attempt}失敗] {err_short}")
                    self.log(f"  [{label}] ポップアップをリセットしてリトライします...")
                    # ポップアップが残っていれば閉じる
                    try:
                        if popup and not popup.is_closed():
                            popup.close()
                    except Exception:
                        pass
                    popup = None
                    self.page.wait_for_timeout(1000)
                else:
                    raise RuntimeError(
                        f"[{label}] {max_retry}回リトライ後も失敗: {err_short}"
                    ) from e

    def _fid(self, section: str, key: str):
        val = self.fids.get(section, key, fallback=None)
        if val is None or val.strip().upper().startswith("TODO"):
            return None
        return val.strip()

    def _fill(self, field_id: str, value: str, tab: bool = False):
        t = self.page.locator(f"id={field_id}")
        t.scroll_into_view_if_needed()
        t.fill(value)
        if tab:
            t.press("Tab")

    def _fill_or_skip(self, section: str, key: str, label: str,
                      data: dict, tab: bool = False):
        fid   = self._fid(section, key)
        value = data.get(key, "")
        if not value:
            return
        if fid:
            self._fill(fid, value, tab=tab)
            self.log(f" - {label}: {value}")
        else:
            self.log(f" - {label} 取得済み（フィールドID未設定・スキップ）: {value}")

    def _fill_zip_with_azacho(self,
                              fid_zip, fid_aza, fid_addr,
                              zip_val, full_address, building,
                              label="", btn_title="", btn_index=0,
                              page=None,
                              banchi_only="",
                              return_result=False):
        """
        郵便番号入力 → エラー判定 → 字名丁目確定 → 番地以降を address に入力。
        address に入力する値は normalize_address() で全角に統一する。
        """
        prefix = f"[{label}] " if label else ""
        chosen_oaza = ""
        page = page or self.page

        # ① 郵便番号入力（JS setValueでBEAMSに確実に認識させる）
        z = page.locator(f'[id="{fid_zip}"]')
        z.scroll_into_view_if_needed()
        # JS で value をセットしてから Tab を押す
        page.evaluate(
            """([fid, val]) => {
                var el = document.getElementById(fid);
                if (!el) return;
                el.value = val;
                el.dispatchEvent(new Event('input', {bubbles: true}));
                el.dispatchEvent(new Event('change', {bubbles: true}));
            }""",
            [fid_zip, zip_val]
        )
        z.press("Tab")
        self.log(f"  {prefix}郵便番号入力: {zip_val}")
        self.wait_for_loading()

        # ② 常にルックアップポップアップを開いて字丁目を選択する
        # 一意確定ルートは廃止 - エラー有無に関わらず必ずポップアップで選択
        azacho_filled = ""

        # Tab を押してBEAMSのエラーを確定させる（複数候補があればエラー表示）
        z.press("Tab")
        page.wait_for_timeout(300)
        self.log(f"  {prefix}ルックアップを開きます")

        if True:  # 常にポップアップを開く（以前の if error_visible と同じ構造を維持）
            # ── ルックアップボタン特定（title属性直接指定）─────────────
            popup_btn = page.locator(f'img[title="{btn_title}"]').nth(btn_index)
            self.log(f"  {prefix}ルックアップボタン: 「{btn_title}」[{btn_index}]")

            expected_town = fetch_town_by_zip(zip_val)
            self.log(f"  {prefix}期待 town: 「{expected_town}」")

            # ボタン表示待機 + DOM安定待機
            # 2件目以降はBEAMSの再描画でボタンがDOMから一時消失することがある。
            # visible になった後、さらにDOMに安定して存在するまでポーリングで待つ。
            try:
                popup_btn.wait_for(state="visible", timeout=10000)
                # DOM安定確認: 最大3秒間、0.3秒ごとにattached状態を確認
                for _st in range(10):
                    try:
                        if popup_btn.count() > 0:
                            popup_btn.scroll_into_view_if_needed()
                            break
                    except Exception:
                        page.wait_for_timeout(300)
                else:
                    # それでも失敗する場合はスクロールをスキップして続行
                    self.log(f"  {prefix}[警告] スクロールスキップ（DOM再描画中）")
                self.log(f"  {prefix}ルックアップボタン確認済み")
            except Exception as btn_err:
                self.log(f"  {prefix}[警告] ボタン表示待機タイムアウト: {btn_err}")

            # ポップアップが開く前にBEAMSのJS初期化を待つ
            page.wait_for_timeout(1000)

            # フォーカスをEdgeに戻す（ユーザーが別ウィンドウを操作していた場合の対策）
            try:
                page.bring_to_front()
                page.wait_for_timeout(300)
            except Exception:
                pass

            # ポップアップ開く
            # 試行順: ① JS evaluate click（実績あり） → ② 通常 click → ③ dispatch_event('click')
            popup = None
            for _attempt, _click_fn in enumerate([
                lambda: page.evaluate("(el) => el.click()", popup_btn.element_handle()),
                lambda: popup_btn.click(),
                lambda: popup_btn.dispatch_event('click'),
            ], 1):
                try:
                    with page.expect_popup(timeout=5000) as popup_info:
                        _click_fn()
                    popup = popup_info.value
                    self.log(f"  {prefix}ポップアップ開成功（試行{_attempt}）")
                    break
                except Exception as _e:
                    self.log(f"  {prefix}[試行{_attempt}] ポップアップ未開: {str(_e)[:60]}")
            if popup is None:
                raise RuntimeError(f"{prefix}ルックアップポップアップが3回試行後も開きませんでした")
            popup.wait_for_load_state("domcontentloaded")
            # ポップアップ自身にフォーカスを移す
            try:
                popup.bring_to_front()
                popup.wait_for_timeout(300)
            except Exception:
                pass

            # フレーム探索
            target_frame = popup
            try:
                popup.wait_for_selector("a.dataCell", timeout=3000)
            except Exception:
                found = False
                for frame in popup.frames:
                    try:
                        frame.wait_for_selector("a.dataCell", timeout=5000)
                        target_frame = frame
                        found = True
                        self.log(f"  {prefix}フレーム内にデータ発見: {frame.url}")
                        break
                    except Exception:
                        continue
                if not found:
                    self.log(f"  {prefix}[警告] どのフレームにも dataCell が見つかりません")
                    for fi, frame in enumerate(popup.frames):
                        self.log(f"  {prefix}[DEBUG] frame[{fi}] url={frame.url}")

            self.log(f"  {prefix}選択ウィンドウ表示")

            # 候補テーブル走査
            # 優先度: ① full_address との双方向部分一致 → ② expected_town との一致
            #         → ③ azacho が空白の行（blank） → ④ 最初の dataCell
            target_link   = None
            blank_link    = None
            first_link    = None   # どれにも合わなかった場合の最終フォールバック
            best_len      = -1
            seen_ids      = set()
            selected_oaza  = ""
            selected_azacho = ""   # クリックした行の azacho を記録
            blank_oaza    = ""
            first_oaza    = ""
            rows = target_frame.locator("table tr").all()

            for ri, row in enumerate(rows):
                cells = row.locator("td").all()
                if len(cells) != 4:
                    continue

                link = row.locator("a.dataCell").first
                if link.count() == 0:
                    continue

                onclick_val = link.get_attribute("onclick") or ""
                id_parts    = re.findall(r"'([^']*)'", onclick_val)
                record_id   = id_parts[4] if len(id_parts) > 4 else ""
                if record_id in seen_ids:
                    self.log(f"  {prefix}[DEBUG] row[{ri}] 重複スキップ (id={record_id})")
                    continue
                seen_ids.add(record_id)

                oaza     = cells[2].inner_text().strip()
                azacho   = cells[3].inner_text().strip()
                combined = oaza + azacho

                # first_link: 最初の有効行（全フォールバック用）
                if first_link is None:
                    first_link = link
                    first_oaza = oaza

                # ③ azacho が空の行（blank）→ best_len 比較から除外して専用フォールバックへ
                if azacho == "":
                    if blank_link is None:
                        blank_link = link
                        blank_oaza = oaza
                    # azacho空行は①②の候補として使わない（丁目が必要な場合に誤選択を防ぐ）
                    self.log(f"  {prefix}[DEBUG] row[{ri}] oaza=「{oaza}」 azacho=「（空）」→ blank候補")
                    continue

                # ① 双方向部分一致（full_address ↔ combined）
                if combined:
                    _match = (combined in full_address) or (full_address and full_address in combined)
                    # 全角・半角を正規化して再試行
                    if not _match:
                        _fa_norm = full_address.translate(_HAN2ZEN)
                        _co_norm = combined.translate(_HAN2ZEN)
                        _match = (_co_norm in _fa_norm) or (_fa_norm in _co_norm)
                    _match_str = "✔マッチ" if _match else "✗不一致"
                    self.log(f"  {prefix}[DEBUG] row[{ri}] oaza=「{oaza}」 azacho=「{azacho}」 combined=「{combined}」 {_match_str} (full_address=「{full_address[:40]}…」)")
                    if _match and len(combined) > best_len:
                        target_link    = link
                        best_len       = len(combined)
                        selected_oaza  = oaza
                        selected_azacho = azacho

                # ② expected_town を含む行（full_address マッチがない場合のサブ候補）
                if target_link is None and expected_town and (
                    expected_town in oaza or oaza in expected_town or
                    expected_town in azacho
                ):
                    self.log(f"  {prefix}[DEBUG] row[{ri}] expected_town=「{expected_town}」でサブ候補選択")
                    target_link    = link
                    best_len       = len(combined)
                    selected_oaza  = oaza
                    selected_azacho = azacho

            # 優先順位: ①target → ③blank → ④first
            self.log(f"  {prefix}[DEBUG] 選択結果: target={'あり' if target_link else 'なし'} blank={'あり' if blank_link else 'なし'} first={'あり' if first_link else 'なし'}")
            self.log(f"  {prefix}[DEBUG] full_address全文=「{full_address}」")
            if target_link:
                click_link    = target_link
                chosen_oaza   = selected_oaza
                chosen_azacho = selected_azacho
            elif blank_link:
                click_link    = blank_link
                chosen_oaza   = blank_oaza
                chosen_azacho = ""
                self.log(f"  {prefix}[フォールバック] 完全一致なし → azacho空行を選択")
            elif first_link:
                click_link    = first_link
                chosen_oaza   = first_oaza
                chosen_azacho = ""
                self.log(f"  {prefix}[フォールバック] azacho空行なし → 最初の行を選択")
            else:
                click_link    = None
                chosen_oaza   = ""
                chosen_azacho = ""

            if click_link:
                # クリックではなく onclick の lookupPick() を直接 JS で実行する。
                # Playwright の .click() はポップアップ内でフォーカスが戻った際に
                # BEAMS が別の候補行を自動選択してしまう場合があるため、
                # HTML の onclick 属性に記載された lookupPick() を直接呼び出すことで
                # 確実に意図した行を選択する。
                onclick_raw = click_link.get_attribute("onclick") or ""
                _picked = False
                if "lookupPick(" in onclick_raw:
                    try:
                        target_frame.evaluate(f"(function(){{{onclick_raw}}})()")
                        self.log(f"  {prefix}候補行をJS実行でクリック (oaza=「{chosen_oaza}」 azacho=「{chosen_azacho}」)")
                        _picked = True
                    except Exception as _je:
                        self.log(f"  {prefix}[警告] JS実行失敗、通常クリックで代替: {_je}")
                if not _picked:
                    click_link.click()
                    self.log(f"  {prefix}候補行をクリック (oaza=「{chosen_oaza}」 azacho=「{chosen_azacho}」)")
            else:
                raise RuntimeError(f"{prefix}ルックアップテーブルに選択可能な行がありません")

            try:
                popup.wait_for_event("close", timeout=5000)
            except Exception:
                pass
            self.wait_for_loading()
            # ポップアップ選択後もBEAMSが住所フィールドを非同期補完するため安定待機
            self._wait_for_field_stable(page, fid_aza or fid_addr, prefix)

            if fid_aza:
                try:
                    azacho_filled = page.locator(f'[id="{fid_aza}"]').input_value()
                except Exception:
                    azacho_filled = ""
                self.log(f"  {prefix}azacho 確定: 「{azacho_filled}」")

        # ③ address の組み立て + 全角正規化
        # building はそのまま結合（保存用）。ただし番地フィールドへの入力時は
        # CMR/REQ番号以降を除去する（番地欄にCMRが混入するのを防ぐ）。
        combined = full_address
        if building and building not in combined:
            combined = combined + building

        detail = ""
        if banchi_only:
            # PDFのaddress_partsから明示的に渡された番地を最優先で使う
            # BEAMSが誤った丁目を補完しても番地は正確に入力される
            detail = banchi_only
        elif azacho_filled and azacho_filled in combined:
            # azacho が確定している → azacho の後ろを番地として使う
            idx    = combined.index(azacho_filled)
            detail = combined[idx + len(azacho_filled):].strip()
        elif chosen_oaza and chosen_oaza in combined:
            # ポップアップ選択で oaza が確定 → oaza の後ろを番地として使う
            idx    = combined.index(chosen_oaza)
            detail = combined[idx + len(chosen_oaza):].strip()
        else:
            detail = combined

        # CMR/REQ番号は番地フィールドにも残す（除去不要）
        # 全角正規化（ハイフン・数字・記号を全角に統一）
        detail = normalize_address(detail)

        self.log(f"  {prefix}address 入力値: 「{detail}」")

        # ④ address フィールドに入力
        # BEAMSはfill後にJSが値をクリアすることがある。
        # JS経由で value をセットし change/input イベントを発火して確実に保持させる。
        if fid_addr and detail:
            page.evaluate(
                """([fid, val]) => {
                    var el = document.getElementById(fid);
                    if (!el) return;
                    el.value = val;
                    ['input', 'change', 'blur'].forEach(function(t) {
                        el.dispatchEvent(new Event(t, {bubbles: true}));
                    });
                }""",
                [fid_addr, detail]
            )
            self.log(f"  {prefix}address 入力完了")

        if return_result:
            return {'azacho': azacho_filled, 'detail': detail}

    def wait_for_loading(self, timeout=10000):
        sel = "img[src*='loading.gif']"
        try:
            self.page.wait_for_selector(sel, state="visible", timeout=1000)
            self.page.wait_for_selector(sel, state="hidden", timeout=timeout)
            self.log(" - 通信完了を確認")
        except Exception:
            pass

    def _wait_for_field_stable(self, page, fid: str, prefix: str = "", polls: int = 3, interval_ms: int = 300):
        """
        指定フィールドの値が連続して変化しなくなるまで待機する。
        BEAMSが郵便番号ロード後に住所フィールドを非同期補完し終わるのを待つ。
        polls: 何回連続で同じ値なら安定とみなすか（3回＝900ms程度）
        interval_ms: ポーリング間隔（ミリ秒）
        """
        if not fid:
            page.wait_for_timeout(interval_ms * polls)
            return
        prev = None
        stable_count = 0
        for _ in range(polls * 6):  # 最大 polls*6 回試行（約5秒）
            try:
                loc = page.locator(f'[id="{fid}"]')
                current = loc.input_value() if loc.count() > 0 else ""
            except Exception:
                current = ""
            if current == prev:
                stable_count += 1
                if stable_count >= polls:
                    return
            else:
                stable_count = 0
            prev = current
            page.wait_for_timeout(interval_ms)

    # ---- 基本情報 ------------------------------------------------

    def section_basic_info(self):
        self.log("[基本情報] 入力を開始...")
        fids = self.fids['BASIC']

        # 入力規則iniの[BASIC]セクションから値を取得（東西で異なる値に対応）
        _live_basic = {}
        if self.live and 'BASIC' in self.live:
            _live_basic = self.live['BASIC']

        def _live_val(key, fallback=''):
            return _live_basic.get(key, fallback).strip()

        btn = self.page.locator("a[title='法人登録タブ']").first
        btn.wait_for(state="visible", timeout=10000)
        try:
            self.page.bring_to_front()
            self.page.wait_for_timeout(200)
        except Exception:
            pass
        btn.click()
        self.page.wait_for_load_state("domcontentloaded")
        self.wait_for_loading()

        fid = fids.get('apply_date')
        if fid:
            self.page.wait_for_selector(f"id={fid}", state="visible", timeout=15000)
            for _retry in range(5):
                try:
                    self.page.evaluate(f"DatePicker.insertDate('{self.today_str}', '{fid}', true);")
                    break
                except Exception as _e:
                    if _retry < 4:
                        self.page.wait_for_timeout(500)
                    else:
                        raise

        fid = fids.get('sales_method')
        if fid:
            self.page.select_option(f"id={fid}", label=_live_val('sales_method', '訪販'))

        # 取扱店CODE: 入力規則iniの designated_code を優先、なければ field_ids.ini の designated_code_value
        fid = fids.get('designated_code')
        val = _live_val('designated_code') or fids.get('designated_code_value', 'HCAYVT015')
        if fid:
            self.page.fill(f"id={fid}", val)
            self.log(f" - 取扱店CODE: {val}")
            self.wait_for_loading()

        # 営業担当者番号
        fid = fids.get('add_code1')
        val = _live_val('add_code1') or fids.get('add_code1_value', '9999999')
        if fid:
            t = self.page.locator(f"id={fid}")
            t.click(); t.fill(val); t.press("Tab")
            self.log(f" - 営業担当者番号: {val}")
            self.wait_for_loading()

        # 前確担当者番号
        fid = fids.get('add_code2')
        val = _live_val('add_code2') or fids.get('add_code2_value', '9999999')
        if fid:
            t = self.page.locator(f"id={fid}")
            t.click(); t.fill(val); t.press("Tab")
            self.log(f" - 前確担当者番号: {val}")
            self.wait_for_loading()

        fid = fids.get('checkbox')
        if fid:
            t = self.page.locator(f"id={fid}")
            t.scroll_into_view_if_needed(); t.check()
            self.log(" - 郵送コード不要フラグ: チェック")
            self.wait_for_loading()

        # NTT販売担当者ID
        fid = fids.get('special_code')
        val = _live_val('special_code') or fids.get('special_code_value', '45004689')
        if fid:
            t = self.page.locator(f"id={fid}")
            t.scroll_into_view_if_needed(); t.fill(val); t.press("Tab")
            self.log(f" - NTT販売担当者ID: {val}")
            self.wait_for_loading()

        fid = self._fid('BASIC', 'gender_select')
        if fid:
            t = self.page.locator(f"id={fid}")
            t.scroll_into_view_if_needed()
            t.select_option(label=_live_val('gender_select', '男性'))
            self.log(f" - 性別: {_live_val('gender_select', '男性')}")
        # ※ 続柄「担当者」の選択は section_service_info の「次ページへ」直前に実行

    # ---- 住所・法人情報 ------------------------------------------

    def section_address_info(self, pdf_data: dict):
        self.log("[住所情報] 入力を開始...")
        sec = 'ADDRESS'
        sec_addr = self.fids['ADDRESS']
        ap = pdf_data.get("address_parts", {})

        self._fill_or_skip(sec, 'company_kana', '会社名カナ', pdf_data)
        self._fill_or_skip(sec, 'company_name', '会社名漢字', pdf_data)
        self._fill_or_skip(sec, 'staff_name',   '担当者名',   pdf_data)
        self._fill_or_skip(sec, 'phone',        '電話番号',   pdf_data)

        fid_zip  = self._fid(sec, 'zip_code')
        fid_aza  = self._fid(sec, 'azacho')
        fid_addr = self._fid(sec, 'banchi')
        zip_val  = pdf_data.get('zip_code', '')
        if fid_zip and zip_val:
            # PDFのaddress_partsからbanchiを取り出してbanchi_onlyとして渡す
            # BEAMSが誤った丁目を補完しても番地部分が正しく入力される
            _ap_banchi = ap.get('banchi', '')
            self._fill_zip_with_azacho(
                fid_zip      = fid_zip,
                fid_aza      = fid_aza,
                fid_addr     = fid_addr,
                zip_val      = zip_val,
                full_address = pdf_data.get('address', ''),
                building     = ap.get('building', ''),
                label        = "設置先",
                btn_title    = "契約人住所 郵便番号（ルックアップ） ルックアップ (新規ウィンドウ)",
                btn_index    = 0,
                banchi_only  = _ap_banchi,
            )

        my_fid = sec_addr.get('my_company_id')
        my_val = sec_addr.get('my_company_value')
        if my_fid and my_val:
            self._fill(my_fid, my_val)
            self.log(f" - 契約者氏名入力: {my_val}")

        # ---- 会社名漢字（追加2箇所）----
        comp_name = pdf_data.get('company_name', '')
        if comp_name:
            for i in range(1, 3):
                fid = sec_addr.get(f'extra_company_id_{i}')
                if fid:
                    self._fill(fid, comp_name)
                    self.log(f" - 会社名漢字({i+1})入力: {comp_name}")

        # ---- 会社名カナ（追加2箇所）----
        comp_kana = pdf_data.get('company_kana', '')
        if comp_kana:
            self._fill_or_skip('ADDRESS', 'company_kana', '会社名カナ(1)', pdf_data)
            for i in range(1, 3):
                fid = sec_addr.get(f'extra_company_kana_id_{i}')
                if fid:
                    self._fill(fid, comp_kana)
                    self.log(f" - 会社名カナ({i+1})入力: {comp_kana}")

        # ---- 「契約者住所と同じ」ボタン（担当者名入力の前に押す）----
        # ※ コピーボタンはBEAMS側で担当者フィールドをリセットする可能性があるため
        #   担当者名・カナ・電話番号の入力より先に実行する
        btn_fid = self.fids.get('BASIC', 'copy_address_btn', fallback=None)
        if btn_fid and not btn_fid.strip().upper().startswith('TODO'):
            try:
                btn = self.page.locator(f'[id="{btn_fid}"]')
                if btn.count() > 0:
                    self.log("  - 「契約者住所と同じ」ボタンをクリックします...")
                    try:
                        self.page.bring_to_front()
                        self.page.wait_for_timeout(200)
                    except Exception:
                        pass
                    btn.click()
                    self.page.wait_for_timeout(1500)
                    self.wait_for_loading()

                    # 「契約者住所と同じ」ボタンは宛名フィールドも会社名で上書きする。
                    # billing_name（開通案内書類の宛名）が別途 PDF に存在する場合は
                    # ボタン後に正しい値で上書きする。
                    _billing_name_fid = self._fid('BILLING', 'doc_address_name')
                    _billing_name_val = pdf_data.get('billing_name', '') or pdf_data.get('company_name', '')
                    if _billing_name_fid and _billing_name_val:
                        try:
                            _loc_bn = self.page.locator(f'[id="{_billing_name_fid}"]')
                            if _loc_bn.count() > 0:
                                self.page.evaluate(
                                    """([fid, val]) => {
                                        var el = document.getElementById(fid);
                                        if (!el) return;
                                        el.value = val;
                                        ['input', 'change', 'blur'].forEach(function(t) {
                                            el.dispatchEvent(new Event(t, {bubbles: true}));
                                        });
                                    }""",
                                    [_billing_name_fid, _billing_name_val]
                                )
                                self.log(f"  - 宛名（開通案内書類）上書き: {_billing_name_val}")
                        except Exception as _bne:
                            self.log(f"  - [警告] 宛名上書き失敗: {_bne}")
                else:
                    self.log("  - [警告] コピーボタンが見つかりません")
            except Exception as e:
                self.log(f"  - [失敗] コピーボタン操作エラー: {e}")

        # ---- 生年月日 ----
        # ※ コピーボタンの後に入力することで消失を防ぐ（2欄対応）
        # 1欄目・2欄目ともに rules ini の [BASIC] birth_date から取得（fallback: 1970/01/01）
        _live_basic_bd = self.live['BASIC'] if self.live and 'BASIC' in self.live else {}
        _BIRTH_DATE = _live_basic_bd.get('birth_date', '1970/01/01').strip() or '1970/01/01'

        fid = self.fids.get('BASIC', 'birth_date', fallback=None)
        if fid:
            fid = fid.strip().replace('"', '')
            try:
                self.page.wait_for_selector(f"id={fid}", state="visible", timeout=5000)
                self.page.evaluate(f"DatePicker.insertDate('{_BIRTH_DATE}', '{fid}', true);")
                self.log(f" - 生年月日①: {_BIRTH_DATE}")
            except Exception as e:
                self.log(f" - [警告] 生年月日①入力失敗: {e}")

        # 2欄目: 固定ID（請求先住所セクションの生年月日欄）/ 値は rules ini [BASIC] birth_date と同じ
        _BIRTH_DATE2_FID = "j_id0:sve_form1:pageBlock1:pageBlockSection14:pageBlockSectionItem15:inputField15"
        try:
            loc2 = self.page.locator(f'[id="{_BIRTH_DATE2_FID}"]')
            if loc2.count() > 0:
                self.page.evaluate(f"DatePicker.insertDate('{_BIRTH_DATE}', '{_BIRTH_DATE2_FID}', true);")
                self.log(f" - 生年月日②: {_BIRTH_DATE}")
            else:
                self.log(" - [スキップ] 生年月日②欄が見つかりません（ページに存在しない）")
        except Exception as e:
            self.log(f" - [警告] 生年月日②入力失敗: {e}")

        # ---- 担当者名（漢字・カナ）/ 電話番号 ----
        # ※ コピーボタンの後に入力することで消失を防ぐ
        staff_n = clean_text(pdf_data.get('staff_name', ''))
        if staff_n:
            parts_n = staff_n.split()
            last_n  = parts_n[0] if len(parts_n) >= 1 else ""
            first_n = parts_n[1] if len(parts_n) >= 2 else ""
            self._fill_or_skip(sec, 'staff_last_name',  '担当者(姓)漢字', {'staff_last_name': last_n})
            self._fill_or_skip(sec, 'staff_first_name', '担当者(名)漢字', {'staff_first_name': first_n})

        staff_k = pdf_data.get('staff_kana', '')
        if staff_k:
            parts_k = staff_k.split()
            last_k  = parts_k[0] if len(parts_k) >= 1 else ""
            first_k = parts_k[1] if len(parts_k) >= 2 else ""
            self._fill_or_skip(sec, 'staff_last_kana',  '担当者(姓)カナ', {'staff_last_kana': last_k})
            self._fill_or_skip(sec, 'staff_first_kana', '担当者(名)カナ', {'staff_first_kana': first_k})

        self._fill_or_skip(sec, 'mobile_phone', '携帯電話番号', pdf_data)
        self._fill_or_skip(sec, 'phone',        '電話番号',     pdf_data)

        self.log("[設置先住所・法人情報] 入力完了")

    # ---- 請求情報 ------------------------------------------------

    def section_billing_info(self, data):
        self.log("--- 請求情報の入力 (2箇所) ---")
        sec_bill = self.fids['BILLING']

        full_addr = data.get('billing_address', '')
        building  = data.get('billing_building', '')
        zip_val   = re.sub(r'[^\d]', '', data.get('billing_zip', ''))

        # 書類送付先・請求書送付先が設置場所住所と同一の場合、
        # PDF 2ページ目の請求先郵便番号欄が空になることがある。
        # その場合は請求先住所も無効とみなし、設置先住所をフォールバックとして使用する。
        if not zip_val:
            zip_val   = re.sub(r'[^\d]', '', data.get('zip_code', ''))
            # billing_zip が空のときは billing_address も信頼せず設置先住所に切り替える
            full_addr = data.get('address', '')
            building  = data.get('address_parts', {}).get('building', '') or building
            self.log("  [請求情報] 請求先郵便番号が未設定のため設置先住所をフォールバックとして使用します")
        if not full_addr:
            full_addr = data.get('address', '')

        # building をそのまま使用（CMR/REQ除去は不要）
        _bld_clean = building.strip() if building else ""

        # 番地以降のみを事前に切り出す（BEAMSが都道府県〜oazaを自動補完するため）
        _banchi_only = ""
        if full_addr:
            _m = re.search(r'丁目([0-9０-９].+)', full_addr)
            if _m:
                _banchi_only = _m.group(1).strip()
                if _bld_clean and _bld_clean not in _banchi_only:
                    _banchi_only += _bld_clean
            elif _bld_clean:
                _banchi_only = _bld_clean

        billing_targets = [
            {'zip': 'billing_zip1', 'aza': 'billing_azacho1', 'addr': 'billing_address1'},
            {'zip': 'billing_zip2', 'aza': 'billing_azacho2', 'addr': 'billing_address2'},
        ]

        BILLING_BTNS = [
            # 請求先1（billing_zip1 = Component36）→ 書類送付先住所
            ("書類送付先住所 郵便番号（ルックアップ） ルックアップ (新規ウィンドウ)", 0),
            # 請求先2（billing_zip2 = Component68）→ 請求先住所_郵便番号
            ("請求先住所_郵便番号（ルックアップ） ルックアップ (新規ウィンドウ)", 0),
        ]

        # 請求先1でポップアップ選択した azacho・detail を請求先2に再利用する
        # 2箇所は必ず同じ住所のため、1回目の選択結果を2回目にそのまま適用する
        _confirmed_azacho = None  # 1回目で確定した字丁目（None=未確定）
        _confirmed_detail = None  # 1回目で確定した番地以降

        for i, (target, (btn_title, btn_index)) in enumerate(
                zip(billing_targets, BILLING_BTNS), 1):
            self.log(f"  --- 請求先セット {i} ---")
            # 前セットの処理完了を待機
            if i > 1:
                self.wait_for_loading()
                self.page.wait_for_timeout(300)

            fid_zip  = sec_bill.get(target['zip'])
            fid_aza  = sec_bill.get(target['aza'])
            fid_addr = sec_bill.get(target['addr'])

            if not (fid_zip and zip_val):
                self.log(f"  [スキップ] 請求先{i}: フィールドIDまたは郵便番号が未設定")
                continue

            if i == 2 and _confirmed_azacho is not None and _confirmed_detail is not None:
                # ── 請求先2: ポップアップを開き、請求先1で選んだ azacho と一致する行を選択 ──
                # BEAMSの自動補完が複数候補ポップアップを出す場合があるため、
                # 直接JSで書き込むのではなく、必ずポップアップ経由で正しい行を選択する。
                self.log(f"  [請求先2] 請求先1の確定値を使ってポップアップ選択")
                self.log(f"  [請求先2] 郵便番号入力: {zip_val} / 期待 azacho:「{_confirmed_azacho}」")

                page = self.page

                # ① 郵便番号入力
                page.evaluate(
                    """([fid, val]) => {
                        var el = document.getElementById(fid);
                        if (!el) return;
                        el.value = val;
                        el.dispatchEvent(new Event('input', {bubbles: true}));
                        el.dispatchEvent(new Event('change', {bubbles: true}));
                    }""",
                    [fid_zip, zip_val]
                )
                z2 = page.locator(f'[id="{fid_zip}"]')
                z2.press("Tab")
                self.wait_for_loading()
                z2.press("Tab")
                page.wait_for_timeout(300)

                # ② ルックアップポップアップを開く
                popup_btn2 = page.locator(f'img[title="{btn_title}"]').nth(btn_index)
                try:
                    popup_btn2.wait_for(state="visible", timeout=10000)
                    for _st in range(10):
                        try:
                            if popup_btn2.count() > 0:
                                popup_btn2.scroll_into_view_if_needed()
                                break
                        except Exception:
                            page.wait_for_timeout(300)
                    else:
                        self.log(f"  [請求先2][警告] スクロールスキップ（DOM再描画中）")
                except Exception as _be:
                    self.log(f"  [請求先2][警告] ボタン待機タイムアウト: {_be}")

                # ポップアップが開く前にBEAMSのJS初期化を待つ
                page.wait_for_timeout(1000)

                # フォーカスをEdgeに戻す
                try:
                    page.bring_to_front()
                    page.wait_for_timeout(300)
                except Exception:
                    pass

                popup2 = None
                for _attempt, _click_fn in enumerate([
                    lambda: page.evaluate("(el) => el.click()", popup_btn2.element_handle()),
                    lambda: popup_btn2.click(),
                    lambda: popup_btn2.dispatch_event('click'),
                ], 1):
                    try:
                        with page.expect_popup(timeout=5000) as popup_info2:
                            _click_fn()
                        popup2 = popup_info2.value
                        self.log(f"  [請求先2] ポップアップ開成功（試行{_attempt}）")
                        break
                    except Exception as _e:
                        self.log(f"  [請求先2][試行{_attempt}] ポップアップ未開: {str(_e)[:60]}")
                if popup2 is None:
                    raise RuntimeError("  [請求先2] ルックアップポップアップが3回試行後も開きませんでした")

                popup2.wait_for_load_state("domcontentloaded")
                try:
                    popup2.bring_to_front()
                    popup2.wait_for_timeout(300)
                except Exception:
                    pass

                # フレーム探索
                target_frame2 = popup2
                try:
                    popup2.wait_for_selector("a.dataCell", timeout=3000)
                except Exception:
                    for frame in popup2.frames:
                        try:
                            frame.wait_for_selector("a.dataCell", timeout=5000)
                            target_frame2 = frame
                            self.log(f"  [請求先2] フレーム内にデータ発見: {frame.url}")
                            break
                        except Exception:
                            continue

                # ③ _confirmed_azacho と一致する行を選択
                rows2 = target_frame2.locator("table tr").all()
                click_link2    = None
                fallback_link2 = None
                first_link2    = None
                seen_ids2 = set()
                for ri, row in enumerate(rows2):
                    cells = row.locator("td").all()
                    if len(cells) != 4:
                        continue
                    link = row.locator("a.dataCell").first
                    if link.count() == 0:
                        continue
                    onclick_val = link.get_attribute("onclick") or ""
                    id_parts = re.findall(r"'([^']*)'", onclick_val)
                    record_id = id_parts[4] if len(id_parts) > 4 else ""
                    if record_id in seen_ids2:
                        continue
                    seen_ids2.add(record_id)

                    if first_link2 is None:
                        first_link2 = link

                    oaza2   = cells[2].inner_text().strip()
                    azacho2 = cells[3].inner_text().strip()
                    row_azacho = (oaza2 + azacho2).strip()

                    # 請求先1で選んだ azacho を含む行を選択
                    if _confirmed_azacho and (_confirmed_azacho in row_azacho or row_azacho in _confirmed_azacho):
                        click_link2 = link
                        self.log(f"  [請求先2] 一致行発見 row[{ri}]: oaza=「{oaza2}」 azacho=「{azacho2}」")
                        break
                    if fallback_link2 is None and azacho2 == "":
                        fallback_link2 = link

                def _js_pick(frame, link, label=""):
                    """onclick の lookupPick() を JS で直接実行。失敗時は通常クリックで代替。"""
                    _onclick = link.get_attribute("onclick") or ""
                    if "lookupPick(" in _onclick:
                        try:
                            frame.evaluate(f"(function(){{{_onclick}}})()")
                            return
                        except Exception as _je:
                            self.log(f"  {label}[警告] JS実行失敗、通常クリックで代替: {_je}")
                    link.click()

                if click_link2:
                    _js_pick(target_frame2, click_link2, "[請求先2]")
                elif fallback_link2:
                    self.log(f"  [請求先2][フォールバック] 一致行なし → azacho空行を選択")
                    _js_pick(target_frame2, fallback_link2, "[請求先2]")
                elif first_link2:
                    self.log(f"  [請求先2][フォールバック] azacho空行なし → 最初の行を選択")
                    _js_pick(target_frame2, first_link2, "[請求先2]")
                else:
                    raise RuntimeError("  [請求先2] ルックアップテーブルに選択可能な行がありません")

                try:
                    popup2.wait_for_event("close", timeout=5000)
                except Exception:
                    pass
                self.wait_for_loading()
                self._wait_for_field_stable(page, fid_aza or fid_addr, "[請求先2] ")

                # ④ banchi を確定値で上書き（BEAMSが自動補完しても正しい値を保証）
                if fid_addr and _confirmed_detail:
                    page.evaluate(
                        """([fid, val]) => {
                            var el = document.getElementById(fid);
                            if (!el) return;
                            el.value = val;
                            ['input','change','blur'].forEach(t =>
                                el.dispatchEvent(new Event(t, {bubbles: true})));
                        }""",
                        [fid_addr, _confirmed_detail]
                    )
                    self.log(f"  [請求先2] address 入力: 「{_confirmed_detail}」")

            else:
                # ── 請求先1: ポップアップで選択 ──────────────────────────
                result = self._fill_zip_with_azacho(
                    fid_zip      = fid_zip,
                    fid_aza      = fid_aza,
                    fid_addr     = fid_addr,
                    zip_val      = zip_val,
                    full_address = full_addr,
                    building     = building,
                    label        = f"請求先{i}",
                    btn_title    = btn_title,
                    btn_index    = btn_index,
                    banchi_only  = _banchi_only,
                    return_result = True,  # 確定値を返す
                )
                if result:
                    _confirmed_azacho = result.get('azacho', '')
                    _confirmed_detail = result.get('detail', '')
                    self.log(f"  [請求先1] 確定値を保存: azacho=「{_confirmed_azacho}」 detail=「{_confirmed_detail}」")

        self.log("[請求情報] 完了")

    # ---- 申込サービス入力（1️⃣〜4️⃣）--------------------------------

    def section_service_info(self, pdf_data: dict):
        """
        申込サービス（主商材）〜 詳細入力 の全フロー。
        livecamera_west.ini の [SERVICE] セクションを参照。
        """
        self.log("--- 申込サービス入力 開始 ---")
        page = self.page

        # 入力規則iniの各セクションから値を取得
        _live_svc   = self.live['SERVICE'] if self.live and 'SERVICE' in self.live else {}
        _live_other = self.live['OTHER']   if self.live and 'OTHER'   in self.live else {}
        _live_basic = self.live['BASIC']   if self.live and 'BASIC'   in self.live else {}

        def _svc(key, fallback=''):
            return _live_svc.get(key, fallback).strip()

        # 商材名をiniから取得
        _plan_hayabusa  = _svc('plan_hayabusa',  'フレッツ光ネクスト隼ファミリー')
        _plan_gigaline  = _svc('plan_gigaline',  'フレッツ光ネクスト ファミリー・ギガライン東')
        _plan_cross     = _svc('plan_cross',     'フレッツ光ネクストファミリー')
        _option_ace     = _svc('option_hayabusa','ひかり電話_エースプラン')

        # ─── 商材選択モード判定 ─────────────────────────────────────────
        # plan_mode = auto  : PDFのプラン名からクロス/隼/ギガラインを自動判定（従来通り）
        # plan_mode = fixed : 固定値（PDFに関わらず plan_cross/hayabusa/gigaline の固定値を使う）
        _plan_mode = _svc('plan_mode', 'auto').lower().strip()

        # PDFのプラン名からクロス/隼/ギガラインを判定
        plan1_name = pdf_data.get("plan1_name", "")
        plan2_name = pdf_data.get("plan2_name", "")
        all_plans  = plan1_name + plan2_name
        is_hayabusa  = "隼"        in all_plans
        is_gigaline  = "ギガライン" in all_plans
        is_cross     = "クロス"    in all_plans

        if _plan_mode == 'fixed':
            # 固定値モード: PDFに関わらず ini の固定値を使う
            # どのプランを使うかは PDF判定を補助的に利用（判定できない場合はクロスをデフォルト）
            if is_hayabusa:
                plan_type    = "hayabusa"
                main_product = _plan_hayabusa
            elif is_gigaline:
                plan_type    = "gigaline"
                main_product = _plan_gigaline
            else:
                plan_type    = "cross"
                main_product = _plan_cross
            self.log(f"  商材モード: 固定値 → 商材=「{main_product}」")
        else:
            # auto: 従来通り PDF判定
            if is_hayabusa:
                plan_type    = "hayabusa"
                main_product = _plan_hayabusa
                self.log(f"  商材モード: 自動 / プラン判定: 隼 → 商材=「{main_product}」")
            elif is_gigaline:
                plan_type    = "gigaline"
                main_product = _plan_gigaline
                self.log(f"  商材モード: 自動 / プラン判定: ギガライン → 商材=「{main_product}」")
            elif is_cross:
                plan_type    = "cross"
                main_product = _plan_cross
                self.log(f"  商材モード: 自動 / プラン判定: クロス → 商材=「{main_product}」")
            else:
                plan_type    = "cross"
                main_product = _plan_cross
                self.log(f"  商材モード: 自動 / プラン判定: 不明（デフォルト: クロス）→ 商材=「{main_product}」")

        # フリーボックス①: iniの free_box1 をそのまま使用（CMR/REQ自動判定なし）
        free_box1 = _live_other.get('free_box1', 'ＥＡＲＴＨ（ライブカメラ）').strip()
        self.log(f"  フリーボックス①: 「{free_box1}」")

        # ─── 電話プランモード判定 ───────────────────────────────────
        # phone_plan = auto  : PDFのプラン名から隼/ギガライン判定（従来通り）
        # phone_plan = none  : 電話なし（オプション追加・詳細入力・オプション詳細 全スキップ）
        # phone_plan = fixed : 固定値（option_hayabusa の値を常に入力）
        _phone_plan = _svc('phone_plan', 'auto').lower().strip()

        if _phone_plan == 'none':
            # 電話なし: オプション追加もCS詳細も不要
            _use_option  = False
            _use_detail_opt = False
            self.log(f"  電話プラン: なし（スキップ）")
        elif _phone_plan == 'fixed':
            # 固定値: 隼/ギガライン判定に関わらず常にオプションを追加
            _use_option  = True
            _use_detail_opt = True
            # plan_type はクロス扱いにして主商材はini値をそのまま使う
            if plan_type == "cross":
                # クロスでも固定オプションを追加する場合: plan_typeを hayabusa 相当に変える
                plan_type = "hayabusa"
            self.log(f"  電話プラン: 固定値（{_option_ace}）")
        else:
            # auto: 従来通り PDF判定
            _use_option      = plan_type in ("hayabusa", "gigaline")
            _use_detail_opt  = plan_type in ("hayabusa", "gigaline")
            self.log(f"  電話プラン: 自動判定（{plan_type}）")
        self.log("  [1] サービス追加ボタンをクリック")
        add_btn = page.locator(
            "id=j_id0:sve_form1:pageBlock1:dataTableSet2_addButton"
        )
        add_btn.wait_for(state="visible", timeout=15000)
        try:
            page.bring_to_front()
            page.wait_for_timeout(200)
        except Exception:
            pass
        page.evaluate("(el) => { el.click(); }", add_btn.element_handle())
        self.wait_for_loading()

        self.log("  [1] 回線種別: 回線")
        row_sel = "id=j_id0:sve_form1:pageBlock1:dataTableSet2_table:0:inputField112"
        page.wait_for_selector(row_sel, state="visible", timeout=30000)
        page.select_option(row_sel, value="回線")
        page.wait_for_timeout(300)
        self.wait_for_loading()

        self.log("  [1] サービス: フレッツ")
        page.select_option(
            "id=j_id0:sve_form1:pageBlock1:dataTableSet2_table:0:inputField102",
            value="フレッツ"
        )
        page.wait_for_timeout(300)

        # 商材入力: ギガラインはルックアップ経由、クロス/隼はテキスト入力
        _fid98 = "j_id0:sve_form1:pageBlock1:dataTableSet2_table:0:inputField98"
        _loc98 = page.locator(f'[id="{_fid98}"]')
        _loc98.scroll_into_view_if_needed()

        if plan_type == "gigaline":
            # ギガラインはルックアップポップアップで「フレッツ光ネクスト ファミリー・ギガライン東」を選択
            self.log(f"  [1] 商材ルックアップ起動（ギガライン）")
            _lookup_btn = page.locator(
                'img[title="申込サービス ルックアップ (新規ウィンドウ)"]'
            ).first
            try:
                _lookup_btn.wait_for(state="visible", timeout=10000)
            except Exception:
                # title が一致しない場合は inputField98 横のルックアップアイコンを探す
                _lookup_btn = page.locator(
                    f'[id="{_fid98}"]'
                ).locator('xpath=following-sibling::a[1]')
            page.wait_for_timeout(500)
            try:
                page.bring_to_front()
                page.wait_for_timeout(200)
            except Exception:
                pass
            with page.expect_popup(timeout=15000) as _lk_info:
                _lookup_btn.click()
            _lk_popup = _lk_info.value
            _lk_popup.wait_for_load_state("domcontentloaded")
            try:
                _lk_popup.bring_to_front()
                _lk_popup.wait_for_timeout(300)
            except Exception:
                pass
            # 「ギガライン東」を含む行を探してクリック
            _target_text = "ギガライン東"
            _clicked = False
            try:
                _lk_popup.wait_for_selector("a.dataCell", timeout=8000)
                for _lk_link in _lk_popup.locator("a.dataCell").all():
                    if _target_text in (_lk_link.inner_text() or ""):
                        _lk_link.click()
                        _clicked = True
                        self.log(f"  [1] ルックアップ選択: 「{_lk_link.inner_text().strip()}」")
                        break
            except Exception:
                for _frame in _lk_popup.frames:
                    try:
                        _frame.wait_for_selector("a.dataCell", timeout=5000)
                        for _lk_link in _frame.locator("a.dataCell").all():
                            if _target_text in (_lk_link.inner_text() or ""):
                                _lk_link.click()
                                _clicked = True
                                self.log(f"  [1] ルックアップ選択（frame内）: 「{_lk_link.inner_text().strip()}」")
                                break
                        if _clicked:
                            break
                    except Exception:
                        continue
            if not _clicked:
                # 見つからない場合は先頭行を選択してログ警告
                self.log("  [1] [警告] ギガライン東が見つかりません。先頭行を選択します")
                try:
                    _lk_popup.locator("a.dataCell").first.click()
                except Exception:
                    pass
            try:
                _lk_popup.wait_for_event("close", timeout=8000)
            except Exception:
                pass
            self.wait_for_loading()
            page.wait_for_timeout(500)

            # ルックアップ後のページエラーチェック（複数候補ヒット等）
            _page_errors = []
            try:
                for _em in page.locator(".errorMsg, .message, [class*='error']").all()[:5]:
                    _txt = (_em.inner_text() or "").strip()
                    if _txt:
                        _page_errors.append(_txt)
            except Exception:
                pass
            if _page_errors:
                self.log(f"  [1] [警告] 商材入力後ページエラー: {_page_errors[0][:80]}")
                # エラーをクリアするため商材フィールドを直接テキスト入力に切り替える
                self.log(f"  [1] [リカバリ] 商材をテキスト直接入力に切り替えます: {main_product}")
                try:
                    _loc98.click()
                    _loc98.fill(main_product)
                    _loc98.press("Tab")
                    page.wait_for_timeout(300)
                    self.wait_for_loading()
                except Exception as _re:
                    self.log(f"  [1] [リカバリ失敗] {_re}")
        else:
            # クロス / 隼: テキスト直接入力
            self.log(f"  [1] 商材入力: {main_product}")
            _loc98.click()
            _loc98.fill(main_product)
            _loc98.press("Tab")
            page.wait_for_timeout(200)

        # BEAMSの mod / lkid フラグをセット（共通）
        page.evaluate(
            """([fid]) => {
                var mod = document.getElementById(fid + '_mod');
                if (mod) mod.value = '1';
                var lkid = document.getElementById(fid + '_lkid');
                if (lkid) lkid.value = '';
            }""",
            [_fid98]
        )

        # 隼 / ギガライン / fixed: エースプランオプション追加
        if _use_option:
            self.log(f"  [1] オプション追加ボタンをクリック（エースプラン）")
            opt_btn = page.locator(
                "id=j_id0:sve_form1:pageBlock1:dataTableSet4_addButton"
            )
            opt_btn.wait_for(state="visible", timeout=15000)
            page.evaluate("(el) => { el.click(); }", opt_btn.element_handle())
            self.wait_for_loading()

            opt_row_sel = "id=j_id0:sve_form1:pageBlock1:dataTableSet4_table:0:inputField114"
            page.wait_for_selector(opt_row_sel, state="visible", timeout=30000)
            page.select_option(opt_row_sel, value="フレッツ")
            page.wait_for_timeout(300)

            _fid101 = "j_id0:sve_form1:pageBlock1:dataTableSet4_table:0:inputField101"
            _loc101 = page.locator(f'[id="{_fid101}"]')
            _loc101.scroll_into_view_if_needed()
            _loc101.click()
            _loc101.fill(_option_ace)
            _loc101.press("Tab")
            page.wait_for_timeout(200)
            page.evaluate(
                """([fid]) => {
                    var mod = document.getElementById(fid + '_mod');
                    if (mod) mod.value = '1';
                    var lkid = document.getElementById(fid + '_lkid');
                    if (lkid) lkid.value = '';
                }""",
                [_fid101]
            )
            self.log(f"  [1] オプション入力: {_option_ace}")

        # ─── 2️⃣ 移行前回線種別 / パートナーコード / フリーボックス ──
        _prev_line    = _live_other.get('prev_line_type',   'その他').strip()
        _partner_code = _live_other.get('ntt_partner_code', '1016498449').strip()

        self.log(f"  [2] 移行前回線種別: {_prev_line}")
        page.select_option(
            "id=j_id0:sve_form1:pageBlock1:Component131:Component142:Component140",
            value=_prev_line
        )
        page.wait_for_timeout(300)

        self.log(f"  [2] NTTパートナーコード: {_partner_code}")
        page.fill(
            "id=j_id0:sve_form1:pageBlock1:Component131:Component150:Component149",
            _partner_code
        )

        self.log(f"  [2] フリーボックス①: {free_box1}")
        page.fill(
            "id=j_id0:sve_form1:pageBlock1:pageBlockSection13:pageBlockSectionItem116:inputField123",
            free_box1
        )

        # ─── 2️⃣ 続柄「担当者」選択（次ページ直前）────────────────
        # sve_placeholder クラスのカスタムセレクトは select_option だけでは
        # BEAMSの内部状態が更新されないため、JS で value をセットして
        # change・blur イベントを明示的に発火させる
        fid_rel = self.fids.get('BASIC', 'relation_select', fallback=None)
        _relation_val = _live_basic.get('relation_select', '担当者').strip()
        if fid_rel and not fid_rel.strip().upper().startswith('TODO'):
            try:
                t_rel = page.locator(f'[id="{fid_rel}"]')
                t_rel.scroll_into_view_if_needed()
                t_rel.wait_for(state="visible", timeout=5000)

                try:
                    t_rel.select_option(value=_relation_val)
                except Exception:
                    t_rel.select_option(label=_relation_val)

                page.evaluate(
                    """([fid, val]) => {
                        var el = document.getElementById(fid);
                        if (!el) return;
                        el.value = val;
                        ['change', 'blur', 'input'].forEach(function(evt) {
                            el.dispatchEvent(new Event(evt, {bubbles: true}));
                        });
                    }""",
                    [fid_rel, _relation_val]
                )
                page.wait_for_timeout(800)
                self.wait_for_loading()
                confirmed = t_rel.input_value()
                self.log(f"  [2] 契約者との続柄: 「{confirmed}」")
            except Exception as rel_err:
                self.log(f"  [2] [警告] 続柄選択失敗: {rel_err}")

        # ─── 2️⃣ 次ページへボタン ─────────────────────────────────
        self.log("  [2] 次ページへボタンをクリック")
        next_btn = page.locator(
            "id=j_id0:sve_form1:pageBlock1:j_id82:Component999"
        )
        next_btn.wait_for(state="visible", timeout=10000)
        try:
            page.bring_to_front()
            page.wait_for_timeout(200)
        except Exception:
            pass
        next_btn.click()
        # ページ遷移完了まで十分に待機（BEAMSはSalesforceベースで重い）
        page.wait_for_load_state("domcontentloaded", timeout=30000)
        page.wait_for_timeout(2000)
        self.wait_for_loading()

        # ─── 3️⃣ 詳細入力（主商材）────────────────────────────────
        self.log("  [3] 詳細入力ボタンをクリック（主商材）")
        detail_btn = page.locator(
            "id=j_id0:sve_form1:pageBlock1:dataTableSet2_table:0:customButton6"
        )
        try:
            detail_btn.wait_for(state="visible", timeout=15000)
        except Exception:
            try:
                err_msgs = page.locator(".errorMsg, .message, [class*='error']").all()
                for em in err_msgs[:5]:
                    self.log(f"  [3] [ページエラー] {em.inner_text().strip()[:100]}")
            except Exception:
                pass
            self.log(f"  [3] [DEBUG] 現在URL: {page.url[:120]}")
            raise

        # 人間らしいクリック: スクロール → 視認待機 → ホバー → クリック
        detail_btn.scroll_into_view_if_needed()
        page.wait_for_timeout(600)
        detail_btn.hover()
        page.wait_for_timeout(300)

        def _open_detail_popup():
            try:
                page.bring_to_front()
                page.wait_for_timeout(200)
            except Exception:
                pass
            with page.expect_popup(timeout=20000) as _info:
                detail_btn.click()
            _p = _info.value
            _p.wait_for_load_state("domcontentloaded")
            _p.bring_to_front()
            _p.wait_for_timeout(500)
            _p.wait_for_selector("id=00N10000004lYPP", state="visible", timeout=10000)
            return _p

        def _do_detail_input(detail_page):
            self.log("  [3] 詳細入力: 各フィールドを入力")

            def _safe_select(fid, value, label=""):
                try:
                    detail_page.select_option(f"id={fid}", value=value)
                    if label:
                        self.log(f"    {label}: {value}")
                except Exception:
                    self.log(f"    [スキップ] {label or fid}: 選択肢「{value}」が見つかりません")

            _safe_select("00N10000004lYPP", _svc('current_line',         'その他'),              "現在利用中電話回線")
            _safe_select("00N10000001dZ6j", _svc('house_type',           '戸建'),               "住宅区分")
            _source_filename = pdf_data.get('source_filename', '')
            if _source_filename:
                try:
                    detail_page.fill("id=00N10000001dW5E", _source_filename)
                    self.log(f"    申込書番号: {_source_filename}")
                except Exception:
                    self.log(f"    [スキップ] 申込書番号: 入力できませんでした")
            _safe_select("00N10000001dW4y", _svc('discount_plan',        '光はじめ割'),          "割引プラン")
            try:
                detail_page.fill("id=00N10000001dW5N", _svc('existing_provider', 'なし'))
            except Exception:
                self.log("    [スキップ] 既存プロバイダ名: 入力できませんでした")
            _safe_select("00N10000001dwCR", _svc('lan_rental',           'しない'),              "NTT無線LANレンタル")
            _safe_select("00N10000004pirK", _svc('billing_detail',       '個別請求'),            "料金請求方法")
            _safe_select("00N10000004pirP", _svc('billing_destination',  'フレッツ光ご利用場所住所、ご契約者名宛に送付'), "請求書送付先")
            _safe_select("00N10000004piro", _svc('payment_detail',       '請求書送付（有料）'),   "支払い方法")
            _safe_select("00N10000001e9w6", _svc('construction_payment', '一括'),               "工事費支払い方法")
            _safe_select("00N10000001e9oM", _svc('indoor_wiring',        '無'),                 "屋内配線実施")

            self.log("  [3] 保存をクリック")
            save_btn = detail_page.locator("input[name='save'][tabindex='214']")
            save_btn.wait_for(state="visible", timeout=10000)
            save_btn.click()
            try:
                detail_page.wait_for_event("close", timeout=10000)
            except Exception:
                pass

        self._popup_with_retry(
            open_fn=_open_detail_popup,
            work_fn=_do_detail_input,
            label="詳細入力",
            max_retry=2,
        )
        page.wait_for_load_state("domcontentloaded", timeout=15000)
        self.wait_for_loading()

        # ─── 3️⃣ 隼/ギガライン/fixed: 契約サービスIDルックアップ + オプション詳細入力 ──
        if _use_detail_opt:
            self.log(f"  [3] 契約サービスIDルックアップをクリック（{plan_type}）")
            cs_lookup_btn = page.locator(
                'img[title="契約サービスID ルックアップ (新規ウィンドウ)"]'
            ).first
            cs_lookup_btn.wait_for(state="visible", timeout=10000)

            try:
                page.bring_to_front()
                page.wait_for_timeout(200)
            except Exception:
                pass
            with page.expect_popup(timeout=20000) as cs_popup_info:
                cs_lookup_btn.click()
            cs_popup = cs_popup_info.value
            cs_popup.wait_for_load_state("domcontentloaded")
            try:
                cs_popup.bring_to_front()
                cs_popup.wait_for_timeout(300)
            except Exception:
                pass

            self.log("  [3] 契約サービスID: 先頭候補をクリック")
            try:
                first_link = cs_popup.locator("a.dataCell").first
                first_link.wait_for(state="visible", timeout=8000)
                first_link.click()
            except Exception:
                for frame in cs_popup.frames:
                    try:
                        fl = frame.locator("a.dataCell").first
                        fl.wait_for(state="visible", timeout=5000)
                        fl.click()
                        break
                    except Exception:
                        continue
            try:
                cs_popup.wait_for_event("close", timeout=8000)
            except Exception:
                pass
            page.wait_for_load_state("domcontentloaded", timeout=15000)
            self.wait_for_loading()

            # オプション詳細入力
            self.log("  [3] 詳細入力ボタンをクリック（オプション）")
            opt_detail_btn = page.locator(
                "id=j_id0:sve_form1:pageBlock1:dataTableSet3_table:0:customButton7"
            )
            opt_detail_btn.wait_for(state="visible", timeout=10000)

            _OPT_FIRST_FID = (
                "id=j_id0:sve_form1:pageBlock1:pageBlockSection1"
                ":pageBlockSectionItem95:inputField78"
            )

            def _open_opt_popup():
                try:
                    page.bring_to_front()
                    page.wait_for_timeout(200)
                except Exception:
                    pass
                with page.expect_popup(timeout=20000) as _info:
                    opt_detail_btn.click()
                _p = _info.value
                _p.wait_for_load_state("domcontentloaded")
                _p.bring_to_front()
                _p.wait_for_timeout(500)
                _p.wait_for_selector(_OPT_FIRST_FID, state="visible", timeout=10000)
                return _p

            def _do_opt_input(opt_page):
                self.log("  [3] オプション詳細: 各フィールドを入力")

                def _os(fid, val):
                    try:
                        opt_page.select_option(f"id={fid}", value=val)
                    except Exception:
                        self.log(f"    [スキップ] {fid}: 選択肢「{val}」が見つかりません")

                _os("j_id0:sve_form1:pageBlock1:pageBlockSection1:pageBlockSectionItem95:inputField78",  _svc('addon_change',    '変更無し'))
                _os("j_id0:sve_form1:pageBlock1:pageBlockSection1:pageBlockSectionItem96:inputField79",  _svc('contract_change', 'すべて現状どおり'))
                _os("j_id0:sve_form1:pageBlock1:pageBlockSection10:pageBlockSectionItem47:inputField33", _svc('number_transfer', 'しない'))
                _os("j_id0:sve_form1:pageBlock1:pageBlockSection12:pageBlockSectionItem53:inputField39", _svc('caller_id',       '希望(非通知)'))
                _os("j_id0:sve_form1:pageBlock1:pageBlockSection12:pageBlockSectionItem54:inputField40", _svc('phonebook',       '掲載略'))
                _os("j_id0:sve_form1:pageBlock1:pageBlockSection12:pageBlockSectionItem55:inputField41", _svc('call_record',     '一部非希望'))

                self.log("  [3] 保存するをクリック")
                opt_save_btn = opt_page.locator(
                    "id=j_id0:sve_form1:pageBlock1:j_id74:customButton1"
                )
                opt_save_btn.wait_for(state="visible", timeout=10000)
                opt_save_btn.click()
                try:
                    opt_page.wait_for_event("close", timeout=10000)
                except Exception:
                    pass

            self._popup_with_retry(
                open_fn=_open_opt_popup,
                work_fn=_do_opt_input,
                label="オプション詳細",
                max_retry=2,
            )
            page.wait_for_load_state("domcontentloaded", timeout=15000)
            self.wait_for_loading()

        # ─── NTTへの伝言 / NTTパートナー担当 入力 ────────────────
        ntt_msg = ""
        ntt_partner = ""
        if self.live and 'OTHER' in self.live:
            ntt_msg     = self.live['OTHER'].get('ntt_message', '').strip()
            ntt_partner = self.live['OTHER'].get('ntt_partner_note', '').strip()

        self.log(f"  NTTへの伝言: 「{ntt_msg}」")
        page.fill(
            "id=j_id0:sve_form1:pageBlock1:pageBlockSection3:pageBlockSectionItem17:inputField11",
            ntt_msg
        )
        self.log(f"  NTTパートナー担当: 「{ntt_partner}」")
        page.fill(
            "id=j_id0:sve_form1:pageBlock1:pageBlockSection3:pageBlockSectionItem36:inputField14",
            ntt_partner
        )

        # ─── 最終操作（何もしない / 保留 / 確定登録）──────────────
        final_action = ""
        if self.live and 'OTHER' in self.live:
            final_action = self.live['OTHER'].get('final_action', '何もしない').strip()

        self.log(f"  最終操作: 「{final_action}」")
        if final_action == '保留':
            btn_hold = page.locator(
                "id=j_id0:sve_form1:pageBlock1:j_id82:customButton10"
            )
            btn_hold.wait_for(state="visible", timeout=10000)
            try:
                page.bring_to_front()
                page.wait_for_timeout(200)
            except Exception:
                pass
            btn_hold.click()
            page.wait_for_load_state("domcontentloaded", timeout=20000)
            self.wait_for_loading()
            self.log("  保留ボタンをクリックしました ✔")
            self._extract_and_notify_req(page)
        elif final_action == '確定登録':
            btn_confirm = page.locator(
                "id=j_id0:sve_form1:pageBlock1:j_id82:customButton8"
            )
            btn_confirm.wait_for(state="visible", timeout=10000)
            try:
                page.bring_to_front()
                page.wait_for_timeout(200)
            except Exception:
                pass
            btn_confirm.click()
            page.wait_for_load_state("domcontentloaded", timeout=20000)
            self.wait_for_loading()
            self.log("  確定登録ボタンをクリックしました ✔")
            self._extract_and_notify_req(page)
        else:
            self.log("  最終操作: 何もしない（手動で保留/確定登録してください）")

        self.log("--- 申込サービス入力 完了 ✔ ---")

    # ----------------------------------------------------------------

    def _extract_and_notify_req(self, page):
        """
        保留・確定登録完了後のページから REQ番号を取得し、
        ログ・UI・コールバックに通知する。

        BEAMSは保留/確定登録後に <h2 class="pageDescription">REQxxxxxxxx</h2>
        を含む確認ページへ遷移する。
        """
        req_number = ""
        try:
            # h2.pageDescription が出現するまで最大5秒待機
            page.wait_for_selector("h2.pageDescription", timeout=5000)
            raw = page.locator("h2.pageDescription").first.inner_text().strip()
            # "REQ" で始まる数字列を抽出（スペース・改行・全角スペースを除去）
            m = re.search(r'(REQ\s*\d+)', raw.replace('\u3000', '').replace('\n', ''))
            if m:
                req_number = re.sub(r'\s+', '', m.group(1))  # "REQ 15084162" → "REQ15084162"
            else:
                req_number = raw  # そのまま使用
        except Exception as e:
            self.log(f"  [REQ取得] h2.pageDescription が見つかりません: {e}")

        if req_number:
            self.log(f"  ★ REQ番号: {req_number} ✔")
            # UI のREQ表示ラベルを更新（コールバック経由）
            if self.on_req_acquired:
                self.on_req_acquired(req_number)
        else:
            self.log("  [REQ取得] REQ番号を取得できませんでした")


# =====================================================
# メインアプリ
# =====================================================

class BeamsApp:
    def __init__(self, account, password):
        # tkinterdnd2 が利用可能な場合はドラッグドロップ対応の Tk を使用する
        try:
            from tkinterdnd2 import TkinterDnD
            self.root = TkinterDnD.Tk()
        except Exception:
            self.root = tk.Tk()
        self.root.title("BEAMS 自動入力 v9.0.0")

        # アイコン設定
        _icon_path = data_path("icon.ico")
        if os.path.exists(_icon_path):
            try:
                self.root.iconbitmap(_icon_path)
                self.root.after(100, lambda p=_icon_path: self.root.iconbitmap(p))
            except Exception:
                pass
            # Windows タスクバーにアイコンを確実に反映させる
            try:
                import ctypes
                ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID(
                    "BEAMS.AutoInput.App"
                )
            except Exception:
                pass

        self.account   = account
        self.password  = password
        self.today_str = datetime.date.today().strftime("%Y/%m/%d")

        self._pdf_refresh_id = None  # refresh_pdf_count のタイマーID

        # ウィンドウを閉じる際にタイマーをキャンセルする
        self.root.protocol("WM_DELETE_WINDOW", self._on_close)

        self.playwright  = None
        self.browser     = None
        self.context     = None
        self.page        = None
        self.task_queue  = []
        self.processed_files: set = set()
        self.error_files: set = set()   # エラー発生PDFを記録（UI強調用）
        self.csv_logger  = CsvLogger()

        # エラー時動作モード: 'stay'（その場で停止）or 'skip'（次へスキップ）
        self.field_ids   = load_field_ids()
        layout_config    = load_pdf_layout()
        self.extractor   = PdfExtractor(layout_config) if layout_config else None

        # 入力規則: rules/ フォルダの全 .ini を読み込み、先頭をアクティブに設定
        self._all_rules       = load_all_rules()
        _rule_name, _rule_cfg = get_active_rule(self._all_rules)
        self.live_config      = _rule_cfg
        self._active_rule_name = _rule_name  # 保存先ファイル名の特定に使う

        # エラー時動作モード: live_config の [OTHER] on_error から読み込む
        # キーがなければ後方互換で 'stay'
        self.on_error_mode = self._read_on_error_from_live()

        # 右ペイン入力規則フィールドの StringVar 収集（一括保存用）
        self._rules_vars      = {}   # (sec, key) -> StringVar
        self._rules_name_var  = None  # プロファイル名 StringVar

        # ログイン設定パネルの展開フラグ
        self._settings_expanded = False
        # IPパネルの展開フラグ
        self._ip_expanded = False
        # セッション中に取得したREQ番号リスト
        self._req_list = []

        self.setup_ui()
        self.launch_browser_init()

    # ----------------------------------------------------------------
    # ユーティリティ
    # ----------------------------------------------------------------

    def wait_for_loading(self, timeout=15000):
        """BeamsApp からリセット等で呼び出すための wait_for_loading ラッパー。
        self.page（BeamsOperator ではなく BeamsApp 直接保持のページ）に対して
        Salesforce のローディングインジケータが消えるまで待機する。
        """
        if not self.page:
            return
        try:
            self.page.wait_for_function(
                "() => !document.querySelector('.slds-spinner, .loading')",
                timeout=timeout,
            )
        except Exception:
            pass  # タイムアウトしても続行

    def _read_on_error_from_live(self) -> str:
        """live_config の [OTHER] on_error を読んで返す。なければ 'stay'。"""
        if self.live_config and 'OTHER' in self.live_config:
            val = self.live_config['OTHER'].get('on_error', 'stay').strip().lower()
            if val in ('stay', 'skip'):
                return val
        return 'stay'

    # ----------------------------------------------------------------
    # UI
    # ----------------------------------------------------------------

    def setup_ui(self):
        BG       = "#f8f9fa"
        SURFACE  = "#ffffff"
        PRIMARY  = "#1a73e8"
        PRIMARY2 = "#1557b0"
        SUCCESS  = "#1e8e3e"
        DANGER   = "#d93025"
        TEXT1    = "#202124"
        TEXT2    = "#5f6368"
        BORDER   = "#dadce0"
        FONT_H   = ("Yu Gothic UI", 11, "bold")
        FONT_B   = ("Yu Gothic UI", 9)
        FONT_S   = ("Yu Gothic UI", 8)
        FONT_LOG = ("BIZ UDGothic", 9)  # 日本語・英数混在に対応

        # ── フルウィンドウ・2ペイン構成 ─────────────────────────────
        self.root.configure(bg=BG)
        self.root.minsize(800, 500)
        self.root.resizable(True, True)
        self.root.state('zoomed')  # 起動時に最大化

        # ── ヘッダー ────────────────────────────────────────────────
        header = tk.Frame(self.root, bg=PRIMARY, height=48)
        header.pack(fill="x", side="top")
        header.pack_propagate(False)
        tk.Label(header, text="BEAMS 自動入力 v8.5", bg=PRIMARY, fg="white",
                 font=("Yu Gothic UI", 13, "bold")).pack(side=tk.LEFT, padx=16, pady=10)

        # アップデート情報ボタン（右端）
        _UPDATE_URL = "https://docs.google.com/document/d/1oo_Q2Wm3xQXtI_zjc6qqhaE6STp18EUVfJqNo41GBNs/edit?usp=sharing"
        update_frame = tk.Frame(header, bg=PRIMARY)
        update_frame.pack(side=tk.RIGHT, padx=10)
        tk.Button(
            update_frame, text="📄 アップデート情報",
            bg="#1557b0", fg="white", relief="flat", cursor="hand2",
            font=("Yu Gothic UI", 8), padx=8, pady=2,
            command=lambda: __import__('webbrowser').open(_UPDATE_URL)
        ).pack(side=tk.TOP, pady=(0, 6))

        self.date_lbl = tk.Label(header, text=self.today_str,
                                  bg=PRIMARY, fg="#c8dbf8", font=("Yu Gothic UI", 9))
        self.date_lbl.pack(side=tk.RIGHT, padx=16)

        # ── 2ペイン：左＝操作パネル、右＝入力規則 ──────────────────
        pane = tk.PanedWindow(self.root, orient=tk.HORIZONTAL,
                               bg=BG, sashwidth=6, sashrelief="flat")
        pane.pack(fill="both", expand=True)

        # ════ 左ペイン ════════════════════════════════════════════
        left = tk.Frame(pane, bg=BG)
        pane.add(left, minsize=340)

        # ── ログイン設定トグルボタン ──────────────────────────────
        self._settings_card = tk.Frame(left, bg=SURFACE, relief="flat",
                                        highlightbackground=BORDER, highlightthickness=1)
        self._settings_card.pack(fill="x", padx=10, pady=(8, 0))

        toggle_row = tk.Frame(self._settings_card, bg=SURFACE)
        toggle_row.pack(fill="x")
        tk.Label(toggle_row, text="⚙ ログイン設定 / IP操作",
                 bg=SURFACE, fg=TEXT2, font=FONT_B).pack(side=tk.LEFT, padx=10, pady=5)
        self._toggle_btn = tk.Button(
            toggle_row, text="▶ 開く", font=FONT_S,
            bg=SURFACE, fg=PRIMARY, relief="flat", cursor="hand2",
            command=self._toggle_settings
        )
        self._toggle_btn.pack(side=tk.RIGHT, padx=6)

        # ── ログイン設定パネル（初期非表示）──────────────────────
        self._settings_inner = tk.Frame(self._settings_card, bg=SURFACE)

        self.url_var = tk.StringVar()
        self.id_var  = tk.StringVar(value=self.account)
        self.pw_var  = tk.StringVar(value=self.password)
        self._pw_visible = False  # PW伏せ字フラグ

        conf = load_config()
        if conf:
            self.url_var.set(conf.get('URL', ''))

        for row_i, (lbl_text, var, is_pw) in enumerate(
                [("URL", self.url_var, False),
                 ("ID",  self.id_var,  False),
                 ("PW",  self.pw_var,  True)]):
            tk.Label(self._settings_inner, text=lbl_text, bg=SURFACE, fg=TEXT2,
                     font=FONT_B, width=4, anchor="e").grid(
                row=row_i, column=0, padx=(10, 3), pady=2)
            show_char = "●" if is_pw else ""
            ent = tk.Entry(self._settings_inner, textvariable=var, show=show_char,
                           font=FONT_B, width=26, relief="flat", bg="#f1f3f4",
                           highlightbackground=BORDER, highlightthickness=1)
            ent.grid(row=row_i, column=1, padx=3, pady=2, sticky="ew")
            if is_pw:
                self._pw_entry = ent
                self._pw_toggle_btn = tk.Button(
                    self._settings_inner, text="👁", font=FONT_S,
                    bg=SURFACE, fg=TEXT2, relief="flat", cursor="hand2",
                    command=self._toggle_pw_visibility
                )
                self._pw_toggle_btn.grid(row=row_i, column=2, padx=2)

        tk.Button(
            self._settings_inner, text="💾 設定を保存",
            command=self._save_config_from_ui,
            bg="#34a853", fg="white", relief="flat", cursor="hand2",
            font=FONT_B, padx=8, pady=3
        ).grid(row=3, column=0, columnspan=3, padx=10, pady=(3, 3), sticky="w")

        # IP操作セクション
        tk.Frame(self._settings_inner, bg=BORDER, height=1).grid(
            row=4, column=0, columnspan=3, sticky="ew", padx=6, pady=(4, 2))
        tk.Label(self._settings_inner, text="IP操作", bg=SURFACE, fg=TEXT2,
                 font=FONT_S).grid(row=5, column=0, columnspan=3, sticky="w", padx=10, pady=(2, 2))

        ip_btn_row = tk.Frame(self._settings_inner, bg=SURFACE)
        ip_btn_row.grid(row=6, column=0, columnspan=3, sticky="w", padx=10, pady=(0, 3))

        IP_CMDS = [
            ("① DNS フラッシュ", "ipconfig /flushdns"),
            ("② IP リリース",   "ipconfig /release"),
            ("③ IP 更新",      "ipconfig /renew"),
        ]
        for cmd_label, cmd in IP_CMDS:
            f = tk.Frame(ip_btn_row, bg=SURFACE)
            f.pack(side=tk.LEFT, padx=3)
            tk.Button(f, text=cmd_label, font=FONT_S,
                      bg=SURFACE, fg=PRIMARY, relief="flat", cursor="hand2",
                      highlightbackground=BORDER, highlightthickness=1,
                      padx=6, pady=3,
                      command=lambda c=cmd: self._run_ip_cmd(c)
                      ).pack()
            tk.Label(f, text=cmd, bg=SURFACE, fg="#aaa",
                     font=("Yu Gothic UI", 7)).pack()

        self._ip_label = tk.Label(self._settings_inner, text="現在のIP: -",
                                   bg=SURFACE, fg=TEXT1, font=FONT_S)
        self._ip_label.grid(row=7, column=0, columnspan=3, sticky="w", padx=10, pady=(0, 6))
        self._settings_inner.columnconfigure(1, weight=1)

        # ── ログイン＆開始 統合ボタン ─────────────────────────────
        # 状態: "login" → BEAMSにログイン / "start" → ▶ 開始
        self._main_btn_state = "login"  # "login" or "start"
        action_card = tk.Frame(left, bg=SURFACE, relief="flat",
                               highlightbackground=BORDER, highlightthickness=1)
        action_card.pack(fill="x", padx=10, pady=(5, 0))

        self.main_action_btn = tk.Button(
            action_card, text="🔑  BEAMSにログイン",
            command=self._on_main_action_btn,
            bg=PRIMARY, fg="white", activebackground=PRIMARY2,
            font=FONT_H, relief="flat", cursor="hand2", padx=12, pady=8
        )
        self.main_action_btn.pack(fill="x", padx=10, pady=6)

        # PDF無し警告ラベル（初期非表示）
        self._pdf_warn_label = tk.Label(
            action_card,
            text="⚠ pdfs/ フォルダにPDFがありません。PDFを追加してから開始してください。",
            bg="#fff3e0", fg="#e65100",
            font=("Yu Gothic UI", 8), wraplength=320, justify="left", padx=10, pady=4
        )
        # pack しない（表示は _on_main_action_btn で制御）

        # 後方互換: login_btn / start_btn として参照されている箇所のため alias を張る
        self.login_btn = self.main_action_btn
        self.start_btn = self.main_action_btn

        # ── 操作パネル ─────────────────────────────────────────────
        card_ctrl = tk.Frame(left, bg=SURFACE, relief="flat",
                             highlightbackground=BORDER, highlightthickness=1)
        card_ctrl.pack(fill="x", padx=10, pady=(5, 0))

        # ── 現在の入力規則を大きく表示（誤選択防止）──────────────
        profile_display = tk.Frame(card_ctrl, bg="#e8f0fe",
                                   highlightbackground="#b3c9f5", highlightthickness=1)
        profile_display.pack(fill="x", padx=10, pady=(8, 4))

        tk.Label(profile_display, text="現在の入力規則", bg="#e8f0fe",
                 fg="#5f6368", font=("Yu Gothic UI", 8)).pack(pady=(6, 0))

        _init_profile_name = "（未選択）"
        if self._all_rules:
            first_name, first_cfg = next(iter(self._all_rules.items()))
            _init_profile_name = (first_cfg.get('PROFILE', 'name', fallback=None)
                                  or first_name)
        self._profile_label = tk.Label(
            profile_display,
            text=_init_profile_name,
            bg="#e8f0fe", fg=PRIMARY,
            font=("Yu Gothic UI", 18, "bold"),
            pady=6
        )
        self._profile_label.pack(fill="x")

        tk.Label(card_ctrl,
                 text="① ホームタブを開く  ② ログイン  ③ 入力規則を設定  ④ PDFを追加  ⑤ 開始",
                 bg=SURFACE, fg=TEXT2, font=FONT_S, wraplength=340, justify="left"
                 ).pack(anchor="w", padx=10, pady=(4, 3))

        btn_row = tk.Frame(card_ctrl, bg=SURFACE)
        btn_row.pack(fill="x", padx=10, pady=(0, 6))

        for lbl, cmd in [("📂 PDFs", self.open_pdf_folder), ("📊 ログ", self.open_log_folder)]:
            tk.Button(btn_row, text=lbl, command=cmd,
                      bg=SURFACE, fg=TEXT1, relief="flat", cursor="hand2",
                      font=FONT_B, padx=8, pady=6,
                      highlightbackground=BORDER, highlightthickness=1
                      ).pack(side=tk.LEFT, padx=2)

        # ── PDF一覧パネル ─────────────────────────────────────────
        pdf_panel = tk.Frame(left, bg=SURFACE, relief="flat",
                             highlightbackground=BORDER, highlightthickness=1)
        pdf_panel.pack(fill="x", padx=10, pady=(5, 0))

        pdf_header_row = tk.Frame(pdf_panel, bg=SURFACE)
        pdf_header_row.pack(fill="x", padx=8, pady=(4, 2))
        self.pdf_count_label = tk.Label(
            pdf_header_row, text="未処理PDF: 確認中...",
            bg=SURFACE, fg=TEXT2, font=FONT_S)
        self.pdf_count_label.pack(side=tk.LEFT)
        tk.Button(pdf_header_row, text="📂 開く", font=FONT_S,
                  bg=SURFACE, fg=PRIMARY, relief="flat", cursor="hand2",
                  command=self.open_pdf_folder).pack(side=tk.RIGHT)

        # PDF行を動的に追加するフレーム（スクロール可・最大高さ制限）
        pdf_list_outer = tk.Frame(pdf_panel, bg=SURFACE, height=120)
        pdf_list_outer.pack(fill="x", padx=4, pady=(0, 4))
        pdf_list_outer.pack_propagate(False)

        pdf_canvas = tk.Canvas(pdf_list_outer, bg=SURFACE, highlightthickness=0)
        pdf_sb = tk.Scrollbar(pdf_list_outer, orient="vertical", command=pdf_canvas.yview)
        pdf_canvas.configure(yscrollcommand=pdf_sb.set)
        pdf_sb.pack(side="right", fill="y")
        pdf_canvas.pack(side="left", fill="both", expand=True)

        self._pdf_list_inner = tk.Frame(pdf_canvas, bg=SURFACE)
        _pdf_win = pdf_canvas.create_window((0, 0), window=self._pdf_list_inner, anchor="nw")

        def _on_pdf_inner_conf(e):
            pdf_canvas.configure(scrollregion=pdf_canvas.bbox("all"))
            pdf_canvas.itemconfig(_pdf_win, width=pdf_canvas.winfo_width())
        self._pdf_list_inner.bind("<Configure>", _on_pdf_inner_conf)
        pdf_canvas.bind("<Configure>", lambda e: pdf_canvas.itemconfig(_pdf_win, width=e.width))

        def _mw(event):
            pdf_canvas.yview_scroll(int(-event.delta / 120) if event.delta else
                                    (-1 if event.num == 4 else 1), "units")
        pdf_canvas.bind("<MouseWheel>", _mw)
        pdf_canvas.bind("<Button-4>", _mw)
        pdf_canvas.bind("<Button-5>", _mw)

        self._pdf_canvas = pdf_canvas  # refresh_pdf_list から参照

        # ドロップヒント
        tk.Label(
            left,
            text="💡 PDFをウィンドウ全体にドラッグ＆ドロップで追加できます",
            bg=BG, fg="#80868b", font=("Yu Gothic UI", 7)
        ).pack(anchor="w", padx=12, pady=(2, 0))

        self.refresh_pdf_list()

        # ── REQ 一覧パネル ─────────────────────────────────────────
        req_panel = tk.Frame(left, bg=SURFACE, relief="flat",
                             highlightbackground=BORDER, highlightthickness=1)
        req_panel.pack(fill="x", padx=10, pady=(4, 0))

        req_header = tk.Frame(req_panel, bg=SURFACE)
        req_header.pack(fill="x", padx=8, pady=(4, 2))
        tk.Label(req_header, text="取得済み REQ番号", bg=SURFACE,
                 fg=TEXT2, font=FONT_S).pack(side=tk.LEFT)
        self._req_copy_all_btn = tk.Button(
            req_header, text="📋 全部コピー", font=FONT_S,
            bg=SURFACE, fg=PRIMARY, relief="flat", cursor="hand2",
            command=self._copy_all_req
        )
        self._req_copy_all_btn.pack(side=tk.RIGHT)

        # REQ行を動的に追加するフレーム
        self._req_list_frame = tk.Frame(req_panel, bg=SURFACE)
        self._req_list_frame.pack(fill="x", padx=4, pady=(0, 4))

        # 「まだありません」プレースホルダ
        self._req_empty_label = tk.Label(
            self._req_list_frame, text="（まだありません）",
            bg=SURFACE, fg=TEXT2, font=FONT_S
        )
        self._req_empty_label.pack(anchor="w", padx=8, pady=2)

        # ── ログエリア（折りたたみ式・デフォルト非表示）──────────
        log_toggle_row = tk.Frame(left, bg=BG)
        log_toggle_row.pack(fill="x", padx=10, pady=(6, 0))
        self._log_expanded = False
        self._log_toggle_btn = tk.Button(
            log_toggle_row, text="▶ 実行ログを表示",
            font=FONT_S, bg=BG, fg=TEXT2, relief="flat", cursor="hand2",
            command=self._toggle_log
        )
        self._log_toggle_btn.pack(side=tk.LEFT)
        tk.Button(log_toggle_row, text="全文コピー", font=FONT_S,
                  bg=BG, fg=PRIMARY, relief="flat", cursor="hand2",
                  command=self.copy_log).pack(side=tk.RIGHT)

        self._log_frame = tk.Frame(left, bg=BG)
        # デフォルト非表示 → pack しない

        self.log_area = scrolledtext.ScrolledText(
            self._log_frame, height=14, state='disabled',
            bg=SURFACE, fg=TEXT1, font=FONT_LOG, relief="flat",
            highlightbackground=BORDER, highlightthickness=1, insertbackground=TEXT1
        )
        self.log_area.pack(padx=10, pady=(2, 8), fill="both", expand=True)
        self.log_area.tag_config("success", foreground=SUCCESS)
        self.log_area.tag_config("error",   foreground=DANGER)
        self.log_area.tag_config("info",    foreground="#1a73e8")

        # ════ 右ペイン：入力規則パネル ════════════════════════════
        right = tk.Frame(pane, bg=BG)
        pane.add(right, minsize=300)

        rules_header = tk.Frame(right, bg="#e8f0fe")
        rules_header.pack(fill="x")
        tk.Label(rules_header, text="📋 入力規則", bg="#e8f0fe", fg=PRIMARY,
                 font=("Yu Gothic UI", 10, "bold")).pack(side=tk.LEFT, padx=10, pady=6)

        profile_btn_row = tk.Frame(rules_header, bg="#e8f0fe")
        profile_btn_row.pack(side=tk.LEFT, padx=4)

        # 複製・削除・保存ボタン（ヘッダー右端）
        action_row = tk.Frame(rules_header, bg="#e8f0fe")
        action_row.pack(side=tk.RIGHT, padx=6)

        # 💾 保存ボタン（右上に1つだけ置き、全フィールドを一括保存）
        self._save_rules_btn = tk.Button(
            action_row, text="💾 保存", font=FONT_S,
            bg="#1a73e8", fg="white", relief="flat", cursor="hand2",
            padx=8, pady=2,
            command=self._save_all_rules
        )
        self._save_rules_btn.pack(side=tk.LEFT, padx=2)

        tk.Button(action_row, text="＋ 複製", font=FONT_S,
                  bg=SUCCESS, fg="white", relief="flat", cursor="hand2",
                  padx=6, pady=2,
                  command=self._duplicate_rule).pack(side=tk.LEFT, padx=2)
        tk.Button(action_row, text="🗑 削除", font=FONT_S,
                  bg=DANGER, fg="white", relief="flat", cursor="hand2",
                  padx=6, pady=2,
                  command=self._delete_rule).pack(side=tk.LEFT, padx=2)

        self._profile_btn_row = profile_btn_row  # 後で再描画するために参照を保持
        self._rules_frame = tk.Frame(right, bg=SURFACE)
        self._rules_frame.pack(fill="both", expand=True, padx=0, pady=0)

        self._rebuild_profile_buttons()

        # ── 起動時に右カラムのUIを自動表示（プロファイルが存在する場合）──
        if self._all_rules and self.live_config:
            # 既にアクティブな規則があれば即座に右ペインを描画する
            self._show_livecamera_west_rules(self._rules_frame)
        else:
            tk.Label(self._rules_frame, text="← プロファイルを選択してください",
                     bg=SURFACE, fg=TEXT2, font=("Yu Gothic UI", 10)).pack(pady=40)

        # ── ウィンドウ全体へのPDFドラッグ＆ドロップ ─────────────────
        self._setup_drag_drop()

    def _setup_drag_drop(self):
        """
        ウィンドウ全体をPDFのドロップ受付エリアにする。
        tkinterdnd2 が利用できる場合のみ有効化。
        ドロップされたPDFは pdfs/ フォルダへコピーする（processed/ 移行は不要）。
        既存の手動配置（pdfs/ に直接保存）との共存は維持する。
        """
        try:
            from tkinterdnd2 import DND_FILES
            self.root.drop_target_register(DND_FILES)
            self.root.dnd_bind('<<Drop>>', self._on_drop_pdf)
            self.log("PDFドラッグ＆ドロップ: 有効（ウィンドウ全体に対応）")
        except Exception:
            # tkinterdnd2 未インストール時はドラッグドロップなしで通常動作
            pass

    def _on_drop_pdf(self, event):
        """
        ドロップイベントハンドラ。
        複数ファイルのドロップ、スペースを含むパス（{}で囲まれる）に対応。
        PDFのみを pdfs/ フォルダへコピーし、カウントを更新する。
        """
        raw = event.data.strip()
        # tkinterdnd2 はスペースを含むパスを {} で囲む。複数ファイルも同様。
        # 例: "{C:/path with space/a.pdf} C:/simple/b.pdf"
        import re as _re
        paths = _re.findall(r'\{([^}]+)\}|(\S+)', raw)
        file_list = [p[0] if p[0] else p[1] for p in paths]

        pdf_dir = data_path("pdfs")
        copied = []
        skipped = []
        for path in file_list:
            path = path.strip().strip('"')
            if not path.lower().endswith('.pdf'):
                skipped.append(os.path.basename(path))
                continue
            if not os.path.isfile(path):
                skipped.append(path)
                continue
            dest = os.path.join(pdf_dir, os.path.basename(path))
            try:
                shutil.copy2(path, dest)
                copied.append(os.path.basename(path))
            except Exception as e:
                self.log(f"[ドロップ] コピー失敗: {os.path.basename(path)} → {e}")

        if copied:
            self.log(f"[ドロップ] {len(copied)} 件を pdfs/ にコピーしました: {', '.join(copied)}")
        if skipped:
            self.log(f"[ドロップ] PDF以外のためスキップ: {', '.join(skipped)}")
        self.refresh_pdf_list()

    def _on_close(self):
        """ウィンドウ終了時: 全タイマーをキャンセルしてから破棄する"""
        try:
            if self._pdf_refresh_id:
                self.root.after_cancel(self._pdf_refresh_id)
        except Exception:
            pass
        try:
            self.root.destroy()
        except Exception:
            pass

    def _rebuild_profile_buttons(self):
        """プロファイルボタン行を現在の _all_rules から再描画する"""
        for w in self._profile_btn_row.winfo_children():
            w.destroy()

        FONT_S  = ("Yu Gothic UI", 8)
        PRIMARY = "#1a73e8"
        DANGER  = "#d93025"

        if self._all_rules:
            for _rkey, _rcfg in self._all_rules.items():
                _display = (_rcfg.get('PROFILE', 'name', fallback=None) or _rkey)
                def _make_switch(rkey=_rkey, rcfg=_rcfg, display=_display):
                    def _switch():
                        self.live_config = rcfg
                        self._active_rule_name = rkey
                        self._profile_label.config(text=display)
                        self._show_livecamera_west_rules(self._rules_frame)
                        # プロファイル切り替え時に on_error_mode も再読み込み
                        self.on_error_mode = self._read_on_error_from_live()
                        self.log(f"入力規則を切り替えました: {display}")
                    return _switch
                tk.Button(self._profile_btn_row, text=_display,
                          bg=PRIMARY, fg="white", relief="flat", cursor="hand2",
                          font=FONT_S, padx=8, pady=3,
                          command=_make_switch()
                          ).pack(side=tk.LEFT, padx=2)
        else:
            tk.Label(self._profile_btn_row, text="rules/ にiniファイルがありません",
                     bg="#e8f0fe", fg=DANGER, font=FONT_S).pack(side=tk.LEFT, padx=4)

    def _duplicate_rule(self):
        """現在選択中の入力規則を複製して新しいiniファイルを作成する"""
        if not self.live_config or not self._active_rule_name:
            messagebox.showwarning("複製", "まず入力規則を選択してください。")
            return

        # 新しいファイル名を決定（例: livecamera_west_2.ini）
        base = self._active_rule_name
        rules_dir = data_path("rules")
        i = 2
        while True:
            new_key = f"{base}_{i}"
            new_path = os.path.join(rules_dir, f"{new_key}.ini")
            if not os.path.exists(new_path):
                break
            i += 1

        # 現在の設定をコピー
        import copy, configparser as _cp
        new_cfg = _cp.ConfigParser(interpolation=None)
        for sec in self.live_config.sections():
            new_cfg[sec] = dict(self.live_config[sec])

        # プロファイル名を変更
        cur_name = self.live_config.get('PROFILE', 'name', fallback=self._active_rule_name)
        new_name = f"{cur_name} のコピー"
        if 'PROFILE' not in new_cfg:
            new_cfg['PROFILE'] = {}
        new_cfg['PROFILE']['name'] = new_name

        try:
            with open(new_path, 'w', encoding='utf-8') as f:
                new_cfg.write(f)
        except Exception as e:
            messagebox.showerror("複製エラー", f"ファイルの作成に失敗しました:\n{e}")
            return

        # _all_rules に追加してボタンを再描画
        self._all_rules[new_key] = new_cfg
        self._rebuild_profile_buttons()

        # 新しい規則に切り替える
        self.live_config = new_cfg
        self._active_rule_name = new_key
        self._profile_label.config(text=new_name)
        self._show_livecamera_west_rules(self._rules_frame)
        self.log(f"入力規則を複製しました: {new_name} ({new_key}.ini)")

    def _delete_rule(self):
        """現在選択中の入力規則を削除する"""
        if not self.live_config or not self._active_rule_name:
            messagebox.showwarning("削除", "まず入力規則を選択してください。")
            return

        if len(self._all_rules) <= 1:
            messagebox.showwarning("削除", "入力規則が1つしかありません。最後の規則は削除できません。")
            return

        cur_name = self.live_config.get('PROFILE', 'name',
                                         fallback=self._active_rule_name)
        if not messagebox.askyesno("削除の確認",
                                   f"「{cur_name}」を削除しますか？\nこの操作は元に戻せません。"):
            return

        # ファイルを削除
        rules_dir = data_path("rules")
        target_path = os.path.join(rules_dir, f"{self._active_rule_name}.ini")
        alt_path    = data_path(f"{self._active_rule_name}.ini")
        try:
            if os.path.exists(target_path):
                os.remove(target_path)
            elif os.path.exists(alt_path):
                os.remove(alt_path)
        except Exception as e:
            messagebox.showerror("削除エラー", f"ファイルの削除に失敗しました:\n{e}")
            return

        deleted_key = self._active_rule_name
        del self._all_rules[deleted_key]
        self.log(f"入力規則を削除しました: {cur_name}")

        # 残った最初の規則に切り替える
        first_key, first_cfg = next(iter(self._all_rules.items()))
        first_name = first_cfg.get('PROFILE', 'name', fallback=first_key)
        self.live_config = first_cfg
        self._active_rule_name = first_key
        self._profile_label.config(text=first_name)

        self._rebuild_profile_buttons()
        self._show_livecamera_west_rules(self._rules_frame)
        self.log(f"入力規則を切り替えました: {first_name}")
        if self._settings_expanded:
            self._settings_inner.pack_forget()
            self._toggle_btn.config(text="▶ 開く")
            self._settings_expanded = False
        else:
            self._settings_inner.pack(fill="x", padx=0, pady=(0, 4))
            self._toggle_btn.config(text="▼ 閉じる")
            self._settings_expanded = True

    def _toggle_settings(self):
        if self._settings_expanded:
            self._settings_inner.pack_forget()
            self._toggle_btn.config(text="▶ 開く")
            self._settings_expanded = False
        else:
            self._settings_inner.pack(fill="x", padx=0, pady=(0, 4))
            self._toggle_btn.config(text="▼ 閉じる")
            self._settings_expanded = True

    def _toggle_pw_visibility(self):
        """PWフィールドの伏せ字を切り替える"""
        self._pw_visible = not self._pw_visible
        self._pw_entry.config(show="" if self._pw_visible else "●")
        self._pw_toggle_btn.config(text="🔒" if self._pw_visible else "👁")

    def _save_config_from_ui(self):
        url  = self.url_var.get().strip()
        acc  = self.id_var.get().strip()
        pw   = self.pw_var.get().strip()
        try:
            save_config(url, acc, pw)
            self.log("設定を config.ini に保存しました ✔")
        except Exception as e:
            self.log(f"設定保存エラー: {e}")

    def _run_ip_cmd(self, cmd: str):
        self.log(f"IP操作: {cmd}")
        def _exec():
            try:
                result = subprocess.run(
                    cmd, shell=True, capture_output=True, text=True, encoding='cp932'
                )
                self.log(f"IP操作完了: {result.stdout.strip()[:120]}")
            except Exception as e:
                self.log(f"IP操作エラー: {e}")
            finally:
                # 現在のIPを取得して表示
                try:
                    hostname = socket.gethostname()
                    ip = socket.gethostbyname(hostname)
                    self.root.after(0, lambda: self._ip_label.config(text=f"現在のIP: {ip}"))
                    self.log(f"現在のIP: {ip}")
                except Exception:
                    pass
        threading.Thread(target=_exec, daemon=True).start()

    def show_rules_window(self):
        """入力規則は右ペインに統合済み（後方互換のため残す）"""
        self._show_livecamera_west_rules(self._rules_frame)

    # キー名の日本語マッピング
    _KEY_LABELS = {
        # BASIC
        'apply_date': '申込日', 'sales_method': '獲得手法', 'designated_code': '取扱店CODE',
        'add_code1': '営業担当者番号', 'add_code2': '前確担当者番号', 'checkbox': '郵送コード不要フラグ',
        'special_code': 'NTT販売担当者ID', 'gender_select': '性別', 'relation_select': '契約者との続柄',
        'birth_date': '生年月日',
        # ADDRESS
        'company_kana': '会社名（カナ）', 'company_name': '会社名（漢字）',
        'staff_last_name': '担当者姓（漢字）', 'staff_first_name': '担当者名（漢字）',
        'staff_last_kana': '担当者姓（カナ）', 'staff_first_kana': '担当者名（カナ）',
        'phone': '電話番号', 'zip_code': '郵便番号', 'azacho': '字名丁目',
        'banchi': '番地', 'building': '建物名',
        # SERVICE
        'plan_cross': '商材（クロス）', 'plan_hayabusa': '商材（隼）', 'plan_gigaline': '商材（ギガライン）',
        'plan_mode': '商材選択モード（auto/fixed）',
        'option_hayabusa': '電話プラン ／ オプション固定値',
        'phone_plan': '電話プラン（auto/none/fixed）',
        'current_line': '現在利用中電話回線',
        'house_type': '住宅区分', 'discount_plan': '割引プラン', 'lan_rental': 'NTT無線LANレンタル',
        'billing_detail': '料金請求方法（詳細）', 'billing_destination': '請求書送付先',
        'payment_detail': '支払い方法（詳細）', 'construction_payment': '工事費支払い方法',
        'indoor_wiring': '屋内配線実施', 'addon_change': '付加サービス変更有無',
        'contract_change': '契約内容変更', 'number_transfer': '同番移行',
        'caller_id': '発信番号通知', 'phonebook': '電話帳掲載', 'call_record': '通話記録',
        # OTHER
        'prev_line_type': '移行前回線種別', 'ntt_partner_code': 'NTTパートナーコード',
        'free_box1': '代理様フリーボックス①',
        'ntt_message': 'NTTへの伝言', 'ntt_partner_note': '前確コメント',
        'final_action': '最終操作',
        'on_error': 'エラー時の動作',
    }

    def _show_livecamera_west_rules(self, parent_frame):
        """西ライブカメラの入力規則を右ペインに表示"""
        for w in parent_frame.winfo_children():
            w.destroy()

        # 全フィールドの StringVar を収集する辞書
        # _save_all_rules() がこれを参照して一括保存する
        self._rules_vars = {}       # (sec, key) -> StringVar
        self._rules_name_var = None  # プロファイル名専用 StringVar

        SURFACE = "#ffffff"; BORDER = "#dadce0"; TEXT1 = "#202124"; TEXT2 = "#5f6368"
        PRIMARY = "#1a73e8"

        # スクロール可能なフレーム
        canvas = tk.Canvas(parent_frame, bg=SURFACE, highlightthickness=0)
        sb = tk.Scrollbar(parent_frame, orient="vertical", command=canvas.yview)
        canvas.configure(yscrollcommand=sb.set)
        sb.pack(side="right", fill="y")
        canvas.pack(side="left", fill="both", expand=True)

        inner = tk.Frame(canvas, bg=SURFACE)
        canvas_window = canvas.create_window((0, 0), window=inner, anchor="nw")

        def on_configure(e):
            canvas.configure(scrollregion=canvas.bbox("all"))
            canvas.itemconfig(canvas_window, width=canvas.winfo_width())
        inner.bind("<Configure>", on_configure)
        canvas.bind("<Configure>", lambda e: canvas.itemconfig(canvas_window, width=e.width))

        # ── マウスホイールスクロール ──────────────────────────────
        def _on_mousewheel(event):
            if event.num == 4:
                canvas.yview_scroll(-1, "units")
            elif event.num == 5:
                canvas.yview_scroll(1, "units")
            else:
                canvas.yview_scroll(int(-event.delta / 120), "units")

        def _bind_mousewheel(widget):
            widget.bind("<MouseWheel>", _on_mousewheel)
            widget.bind("<Button-4>",   _on_mousewheel)
            widget.bind("<Button-5>",   _on_mousewheel)

        def _bind_all_children(widget):
            _bind_mousewheel(widget)
            for child in widget.winfo_children():
                _bind_all_children(child)

        _bind_mousewheel(canvas)
        _bind_mousewheel(inner)
        inner.bind("<Configure>", lambda e: (_bind_all_children(inner),
                                              canvas.configure(scrollregion=canvas.bbox("all")),
                                              canvas.itemconfig(canvas_window, width=canvas.winfo_width())))

        # テーブルヘッダー
        header_row = tk.Frame(inner, bg=PRIMARY)
        header_row.pack(fill="x")
        for h, w in [("欄の名前", 20), ("入力内容", 0)]:
            tk.Label(header_row, text=h, bg=PRIMARY, fg="white",
                     font=("Yu Gothic UI", 9, "bold"), width=w, anchor="w",
                     padx=6, pady=4).pack(side="left")

        if not self.live_config:
            tk.Label(inner, text="livecamera_west.ini が見つかりません",
                     bg=SURFACE, fg="red").pack(pady=20)
            return

        # ── プロファイル名編集（個別保存ボタンなし・右上「💾 保存」に統合）────────
        name_frame = tk.Frame(inner, bg=SURFACE,
                              highlightbackground=BORDER, highlightthickness=1)
        name_frame.pack(fill="x", padx=0, pady=(0, 4))
        tk.Label(name_frame, text="入力規則名", bg=SURFACE, fg=TEXT2,
                 font=("Yu Gothic UI", 8), padx=8, pady=3).pack(side="left")
        _cur_name = self.live_config.get('PROFILE', 'name',
                                         fallback=self._active_rule_name or "")
        _name_var = tk.StringVar(value=_cur_name)
        self._rules_name_var = _name_var  # 一括保存時に参照
        name_entry = tk.Entry(name_frame, textvariable=_name_var,
                               font=("Yu Gothic UI", 9, "bold"),
                               relief="flat", bg=SURFACE,
                               highlightbackground=BORDER, highlightthickness=1)
        name_entry.pack(side="left", fill="x", expand=True, padx=4, pady=3)

        SECTION_LABELS = {
            'BASIC':   '基本情報',
            'ADDRESS': '住所・担当者情報',
            'SERVICE': 'サービス設定',
            'OTHER':   'その他',
        }

        row_bg = [SURFACE, "#f1f3f4"]
        ri = 0
        for sec, sec_label in SECTION_LABELS.items():
            if sec not in self.live_config:
                continue
            sec_row = tk.Frame(inner, bg="#e8f0fe")
            sec_row.pack(fill="x", pady=(6, 0))
            tk.Label(sec_row, text=f"▶ {sec_label}", bg="#e8f0fe", fg=PRIMARY,
                     font=("Yu Gothic UI", 9, "bold"), padx=8, pady=3,
                     anchor="w").pack(fill="x")

            for key, val in self.live_config[sec].items():
                if key == 'name':
                    continue
                # phone_plan は option_hayabusa の行に統合して描画するためスキップ
                if key == 'phone_plan':
                    continue
                # plan_mode は plan_cross の行に統合して描画するためスキップ
                if key == 'plan_mode':
                    continue
                # on_error はループ外の専用行で描画するためここではスキップ
                if key == 'on_error':
                    continue
                bg = row_bg[ri % 2]
                frame_row = tk.Frame(inner, bg=bg)
                frame_row.pack(fill="x")

                jp_label = self._KEY_LABELS.get(key, key)
                tk.Label(frame_row, text=jp_label, bg=bg, fg=TEXT1,
                         font=("Yu Gothic UI", 8), width=20, anchor="w",
                         padx=6, pady=3, wraplength=140).pack(side="left")

                is_pdf = val.strip().startswith("PDF:")
                display_val = val.strip()
                if is_pdf:
                    m = re.search(r'PDF:\(([^)]+)\)', display_val)
                    ref_text = f"📄 PDFから ({m.group(1)})" if m else display_val
                    tk.Label(frame_row, text=ref_text, bg=bg, fg="#0d652d",
                             font=("Yu Gothic UI", 8, "italic"), anchor="w",
                             padx=6).pack(side="left", fill="x", expand=True)
                    _sv = tk.StringVar(value=display_val)
                    self._rules_vars[(sec, key)] = _sv

                elif key == 'plan_cross':
                    # ── plan_cross の行に plan_mode ラジオボタンを左統合 ──────
                    _pm_raw = self.live_config[sec].get('plan_mode', 'auto').strip() \
                              if 'plan_mode' in self.live_config[sec] else 'auto'
                    rv_pm = tk.StringVar(value=_pm_raw if _pm_raw else 'auto')
                    self._rules_vars[(sec, 'plan_mode')] = rv_pm
                    for opt, lbl in [('auto', '自動'), ('fixed', '固定値')]:
                        tk.Radiobutton(
                            frame_row, text=lbl, variable=rv_pm, value=opt,
                            bg=bg, fg="#202124",
                            font=("Yu Gothic UI", 8),
                            activebackground=bg,
                        ).pack(side="left", padx=6)
                    # 右側: クロス固定値テキスト入力
                    v = tk.StringVar(value=display_val)
                    self._rules_vars[(sec, key)] = v
                    entry = tk.Entry(frame_row, textvariable=v,
                                     font=("Yu Gothic UI", 8),
                                     relief="flat", bg=bg,
                                     highlightbackground=BORDER, highlightthickness=1)
                    entry.pack(side="left", fill="x", expand=True, padx=4)

                elif key in ('plan_hayabusa', 'plan_gigaline'):
                    # 固定値入力のみ（plan_mode=fixed のとき参照される）
                    v = tk.StringVar(value=display_val)
                    self._rules_vars[(sec, key)] = v
                    entry = tk.Entry(frame_row, textvariable=v,
                                     font=("Yu Gothic UI", 8),
                                     relief="flat", bg=bg,
                                     highlightbackground=BORDER, highlightthickness=1)
                    entry.pack(side="left", fill="x", expand=True, padx=4)

                elif key == 'option_hayabusa':
                    # ── option_hayabusa の行に phone_plan ラジオボタンを左統合 ──
                    _pp_raw = self.live_config[sec].get('phone_plan', 'auto').strip() \
                              if 'phone_plan' in self.live_config[sec] else 'auto'
                    rv_pp = tk.StringVar(value=_pp_raw if _pp_raw else 'auto')
                    self._rules_vars[(sec, 'phone_plan')] = rv_pp
                    for opt, lbl in [('auto', '自動'), ('none', '電話なし'), ('fixed', '固定値')]:
                        tk.Radiobutton(
                            frame_row, text=lbl, variable=rv_pp, value=opt,
                            bg=bg, fg="#202124",
                            font=("Yu Gothic UI", 8),
                            activebackground=bg,
                        ).pack(side="left", padx=4)
                    v = tk.StringVar(value=display_val)
                    self._rules_vars[(sec, key)] = v
                    entry = tk.Entry(frame_row, textvariable=v,
                                     font=("Yu Gothic UI", 8),
                                     relief="flat", bg=bg,
                                     highlightbackground=BORDER, highlightthickness=1)
                    entry.pack(side="left", fill="x", expand=True, padx=4)

                elif key == 'final_action':
                    rv = tk.StringVar(value=display_val if display_val else '何もしない')
                    self._rules_vars[(sec, key)] = rv
                    radio_frame = tk.Frame(frame_row, bg=bg)
                    radio_frame.pack(side="left", fill="x", expand=True, padx=4)
                    for opt in ['何もしない', '保留', '確定登録']:
                        tk.Radiobutton(radio_frame, text=opt, variable=rv, value=opt,
                                       bg=bg, font=("Yu Gothic UI", 8),
                                       activebackground=bg).pack(side="left", padx=3)
                else:
                    v = tk.StringVar(value=display_val)
                    self._rules_vars[(sec, key)] = v
                    entry = tk.Entry(frame_row, textvariable=v,
                                     font=("Yu Gothic UI", 8),
                                     relief="flat", bg=bg,
                                     highlightbackground=BORDER, highlightthickness=1)
                    entry.pack(side="left", fill="x", expand=True, padx=4)
                ri += 1

        # ── on_error 専用行（OTHERセクション末尾に常に表示）──────────────
        # rules.ini に on_error キーがあってもなくても表示する
        if self.live_config and 'OTHER' in self.live_config:
            _cur_on_error = self.live_config['OTHER'].get('on_error', 'stay').strip().lower()
            if _cur_on_error not in ('stay', 'skip'):
                _cur_on_error = 'stay'

            bg_oe = row_bg[ri % 2]
            oe_frame_row = tk.Frame(inner, bg=bg_oe,
                                    highlightbackground="#f5c6c6", highlightthickness=1)
            oe_frame_row.pack(fill="x")
            tk.Label(oe_frame_row, text="エラー時の動作", bg=bg_oe, fg="#202124",
                     font=("Yu Gothic UI", 8), width=20, anchor="w",
                     padx=6, pady=3, wraplength=140).pack(side="left")

            rv_oe = tk.StringVar(value=_cur_on_error)
            self._rules_vars[('OTHER', 'on_error')] = rv_oe

            oe_radio_frame = tk.Frame(oe_frame_row, bg=bg_oe)
            oe_radio_frame.pack(side="left", fill="x", expand=True, padx=4)

            def _oe_changed(var=rv_oe):
                self.on_error_mode = var.get()
                _mode_ja = "その場で停止" if self.on_error_mode == 'stay' else "次の案件へスキップ"
                self.log(f"エラー時動作を変更しました: {_mode_ja}（💾保存で確定）")

            for _oe_val, _oe_lbl, _oe_fg in [
                ('stay', '🔴 その場で停止', '#d93025'),
                ('skip', '⏭ 次の案件へスキップ', '#1a73e8'),
            ]:
                tk.Radiobutton(
                    oe_radio_frame, text=_oe_lbl, variable=rv_oe, value=_oe_val,
                    bg=bg_oe, fg=_oe_fg, selectcolor=bg_oe,
                    activebackground=bg_oe,
                    font=("Yu Gothic UI", 8, "bold"),
                    command=lambda v=rv_oe: _oe_changed(v),
                ).pack(side=tk.LEFT, padx=(0, 8))

    def _save_all_rules(self):
        """右上「💾 保存」ボタン: 全フィールドを一括でiniファイルに書き込む"""
        if not self.live_config:
            self.log("保存エラー: 入力規則が選択されていません")
            return

        # ── プロファイル名 ──────────────────────────────────────────
        if self._rules_name_var:
            new_name = self._rules_name_var.get().strip()
            if new_name:
                if 'PROFILE' not in self.live_config:
                    self.live_config['PROFILE'] = {}
                self.live_config['PROFILE']['name'] = new_name
                # ① 左ペインの大きな規則名ラベルを更新
                self._profile_label.config(text=new_name)
                # ② 右ペインのプロファイル切り替えボタン行を再描画（名前変更を反映）
                self._rebuild_profile_buttons()

        # ── 全フィールド（新キーが未存在の場合もセクションごと追加）──────
        for (sec, key), sv in self._rules_vars.items():
            if not self.live_config:
                continue
            # セクションが存在しなければ新規作成
            if sec not in self.live_config:
                self.live_config[sec] = {}
            # キーが存在しなければ新規追加、存在すれば上書き
            self.live_config[sec][key] = sv.get()
            if key not in self.live_config[sec]:
                self.log(f"  [新規追加] [{sec}] {key} = {sv.get()}")

        # ── ファイル書き込み（1回だけ）──────────────────────────────
        try:
            rname = self._active_rule_name or "livecamera_west"
            rpath = data_path("rules", f"{rname}.ini")
            if not os.path.exists(rpath):
                rpath = data_path(f"{rname}.ini")
            with open(rpath, 'w', encoding='utf-8') as f:
                self.live_config.write(f)
            self.log(f"入力規則を保存しました ✔ ({rname}.ini)")
            # 保存後に on_error_mode を同期
            self.on_error_mode = self._read_on_error_from_live()
            # 保存ボタンを一瞬フラッシュして完了を視覚的にフィードバック
            if hasattr(self, '_save_rules_btn'):
                self._save_rules_btn.config(bg="#34a853", text="✔ 保存済")
                self.root.after(1500, lambda: self._save_rules_btn.config(
                    bg="#1a73e8", text="💾 保存"))
        except Exception as e:
            self.log(f"保存エラー: {e}")

    # ----------------------------------------------------------------

    def _bring_browser_to_front(self):
        """ブラウザウィンドウを前面に出す（ログイン確認・手動操作用）"""
        if self.page:
            try:
                self.page.bring_to_front()
                self.log("ブラウザを前面に表示しました")
            except Exception as e:
                self.log(f"前面表示エラー: {e}")
        else:
            self.log("ブラウザがまだ起動していません")

    def _toggle_log(self):
        """実行ログの折りたたみ/展開"""
        if self._log_expanded:
            self._log_frame.pack_forget()
            self._log_toggle_btn.config(text="▶ 実行ログを表示")
            self._log_expanded = False
        else:
            self._log_frame.pack(fill="both", expand=True, after=None)
            # ログ行の後ろに配置（req_row の次）
            self._log_frame.pack(fill="both", expand=True)
            self._log_toggle_btn.config(text="▼ 実行ログを隠す")
            self._log_expanded = True
            self.log_area.see(tk.END)

    def _auto_expand_log(self):
        """エラー発生時など自動的にログを展開する"""
        if not self._log_expanded:
            self._toggle_log()

    def _update_req_display(self, req_number: str):
        """REQ番号をリストに追加してUIに反映する（メインスレッドから呼ぶこと）"""
        if not req_number or req_number in self._req_list:
            return
        self._req_list.append(req_number)

        # プレースホルダを隠す
        self._req_empty_label.pack_forget()

        SUCCESS  = "#1e8e3e"
        SURFACE  = "#ffffff"
        PRIMARY  = "#1a73e8"
        BORDER   = "#dadce0"
        FONT_S   = ("Yu Gothic UI", 8)

        row = tk.Frame(self._req_list_frame, bg=SURFACE)
        row.pack(fill="x", pady=1)

        # 番号ラベル（黄色ハイライト → 1.5秒後に緑）
        lbl = tk.Label(row, text=req_number, bg=SURFACE,
                       fg="#b45309", font=("Yu Gothic UI", 10, "bold"))
        lbl.pack(side=tk.LEFT, padx=(8, 4))
        self.root.after(1500, lambda l=lbl: l.config(fg=SUCCESS))

        # 個別コピーボタン
        tk.Button(row, text="📋", font=FONT_S,
                  bg=SURFACE, fg=PRIMARY, relief="flat", cursor="hand2",
                  padx=2,
                  command=lambda r=req_number: self.copy(r)
                  ).pack(side=tk.LEFT)

    def _copy_all_req(self):
        """セッション中の全REQを改行区切りでクリップボードにコピー"""
        if not self._req_list:
            self.log("コピーするREQがありません")
            return
        self.copy("\n".join(self._req_list))
        self.log(f"全REQ {len(self._req_list)} 件をコピーしました")

    def refresh_pdf_list(self):
        """pdfs/ フォルダの未処理PDFをスキャンしてUIのリストを更新する（5秒ごとに自動更新）"""
        # ウィンドウが既に破棄されていたらタイマーを止める
        try:
            if not self.root.winfo_exists():
                return
        except Exception:
            return

        SURFACE = "#ffffff"
        PRIMARY = "#1a73e8"
        SUCCESS = "#1e8e3e"
        TEXT1   = "#202124"
        TEXT2   = "#5f6368"
        FONT_S  = ("Yu Gothic UI", 8)

        try:
            all_files = sorted(
                f for f in os.listdir(data_path("pdfs"))
                if f.lower().endswith(".pdf")
            )
            unprocessed = [f for f in all_files if f not in self.processed_files]
            count = len(unprocessed)

            # カウントラベル更新
            self.pdf_count_label.config(
                text=f"未処理PDF: {count} 件",
                fg=PRIMARY if count else TEXT2
            )

            # リスト内フレームを再描画
            for w in self._pdf_list_inner.winfo_children():
                w.destroy()

            if not unprocessed:
                tk.Label(self._pdf_list_inner, text="（PDFがありません）",
                         bg=SURFACE, fg=TEXT2, font=FONT_S
                         ).pack(anchor="w", padx=8, pady=4)
            else:
                for fname in unprocessed:
                    is_error = fname in self.error_files
                    row_bg   = "#fff0f0" if is_error else SURFACE
                    row = tk.Frame(self._pdf_list_inner, bg=row_bg)
                    row.pack(fill="x", pady=1)
                    # ファイルアイコン＋名前
                    icon = "⚠️" if is_error else "📄"
                    tk.Label(row, text=icon, bg=row_bg, font=FONT_S
                             ).pack(side="left", padx=(6, 2))
                    # 名前が長い場合は省略（末尾30文字 + 先頭）
                    display = fname if len(fname) <= 44 else fname[:20] + "…" + fname[-20:]
                    fg_color = "#d93025" if is_error else TEXT1
                    lbl = tk.Label(row, text=display, bg=row_bg, fg=fg_color,
                             font=(FONT_S[0], FONT_S[1], "bold") if is_error else FONT_S,
                             anchor="w")
                    lbl.pack(side="left", fill="x", expand=True)
                    if is_error:
                        tk.Label(row, text="エラー", bg="#d93025", fg="white",
                                 font=("Yu Gothic UI", 7, "bold"),
                                 padx=4, pady=1).pack(side="right", padx=(0, 4))

            # Canvas の scrollregion を強制更新
            self._pdf_list_inner.update_idletasks()
            self._pdf_canvas.configure(scrollregion=self._pdf_canvas.bbox("all"))

        except Exception:
            pass

        self._pdf_refresh_id = self.root.after(5000, self.refresh_pdf_list)

    # 後方互換エイリアス
    def refresh_pdf_count(self):
        self.refresh_pdf_list()

    def open_pdf_folder(self):
        p = data_path("pdfs")
        os.makedirs(p, exist_ok=True)
        os.startfile(p)

    def open_log_folder(self):
        p = data_path("log")
        os.makedirs(p, exist_ok=True)
        os.startfile(p)

    def log(self, message: str):
        def _write():
            self.log_area.configure(state='normal')
            ts = datetime.datetime.now().strftime('%H:%M:%S')
            line = f"[{ts}] {message}\n"
            if "完了 ✔" in message or "成功" in message:
                tag = "success"
            elif "エラー" in message or "失敗" in message or "警告" in message:
                tag = "error"
                # エラー・失敗時は自動でログを展開
                self._auto_expand_log()
            elif ">>>" in message or "開始" in message:
                tag = "info"
            else:
                tag = None
            if tag:
                self.log_area.insert(tk.END, line, tag)
            else:
                self.log_area.insert(tk.END, line)
            self.log_area.see(tk.END)
            self.log_area.configure(state='disabled')
        self.root.after(0, _write)

    def copy(self, text):
        self.root.clipboard_clear(); self.root.clipboard_append(text)
        self.log("クリップボードにコピーしました")

    def copy_log(self):
        content = self.log_area.get("1.0", tk.END)
        self.root.clipboard_clear()
        self.root.clipboard_append(content)
        self.log("ログを全文コピーしました")

    def notify_error(self, title: str, message: str):
        self.root.after(0, lambda: messagebox.showerror(title, message))

    def _on_main_action_btn(self):
        """統合ボタンのクリックハンドラ。状態に応じてログインまたは開始処理を呼ぶ。"""
        if self._main_btn_state == "login":
            self.request_login()
        else:
            # PDF存在チェック
            try:
                pdfs = [f for f in os.listdir(data_path("pdfs"))
                        if f.lower().endswith(".pdf") and f not in self.processed_files]
            except Exception:
                pdfs = []
            if not pdfs:
                # 警告ラベルを表示（2秒後に自動非表示）
                self._pdf_warn_label.pack(fill="x", padx=10, pady=(0, 6))
                self.root.after(4000, lambda: self._pdf_warn_label.pack_forget())
                return
            self._pdf_warn_label.pack_forget()
            self.request_automation()

    def _switch_to_start_btn(self):
        """ログイン完了後、ボタンを「▶ 開始」モードに切り替える"""
        SUCCESS = "#1e8e3e"
        self._main_btn_state = "start"
        self.main_action_btn.config(
            text="▶  開始",
            bg=SUCCESS, activebackground="#166d35",
            state="normal"
        )

    def request_login(self):
        if not self.page:
            self.log("エラー：ブラウザがまだ起動していません。"); return
        self.login_btn.config(state="disabled")
        self.task_queue.append(self._do_login)

    def _do_login(self):
        try:
            self.log("ログイン中...")
            account  = self.id_var.get()
            password = self.pw_var.get()
            self.page.fill("id=username", account)
            self.page.fill("id=password", password)
            self.page.click("input[type='submit'].btn")
            self.page.wait_for_load_state("domcontentloaded", timeout=15000)
            self.log("ログイン完了 ✔")
            # ボタンを「開始」モードに切り替え
            self.root.after(0, self._switch_to_start_btn)
        except Exception as e:
            self.log(f"ログイン失敗: {e}")
        finally:
            self.root.after(0, lambda: self.main_action_btn.config(state="normal"))

    def launch_browser_init(self):
        def browser_loop():
            try:
                self.log("ブラウザ（Edge）を起動しています...")
                self.pw_manager = sync_playwright()
                self.playwright = self.pw_manager.start()
                self.browser = self.playwright.chromium.launch(
                    headless=False, channel="msedge",
                    args=[
                        "--start-maximized",
                        "--disable-extensions",
                        "--disable-component-extensions-with-background-pages",
                        "--disable-plugins",
                        "--disable-translate",
                        "--disable-infobars",
                        "--no-default-browser-check",
                        "--disable-background-timer-throttling",  # バックグラウンド時のタイマー抑制を無効化
                        "--disable-renderer-backgrounding",       # バックグラウンド時のレンダラー抑制を無効化
                    ]
                )
                self.context = self.browser.new_context(
                    no_viewport=True,
                    java_script_enabled=True,
                )
                self.page = self.context.new_page()
                conf = load_config()
                if conf:
                    self.page.goto(conf['URL'])
                    self.log("ブラウザ準備完了。ログインして法人登録画面へ進んでください。")
                while True:
                    if self.task_queue:
                        self.task_queue.pop(0)()
                    time.sleep(0.2)
            except Exception as e:
                self.log(f"ブラウザ起動エラー: {e}")

        threading.Thread(target=browser_loop, daemon=True).start()

    def request_automation(self):
        if not self.page:
            self.log("エラー：ブラウザがまだ起動していません。"); return
        self.task_queue.append(self.run_automation_process)
        self.start_btn.config(state="disabled")
        self.log("自動入力をキューに追加しました。")

    def run_automation_process(self):
        pdf_dir       = data_path("pdfs")
        processed_dir = data_path("processed")
        try:
            if not self.extractor:
                self.log("エラー：pdf_layout.ini が読み込めません。"); return
            if not self.field_ids:
                self.log("エラー：field_ids.ini が読み込めません。"); return

            # REQ番号を受け取るコールバック（スレッドセーフにUIへ反映）
            _current_req = {"value": ""}
            def _on_req(req_str):
                _current_req["value"] = req_str
                self.root.after(0, lambda r=req_str: self._update_req_display(r))

            operator = BeamsOperator(
                self.page, self.today_str, self.field_ids, self.log,
                live_config=self.live_config,
                on_req_acquired=_on_req,
            )
            all_files   = sorted(f for f in os.listdir(pdf_dir) if f.lower().endswith(".pdf"))
            unprocessed = [f for f in all_files if f not in self.processed_files]

            if not unprocessed:
                self.log("未処理のPDFはありません。"); return

            self.log(f"未処理PDF: {len(unprocessed)} 件 — 処理を開始します")

            for filename in unprocessed:
                pdf_path = os.path.join(pdf_dir, filename)
                self.log(""); self.log(f">>> 処理開始: {filename}")
                pdf_data: dict = {}

                try:
                    pdf_data = self.extractor.extract(pdf_path)
                    _raw_name = os.path.splitext(filename)[0]
                    _candidate = _raw_name[-14:]
                    if len(_candidate) == 14 and _candidate.startswith('P') and _candidate[1:].isdigit():
                        pdf_data['source_filename'] = _candidate
                    else:
                        pdf_data['source_filename'] = ''
                        self.log(f"  [申込書番号] ファイル名から14桁Pコードを取得できませんでした（スキップ）: {_raw_name}")
                    ap = pdf_data.get("address_parts", {})
                    self.log(
                        f"  [解析] 会社カナ:{pdf_data.get('company_kana')}  "
                        f"会社名:{pdf_data.get('company_name')}  "
                        f"担当者:{pdf_data.get('staff_name')}  "
                        f"TEL:{pdf_data.get('phone')}  "
                        f"〒{pdf_data.get('zip_code')}"
                    )
                    self.log(
                        f"  [住所] 大字通称名:「{pdf_data.get('oaza','')}」  "
                        f"字名丁目:「{ap.get('azacho','')}」  "
                        f"番地:「{ap.get('banchi','')}」  "
                        f"建物:「{ap.get('building','')}」"
                    )
                    self.log(
                        f"  [請求] 請求方法:{pdf_data.get('billing_method')}  "
                        f"支払:{pdf_data.get('payment_method')}  "
                        f"〒{pdf_data.get('billing_zip')}  "
                        f"{pdf_data.get('billing_address')}"
                    )

                    operator.section_basic_info()
                    operator.section_address_info(pdf_data)
                    operator.section_billing_info(pdf_data)
                    operator.section_service_info(pdf_data)

                    dest_path = os.path.join(processed_dir, filename)
                    for attempt in range(1, 4):
                        try:
                            shutil.move(pdf_path, dest_path)
                            self.log(f"  [移動] {filename} → processed/")
                            break
                        except Exception as move_err:
                            if attempt < 3:
                                self.log(f"  [移動待機] ファイル使用中 ({attempt}/3)。3秒後にリトライ...")
                                time.sleep(3)
                            else:
                                self.log(f"  [移動失敗] リトライ上限に達しました。手動で移動してください: {move_err}")

                    self.processed_files.add(filename)
                    self.csv_logger.write(filename, pdf_data, "成功",
                                          req_number=_current_req["value"])
                    self.log(f">>> {filename} 完了 ✔")

                except Exception as file_err:
                    err_msg = str(file_err)
                    self.log(f"【ファイルエラー】{filename}: {err_msg}")
                    self.error_files.add(filename)
                    self.csv_logger.write(filename, pdf_data, "失敗", err_msg,
                                          req_number=_current_req["value"])

                    if self.on_error_mode == 'skip':
                        # ── スキップモード: 追加ウィンドウを閉じて次のPDFへ ──
                        self.log(f"  [スキップ] エラーが発生しました。次の案件へ移動します...")
                        # UIのPDF一覧を更新してエラーを強調表示
                        self.root.after(0, self.refresh_pdf_list)
                        try:
                            # ① 追加ポップアップがあれば閉じる（ルックアップ等）
                            closed_count = 0
                            for ctx_page in list(self.context.pages):
                                if ctx_page != self.page:
                                    try:
                                        ctx_page.close()
                                        closed_count += 1
                                    except Exception:
                                        pass
                            if closed_count:
                                self.log(f"  [スキップ] 追加ウィンドウを {closed_count} 件閉じました")
                                # ポップアップ閉鎖後、メインページが安定するまで待機
                                try:
                                    self.page.wait_for_load_state("domcontentloaded", timeout=8000)
                                except Exception:
                                    pass
                                self.page.wait_for_timeout(800)

                            # ② 「前ページに戻る」ボタンをクリック（あれば）
                            try:
                                prev_btn = self.page.locator(
                                    "id=j_id0:sve_form1:pageBlock1:j_id82:customButton4"
                                )
                                prev_btn.wait_for(state="visible", timeout=4000)
                                try:
                                    self.page.bring_to_front()
                                    self.page.wait_for_timeout(200)
                                except Exception:
                                    pass
                                prev_btn.click()
                                self.page.wait_for_load_state("domcontentloaded", timeout=15000)
                                self.wait_for_loading(timeout=10000)
                                self.log("  [スキップ] 「前ページに戻る」をクリックしました")
                            except Exception:
                                self.log("  [スキップ] 「前ページに戻る」ボタンなし（スキップ）")

                            # ③ 「閉じる」ボタンをクリック
                            _closed_ok = False
                            try:
                                close_btn = self.page.locator(
                                    "id=j_id0:sve_form1:pageBlock1:j_id82:cancelButton1"
                                )
                                close_btn.wait_for(state="visible", timeout=6000)
                                try:
                                    self.page.bring_to_front()
                                    self.page.wait_for_timeout(200)
                                except Exception:
                                    pass
                                close_btn.click()
                                self.page.wait_for_load_state("domcontentloaded", timeout=15000)
                                self.wait_for_loading(timeout=15000)
                                self.log("  [スキップ] 「閉じる」をクリックしました ✔")
                                _closed_ok = True
                            except Exception as _e:
                                self.log(f"  [スキップ] 「閉じる」ボタンが見つかりません。URLリロードで復帰します: {str(_e)[:60]}")

                            # ④ 閉じるボタンが押せなかった場合はURL直接リロードでフォールバック
                            if not _closed_ok:
                                try:
                                    conf = load_config()
                                    if conf:
                                        self.page.goto(conf['URL'], timeout=30000)
                                        self.page.wait_for_load_state("domcontentloaded", timeout=15000)
                                        self.wait_for_loading(timeout=15000)
                                        self.log("  [スキップ] URLリロードで復帰しました ✔")
                                except Exception as _re:
                                    self.log(f"  [スキップ] URLリロード失敗: {_re}")

                        except Exception as skip_err:
                            self.log(f"  [スキップ失敗] {skip_err}")
                    else:
                        # ── 停止モード（現行動作）──────────────────────────
                        self.notify_error(
                            "処理エラー",
                            f"{filename} の処理中にエラーが発生しました。\n\n{err_msg}\n\n次のファイルへ進みます。"
                        )
                        # エラー後にBEAMSのページをリセット（次ファイルで法人登録タブが見つからない問題を防ぐ）
                        try:
                            conf = load_config()
                            if conf:
                                self.log(f"  [リセット] BEAMSページをリロードします...")
                                self.page.goto(conf['URL'], timeout=30000)
                                self.page.wait_for_load_state("domcontentloaded", timeout=15000)
                                self.wait_for_loading(timeout=15000)
                                self.log(f"  [リセット] 完了 → 次のファイルへ")
                        except Exception as reset_err:
                            self.log(f"  [リセット失敗] {reset_err}")

            self.log(""); self.log(">>> すべてのPDFの処理が完了しました")

        except Exception as e:
            self.log(f"【致命的エラー】: {e}")
            self.notify_error("致命的エラー", str(e))
        finally:
            self.root.after(0, lambda: self.main_action_btn.config(state="normal"))
            self.root.after(0, self.refresh_pdf_list)


# =====================================================
# エントリポイント
# =====================================================
if __name__ == "__main__":
    ensure_dirs()
    conf = load_config()
    if conf:
        app = BeamsApp(conf['ACCOUNT'], conf['PASSWORD'])
        app.root.mainloop()