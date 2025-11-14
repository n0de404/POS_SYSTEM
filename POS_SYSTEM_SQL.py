import sys
import os
import re
import glob
import importlib
from datetime import datetime, timedelta
import time
from functools import partial
import tempfile
import subprocess
import json  # Import the json module
from copy import deepcopy
import types
import shutil
import textwrap
import random
import uuid
from collections import Counter
try:
    import serial
    from serial.tools import list_ports
except ImportError:
    serial = None
    list_ports = None
try:
    import win32print
    import win32ui
    import win32con
except ImportError:
    win32print = None
    win32ui = None
    win32con = None
import pandas as pd
from reportlab.lib.pagesizes import letter, A4
from reportlab.pdfgen import canvas
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.lib.units import inch, mm
from reportlab.lib import colors
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
import requests
from PyQt6.QtWidgets import QSizePolicy, QSpacerItem, QTabWidget  # Import QTabWidget
from PyQt6.QtWidgets import QFileDialog  # Import QFileDialog for file dialog
# --- New imports for MySQL-backed persistence ---
import mysql.connector
from mysql.connector import Error
from werkzeug.security import check_password_hash, generate_password_hash
from PIL import Image, ImageQt, ImageOps
from PyQt6.QtWidgets import (QApplication, QCompleter, QGroupBox, QMainWindow, QTableWidget, QTableWidgetItem, QWidget, QLabel, QLineEdit, QPushButton, QComboBox,
                             QListWidget, QListWidgetItem, QTextEdit, QHBoxLayout, QVBoxLayout, QGridLayout, QFormLayout, QDialog,
                             QMessageBox, QInputDialog, QFileDialog, QScrollArea, QFrame, QSpinBox,
                             QDoubleSpinBox, QDialogButtonBox, QCheckBox, QHeaderView, QToolButton, QAbstractItemView, QMenu)
from PyQt6.QtGui import QColor, QPixmap, QAction, QActionGroup, QIcon, QFont, QPalette, QPainter, QPen, QBrush, QConicalGradient, QShortcut, QKeySequence
from PyQt6.QtCore import Qt, QSize, QStringListModel, QPointF, QRectF, QThread, pyqtSignal, QTimer
# --- Global Variables ---
products = {}  # Stores product data from the database: {barcode: [{"name": "...", "price": ..., "stock": ..., "image_filename": "...", "promos": {...}}]}
product_variant_lookup = {}  # Maps SKU (including promo variants) to lookup data for scanning/searching
product_id_lookup = {}  # Maps product_id back to (barcode, variant index) for quick reverse lookups
cart = []  # Stores items currently in the cart
current_item_count = 1  # Default quantity for next scanned item
current_discount = 0.0  # Default discount percentage for next scanned item
# Added global variables for cash and gcash tendered totals
total_cash_tendered = 0.0
total_gcash_tendered = 0.0
current_sales_number = 1  # For unique sales receipt numbers
current_transaction_number = 1  # For unique transaction numbers
inventory_summary = {}
sales_summary = {}  # Stores sales data for reporting: {barcode: {"qty_sold": ..., "revenue": ...}}
promo_inventory_map = {}  # Maps promo code to the number of base units consumed per sale
product_promo_columns = []  # Tracks additional promo pricing codes detected in the database
bundle_promos = {}  # Stores bundle promos with their component details
current_theme_preference = "system"
current_theme_effective = "light"
basket_promos = []  # Stores basket-size promo tiers
PRODUCT_CODE_COLUMN_AVAILABLE = None  # Tracks whether products.code exists
BUNDLE_IMAGE_COLUMN_AVAILABLE = None  # Tracks bundles.image_filename availability
SALES_REFERENCE_COLUMNS_READY = None  # Tracks presence of ref_no columns on sales tables
users_data = {}  # Stores usernames and hashed passwords: {username: {"password_hash": "...", "is_admin": bool}}
current_user_name = None  # Stores the username of the currently logged-in user
ADMIN_PASSWORD_FILE = "admin_password.txt"
DEFAULT_ADMIN_PASSWORD = "p@ssw0rd01"
if getattr(sys, "frozen", False) and hasattr(sys, "executable"):
    BASE_DIR = os.path.dirname(os.path.abspath(sys.executable))
else:
    BASE_DIR = os.path.dirname(os.path.abspath(__file__))
USERS_FILE = "users.txt"  # Name of the text file for user credentials
PRODUCT_IMAGE_FOLDER = os.path.join(BASE_DIR, "product_images")  # Folder where product images are stored
SUPPORTED_IMAGE_EXTENSIONS = (".png", ".jpg", ".jpeg", ".bmp", ".gif", ".webp")
ACTIVITY_LOG_FILE = os.path.join(BASE_DIR, "activity_logs.jsonl")
SALES_VAULT_FILE = os.path.join(BASE_DIR, "sales_vault.json")
# Vault keeps a running ledger across exports so longer periods can be reported later
sales_summary_vault = {}
total_cash_tendered_vault = 0.0
total_gcash_tendered_vault = 0.0
sales_vault_period_start = None
transaction_tracking_index = {}
TRANSACTION_REFERENCE_PREFIX = "POS"
LOCAL_EXPORT_REFERENCE_PREFIX = "LOCAL"
REFERENCE_TIMESTAMP_FORMAT = "%Y-%m-%dT%H:%M:%S"
# Preferred printer for direct receipt printing on Windows; leave blank to use system default.
CUSTOM_RECEIPT_PRINTER_NAME = "RONGTA 58mm Series Printer"
# --- API Integration ---
API_SETTINGS_FILE = "api_settings.json"
API_TOKEN_CACHE_FILE = "api_token.json"
DEFAULT_API_SETTINGS = {
    "base_url": "http://<url>/philtop/IMS/index.php/v1",
    "warehouse_id": 3,
    "customer_id": 1471,
    "include_zero": False,
    "login_identity": "jobapi",
    "login_password": "replace-me",
    "token_ttl_seconds": 604800,
    "force_new_token_on_login": False,
    "order_reference_prefix": "POS",
    "default_reference": None,
    "default_notes": "Submitted via POS application",
    "include_unit_price": False,
    "clear_sales_summary_after_post": False,
    "request_timeout_seconds": 30,
    "use_inventory_stub": True,
    "inventory_stub_file": "inventory_stub.json",
    "use_sales_stub": True,
    "sales_stub_file": "sales_invoice_stub.json",
}

api_settings = None
api_token_cache = None
def normalize_image_filename(filename):
    """
    Returns a sanitized image filename limited to the final path segment.
    """
    if not filename:
        return ""
    filename = filename.strip()
    if not filename:
        return ""
    return os.path.basename(filename)

def resolve_product_image_filename(stock_no, image_filename=None):
    """
    Determines the best-matching image filename for a product.
    The search prefers an explicitly stored filename (relative to PRODUCT_IMAGE_FOLDER)
    and falls back to files named after the stock number with common image extensions.
    """
    def _find_by_base_name(base_name):
        if not base_name:
            return ""
        for ext in SUPPORTED_IMAGE_EXTENSIONS:
            guess = f"{base_name}{ext}"
            guess_path = os.path.join(PRODUCT_IMAGE_FOLDER, guess)
            if os.path.exists(guess_path):
                return guess
        pattern = os.path.join(PRODUCT_IMAGE_FOLDER, f"{base_name}.*")
        for match in glob.glob(pattern):
            if os.path.isfile(match):
                name = os.path.basename(match)
                _, match_ext = os.path.splitext(name)
                if not match_ext or match_ext.lower() in SUPPORTED_IMAGE_EXTENSIONS:
                    return name
        return ""
    candidate = normalize_image_filename(image_filename)
    if candidate:
        candidate_path = os.path.join(PRODUCT_IMAGE_FOLDER, candidate)
        if os.path.exists(candidate_path):
            return candidate
        base_candidate, _ = os.path.splitext(candidate)
        fallback = _find_by_base_name(base_candidate)
        if fallback:
            return fallback
    stock_value = str(stock_no).strip() if stock_no is not None else ""
    if stock_value:
        fallback = _find_by_base_name(stock_value)
        if fallback:
            return fallback
    return candidate
def ensure_inventory_stub_file(file_path, parent=None):
    """
    Validates that the configured inventory stub file exists on disk.
    """
    candidate = os.path.abspath(file_path)
    if os.path.exists(candidate):
        return True
    show_warning("Inventory Stub", f"Inventory stub file '{candidate}' was not found.", parent)
    return False
# --- Database configuration ---
DB_CONFIG_FILE = os.path.join(BASE_DIR, "db_config.json")


def load_db_config():
    """Load database connection settings from the JSON configuration file."""
    try:
        with open(DB_CONFIG_FILE, "r", encoding="utf-8") as config_file:
            config = json.load(config_file)
    except FileNotFoundError:
        print(f"Database configuration file not found: {DB_CONFIG_FILE}")
        return {}
    except json.JSONDecodeError as exc:
        print(f"Invalid JSON in database configuration file: {exc}")
        return {}
    except Exception as exc:
        print(f"Unexpected error reading database configuration: {exc}")
        return {}

    if not isinstance(config, dict):
        print("Database configuration must be a JSON object.")
        return {}

    return config


DB_CONFIG = load_db_config()
# --- Promo pricing support tracking ---
PROMO_PRICE_COLUMN_AVAILABLE = None
PROMO_PRICE_WARNING_SHOWN = False
# --- New Global Variables for Auto-Saving ---
UI_PREFERENCES_FILE = "ui_preferences.json"
# --- New Global Variable for Receipts Archive ---
receipts_archive = {}  # Stores all generated receipts: {"SALES#_TRANS#": "receipt_text_content"}
RECEIPT_FONT_NAME = "MonospaceTypewriter"
FALLBACK_RECEIPT_FONT_NAME = "Courier"
# Try TT Interphases font first, then fall back to MonospaceTypewriter
RECEIPT_FONT_FILE = os.path.join(BASE_DIR, "TT Interphases Pro Mono Trial Regular.ttf")
if not os.path.exists(RECEIPT_FONT_FILE):
    RECEIPT_FONT_FILE = os.path.join(BASE_DIR, "MonospaceTypewriter.ttf")
RECEIPT_PAGE_WIDTH_MM = 58
RECEIPT_MARGIN_MM = 0.7
RECEIPT_TOP_MARGIN_MM = 3
RECEIPT_BASE_FONT_SIZE = 11
RECEIPT_BOOTH_SIZE_INCREMENT = 3
RECEIPT_BOOTH_PREFIX = "Booth #:"
RECEIPT_MIN_FONT_SIZE = 10
RECEIPT_PRICE_COLUMN_WIDTH = 10
RECEIPT_LEFT_COLUMN_TARGET = 24
RECEIPT_LINE_SPACING_MULTIPLIER = 1.2
RECEIPT_BOLD_OFFSET_PT = 0.45  # Positive offset doubles the glyph for a bolder appearance
RECEIPT_SIZE_TAG_PATTERN = re.compile(r"^\s*\[\[size\s*=\s*([0-9]+(?:\.[0-9]+)?)\]\]")


def ensure_mysql_locale_support():
    """
    Ensures mysql-connector can resolve English locale data even in packaged builds
    where locale resources are not copied alongside the library.
    """
    try:
        from mysql.connector import locales
    except Exception:
        return

    en_us_module_name = "mysql.connector.locales.en_US.client_error"
    fallback_errors = {}
    try:
        en_us_module = importlib.import_module(en_us_module_name)
        fallback_errors = getattr(en_us_module, "client_error", {})
        sys.modules.setdefault(en_us_module_name, en_us_module)
    except ImportError:
        # Provide stub modules for en_US so subsequent imports succeed.
        if en_us_module_name not in sys.modules:
            en_us_stub = types.ModuleType(en_us_module_name)
            en_us_stub.client_error = fallback_errors
            sys.modules[en_us_module_name] = en_us_stub
    en_us_pkg_name = "mysql.connector.locales.en_US"
    if en_us_pkg_name not in sys.modules:
        en_us_pkg = types.ModuleType(en_us_pkg_name)
        en_us_pkg.__path__ = []
        en_us_pkg.client_error = sys.modules[en_us_module_name]
        sys.modules[en_us_pkg_name] = en_us_pkg

    def _register_alias(lang_code):
        package_name = f"mysql.connector.locales.{lang_code}"
        module_name = f"{package_name}.client_error"
        client_module = sys.modules.get(module_name)
        if client_module is None:
            client_module = types.ModuleType(module_name)
            sys.modules[module_name] = client_module
        client_module.client_error = fallback_errors
        pkg_module = sys.modules.get(package_name)
        if pkg_module is None:
            pkg_module = types.ModuleType(package_name)
            pkg_module.__path__ = []
            sys.modules[package_name] = pkg_module
        sys.modules[package_name].client_error = client_module

    for alias in ("eng", "en"):
        _register_alias(alias)

    original = getattr(locales, "_original_get_client_error", locales.get_client_error)

    def _patched_get_client_error(language=None):
        normalized = (language or "").lower()
        if normalized in {"eng", "en", "english"}:
            language = "en_US"
        try:
            return original(language)
        except ImportError:
            return fallback_errors

    if not hasattr(locales, "_original_get_client_error"):
        locales._original_get_client_error = original
        locales.get_client_error = _patched_get_client_error


ensure_mysql_locale_support()
def get_db_connection(parent=None):
    """
    Creates and returns a MySQL connection using DB_CONFIG.
    Limits all error UI to a single place so other functions stay lean.
    """
    try:
        return mysql.connector.connect(**DB_CONFIG)
    except Error as exc:
        print(f"Database connection failed: {exc}")
        show_error(
            "Database Connection Error",
            "Could not connect to the configured MySQL database.\n"
            "Please verify DB_CONFIG credentials and that the MySQL server is reachable.",
            parent,
        )
        return None
def copy_image_to_library(source_path, prefix, parent=None):
    """
    Copies the selected image into PRODUCT_IMAGE_FOLDER with a sanitized filename.
    Returns the stored filename or None on failure.
    """
    if not source_path or not os.path.exists(source_path):
        return None
    try:
        os.makedirs(PRODUCT_IMAGE_FOLDER, exist_ok=True)
        _, ext = os.path.splitext(source_path)
        if not ext:
            ext = ".png"
        safe_prefix = re.sub(r"[^A-Za-z0-9_-]", "_", prefix or "img").strip("_")
        if safe_prefix:
            filename = f"{safe_prefix}{ext.lower()}"
        else:
            filename = f"img_{int(time.time())}{ext.lower()}"
        dest_path = os.path.join(PRODUCT_IMAGE_FOLDER, filename)
        shutil.copy2(source_path, dest_path)
        return filename
    except Exception as exc:
        show_error("Image Save Error", f"Unable to copy the selected image: {exc}", parent)
        return None


def ensure_product_code_column(conn):
    """
    Ensures the 'code' column exists on the products table for shorthand lookups.
    Attempts to add it automatically if it is missing.
    """
    global PRODUCT_CODE_COLUMN_AVAILABLE
    if PRODUCT_CODE_COLUMN_AVAILABLE is not None:
        return PRODUCT_CODE_COLUMN_AVAILABLE
    try:
        with conn.cursor() as cursor:
            cursor.execute("SHOW COLUMNS FROM products LIKE 'code'")
            exists = cursor.fetchone() is not None
    except Error:
        PRODUCT_CODE_COLUMN_AVAILABLE = False
        return False
    if exists:
        PRODUCT_CODE_COLUMN_AVAILABLE = True
        return True
    try:
        with conn.cursor() as cursor:
            cursor.execute("ALTER TABLE products ADD COLUMN code VARCHAR(64) NULL")
        conn.commit()
        print("Added missing 'code' column to products table.")
        PRODUCT_CODE_COLUMN_AVAILABLE = True
        return True
    except Error:
        try:
            conn.rollback()
        except Exception:
            pass
        PRODUCT_CODE_COLUMN_AVAILABLE = False
        return False
def ensure_promo_price_column(conn):
    """
    Ensures the product_promotions table has a promo_price column.
    Attempts to add it automatically if missing; falls back gracefully otherwise.
    """
    global PROMO_PRICE_COLUMN_AVAILABLE
    if PROMO_PRICE_COLUMN_AVAILABLE is not None:
        return PROMO_PRICE_COLUMN_AVAILABLE
    try:
        with conn.cursor() as cursor:
            cursor.execute("SHOW COLUMNS FROM product_promotions LIKE 'promo_price'")
            exists = cursor.fetchone() is not None
    except Error as exc:
        warn_missing_promo_price_support(exc)
        PROMO_PRICE_COLUMN_AVAILABLE = False
        return False
    if exists:
        PROMO_PRICE_COLUMN_AVAILABLE = True
        return True
    # Try to add the column so promo pricing matches the legacy behavior.
    try:
        with conn.cursor() as cursor:
            cursor.execute(
                "ALTER TABLE product_promotions "
                "ADD COLUMN promo_price DECIMAL(10,2) NULL"
            )
        conn.commit()
        print("Added missing 'promo_price' column to product_promotions table.")
        PROMO_PRICE_COLUMN_AVAILABLE = True
        return True
    except Error as exc:
        try:
            conn.rollback()
        except Exception:
            pass
        warn_missing_promo_price_support(exc)
        PROMO_PRICE_COLUMN_AVAILABLE = False
        return False
def warn_missing_promo_price_support(exc=None):
    """
    Logs a single warning explaining that promo-specific prices cannot be stored.
    """
    global PROMO_PRICE_WARNING_SHOWN
    if PROMO_PRICE_WARNING_SHOWN:
        return
    message = (
        "Warning: the 'product_promotions' table does not have a 'promo_price' column. "
        "Promo-specific prices will fall back to the base price. "
        "Add the column with "
        "\"ALTER TABLE product_promotions ADD COLUMN promo_price DECIMAL(10,2) NULL\" "
        "to enable full promo pricing support."
    )
    if exc:
        message += f" (Details: {exc})"
    print(message)
    PROMO_PRICE_WARNING_SHOWN = True
def ensure_bundle_image_column(conn):
    """
    Ensures the 'bundles' table has an image_filename column.
    """
    global BUNDLE_IMAGE_COLUMN_AVAILABLE
    if BUNDLE_IMAGE_COLUMN_AVAILABLE is not None:
        return BUNDLE_IMAGE_COLUMN_AVAILABLE
    try:
        with conn.cursor() as cursor:
            cursor.execute("SHOW COLUMNS FROM bundles LIKE 'image_filename'")
            exists = cursor.fetchone() is not None
    except Error:
        BUNDLE_IMAGE_COLUMN_AVAILABLE = False
        return False
    if exists:
        BUNDLE_IMAGE_COLUMN_AVAILABLE = True
        return True
    try:
        with conn.cursor() as cursor:
            cursor.execute("ALTER TABLE bundles ADD COLUMN image_filename VARCHAR(255) NULL")
        conn.commit()
        print("Added missing 'image_filename' column to bundles table.")
        BUNDLE_IMAGE_COLUMN_AVAILABLE = True
        return True
    except Error as exc:
        try:
            conn.rollback()
        except Exception:
            pass
        print(f"Warning: unable to add image_filename column to bundles table: {exc}")
        BUNDLE_IMAGE_COLUMN_AVAILABLE = False
        return False


def ensure_sales_reference_columns(conn):
    """
    Ensures the sales_transactions and sales_items tables include required tracking columns.
    """
    global SALES_REFERENCE_COLUMNS_READY
    if SALES_REFERENCE_COLUMNS_READY is True:
        return True
    try:
        with conn.cursor() as cursor:
            cursor.execute("SHOW COLUMNS FROM sales_transactions LIKE 'ref_no'")
            has_transactions_ref = cursor.fetchone() is not None
            cursor.execute("SHOW COLUMNS FROM sales_items LIKE 'ref_no'")
            has_items_ref = cursor.fetchone() is not None
            cursor.execute("SHOW COLUMNS FROM sales_transactions LIKE 'transaction_uuid'")
            has_transaction_uuid = cursor.fetchone() is not None
        if has_transactions_ref and has_items_ref and has_transaction_uuid:
            SALES_REFERENCE_COLUMNS_READY = True
            return True
        with conn.cursor() as cursor:
            if not has_transactions_ref:
                cursor.execute("ALTER TABLE sales_transactions ADD COLUMN ref_no VARCHAR(64) NULL")
            if not has_items_ref:
                cursor.execute("ALTER TABLE sales_items ADD COLUMN ref_no VARCHAR(64) NULL")
            if not has_transaction_uuid:
                cursor.execute("ALTER TABLE sales_transactions ADD COLUMN transaction_uuid VARCHAR(64) NULL")
        conn.commit()
        SALES_REFERENCE_COLUMNS_READY = True
        return True
    except Error as exc:
        try:
            conn.rollback()
        except Exception:
            pass
        print(f"Warning: unable to ensure sales reference columns exist: {exc}")
        SALES_REFERENCE_COLUMNS_READY = None
        return False


def normalize_product_code(value):
    """
    Standardize shorthand product codes for consistent storage and searching.
    """
    if value is None:
        return None
    code = str(value).strip()
    if not code:
        return None
    return code.upper()


def render_product_identifier(code, stock_no):
    """
    Combine the shorthand code and stock number into a single display token.
    """
    normalized_code = normalize_product_code(code)
    stock_text = str(stock_no or "").strip()
    if normalized_code and stock_text:
        return f"{normalized_code}-{stock_text}"
    return normalized_code or stock_text or ""


def sanitize_product_name(name, fallback=""):
    """
    Ensure display names never surface literal 'None' and optionally use a fallback.
    """
    text = ""
    if name is not None:
        text = str(name).strip()
    if text:
        return text
    if fallback is None:
        return ""
    return str(fallback).strip()


def has_xlsxwriter_support():
    """
    Returns True when the optional xlsxwriter dependency is installed.
    """
    try:
        import xlsxwriter  # noqa: F401
        return True
    except ModuleNotFoundError:
        return False


def assign_reference_to_sales(ref_no, parent=None, stock_numbers=None):
    """
    Tags unassigned sales records with the provided reference number.
    When stock_numbers is provided, only matching product stock numbers are updated.
    Returns (success, (transactions_updated, items_updated)).
    """
    ref_no = (ref_no or "").strip()
    if not ref_no:
        show_error("Missing Reference", "A reference number is required to tag sales records.", parent)
        return False, (0, 0)
    conn = get_db_connection(parent)
    if not conn:
        return False, (0, 0)
    stock_filters = []
    if stock_numbers:
        for value in stock_numbers:
            if value is None:
                continue
            text = str(value).strip()
            if text:
                stock_filters.append(text)
    try:
        if not ensure_sales_reference_columns(conn):
            return False, (0, 0)
        product_ids = []
        if stock_filters:
            placeholders = ", ".join(["%s"] * len(stock_filters))
            with conn.cursor(dictionary=True) as lookup_cursor:
                lookup_cursor.execute(
                    f"SELECT product_id, stock_no FROM products WHERE stock_no IN ({placeholders})",
                    stock_filters,
                )
                rows = lookup_cursor.fetchall()
            product_ids = [row["product_id"] for row in rows]
            if not product_ids:
                return True, (0, 0)
        with conn.cursor() as cursor:
            item_params = [ref_no]
            where_clauses = ["(ref_no IS NULL OR ref_no = '')"]
            if product_ids:
                product_placeholders = ", ".join(["%s"] * len(product_ids))
                where_clauses.append(f"product_id IN ({product_placeholders})")
                item_params.extend(product_ids)
            items_sql = f"""
                UPDATE sales_items
                   SET ref_no = %s
                 WHERE {' AND '.join(where_clauses)}
            """
            cursor.execute(items_sql, item_params)
            updated_items = cursor.rowcount or 0
            if product_ids:
                product_placeholders = ", ".join(["%s"] * len(product_ids))
                transaction_sql = f"""
                    UPDATE sales_transactions st
                       SET ref_no = %s
                     WHERE (st.ref_no IS NULL OR st.ref_no = '')
                       AND EXISTS (
                           SELECT 1
                             FROM sales_items si
                            WHERE si.transaction_id = st.transaction_id
                              AND si.product_id IN ({product_placeholders})
                       )
                """
                cursor.execute(transaction_sql, [ref_no, *product_ids])
            else:
                cursor.execute(
                    """
                    UPDATE sales_transactions st
                       SET ref_no = %s
                     WHERE (st.ref_no IS NULL OR st.ref_no = '')
                       AND NOT EXISTS (
                           SELECT 1
                             FROM sales_items si
                            WHERE si.transaction_id = st.transaction_id
                              AND (si.ref_no IS NULL OR si.ref_no = '')
                       )
                    """,
                    (ref_no,),
                )
            updated_transactions = cursor.rowcount or 0
        conn.commit()
        return True, (updated_transactions, updated_items)
    except Error as exc:
        try:
            conn.rollback()
        except Exception:
            pass
        show_error(
            "Database Error",
            f"Failed to tag sales records with reference '{ref_no}':\n{exc}",
            parent,
        )
        return False, (0, 0)
    finally:
        try:
            conn.close()
        except Exception:
            pass
def get_receipt_font_name():
    """
    Returns the registered font name to use for receipts.
    Prefers the bundled TT Interphases or MonospaceTypewriter font before falling back to Courier.
    """
    try:
        pdfmetrics.getFont(RECEIPT_FONT_NAME)
        return RECEIPT_FONT_NAME
    except KeyError:
        pass
    possible_paths = []
    if RECEIPT_FONT_FILE and os.path.exists(RECEIPT_FONT_FILE):
        possible_paths.append(RECEIPT_FONT_FILE)
    windows_dir = os.environ.get("WINDIR")
    if windows_dir:
        possible_paths.append(os.path.join(windows_dir, "Fonts", "MonospaceTypewriter.ttf"))
    for candidate in possible_paths:
        if not candidate or not os.path.exists(candidate):
            continue
        try:
            pdfmetrics.registerFont(TTFont(RECEIPT_FONT_NAME, candidate))
            return RECEIPT_FONT_NAME
        except Exception as exc:
            print(f"Warning: failed to register font from '{candidate}': {exc}")
    print("Warning: using Courier font as fallback for receipts.")
    return FALLBACK_RECEIPT_FONT_NAME
def compute_receipt_layout():
    """
    Calculates sizing details (font size, column widths, printable character capacity) for receipts.
    Ensures the item description column targets 32 characters and prices remain aligned while fitting within 58mm paper.
    """
    font_name = get_receipt_font_name()
    margin_points = RECEIPT_MARGIN_MM * mm
    printable_width = (RECEIPT_PAGE_WIDTH_MM * mm) - (2 * margin_points)
    printable_width = max(printable_width, RECEIPT_PAGE_WIDTH_MM * mm)
    desired_total = RECEIPT_LEFT_COLUMN_TARGET + RECEIPT_PRICE_COLUMN_WIDTH
    font_size = RECEIPT_BASE_FONT_SIZE
    def char_width(size):
        try:
            width = pdfmetrics.stringWidth("0", font_name, size)
        except Exception:
            width = pdfmetrics.stringWidth("0", FALLBACK_RECEIPT_FONT_NAME, size)
        return max(width, 0.1)
    width_per_char = char_width(font_size)
    max_chars = int(printable_width / width_per_char)
    while font_size > RECEIPT_MIN_FONT_SIZE and max_chars < desired_total:
        font_size -= 0.5
        width_per_char = char_width(font_size)
        max_chars = int(printable_width / width_per_char)
    max_chars = max(max_chars, 1)
    usable_chars = max(max_chars - 1, 1)  # keep a character worth of breathing room
    price_col_width = min(RECEIPT_PRICE_COLUMN_WIDTH, usable_chars)
    if usable_chars >= RECEIPT_LEFT_COLUMN_TARGET + price_col_width:
        left_col_width = RECEIPT_LEFT_COLUMN_TARGET
    else:
        left_col_width = max(usable_chars - price_col_width, 0)
    total_width = left_col_width + price_col_width
    if total_width > usable_chars:
        overflow = total_width - usable_chars
        if left_col_width >= overflow:
            left_col_width -= overflow
        else:
            price_col_width = max(price_col_width - overflow, 0)
            left_col_width = max(left_col_width, 0)
        total_width = left_col_width + price_col_width
    return {
        "font_name": font_name,
        "font_size": font_size,
        "total_width": max(total_width, 1),
        "left_width": max(left_col_width, 0),
        "price_width": max(price_col_width, 0),
        "max_chars": max_chars,
        "printable_width": printable_width,
        "line_spacing": RECEIPT_LINE_SPACING_MULTIPLIER,
        "bold_offset": RECEIPT_BOLD_OFFSET_PT,
        "booth_header_prefix": RECEIPT_BOOTH_PREFIX,
        "booth_header_size": max(font_size + RECEIPT_BOOTH_SIZE_INCREMENT, 1.0),
}
def build_eye_icon(is_visible, size=22):
    """
    Creates a minimalist eye icon pixmap used for password toggle buttons.
    """
    pixmap = QPixmap(size, size)
    pixmap.fill(Qt.GlobalColor.transparent)
    painter = QPainter(pixmap)
    painter.setRenderHint(QPainter.RenderHint.Antialiasing)
    pen = QPen(QColor("#5c627a"), 1.6)
    painter.setPen(pen)
    painter.setBrush(Qt.BrushStyle.NoBrush)
    outline_rect = QRectF(4, 6, size - 8, size - 12)
    painter.drawEllipse(outline_rect)
    inner_rect = QRectF(outline_rect.center().x() - 4, outline_rect.center().y() - 2, 8, 8)
    painter.drawEllipse(inner_rect)
    if not is_visible:
        painter.drawLine(QPointF(5, 5), QPointF(size - 5, size - 5))
    painter.end()
    return QIcon(pixmap)
def _draw_bold_text(canvas_obj, x_pos, y_pos, text, font_name, font_size, offset_pt):
    """Draws text with a slight horizontal offset to simulate a bolder stroke."""
    if not text:
        return
    canvas_obj.setFont(font_name, font_size)
    canvas_obj.drawString(x_pos, y_pos, text)
    if offset_pt > 0:
        canvas_obj.drawString(x_pos + offset_pt, y_pos, text)
def load_ui_preferences():
    """Loads UI preferences such as theme selection from disk."""
    global current_theme_preference
    theme = "system"
    try:
        with open(UI_PREFERENCES_FILE, 'r', encoding='utf-8') as f:
            data = json.load(f)
            requested = data.get("theme", "system")
            if requested not in {"system", "light", "dark"}:
                requested = "system"
            if requested != "system":
                # Always reset persisted preference to system so future launches follow the OS theme.
                save_ui_preferences("system")
                requested = "system"
            theme = requested
    except FileNotFoundError:
        pass
    except Exception as exc:
        print(f"Warning: failed to load UI preferences: {exc}")
    current_theme_preference = theme
    return theme
def save_ui_preferences(theme):
    """Persists UI preferences such as theme selection to disk.

    Persisted value is always 'system' so the app follows the OS theme on launch.
    """
    try:
        with open(UI_PREFERENCES_FILE, 'w', encoding='utf-8') as f:
            json.dump({"theme": "system"}, f, ensure_ascii=False, indent=4)
    except Exception as exc:
        print(f"Warning: failed to save UI preferences: {exc}")
def detect_system_theme():
    """Returns 'light' or 'dark' based on the OS-level color scheme when available."""
    app = QApplication.instance()
    if not app:
        return "light"
    hints = app.styleHints()
    if hasattr(hints, "colorScheme"):
        scheme = hints.colorScheme()
        if scheme == Qt.ColorScheme.Dark:
            return "dark"
        if scheme == Qt.ColorScheme.Light:
            return "light"
    return "light"
def apply_light_theme(app):
    """Applies a light color palette and resets any global stylesheet overrides."""
    if app is None:
        return
    app.setStyle("Fusion")
    palette = QPalette()
    palette.setColor(QPalette.ColorRole.Window, QColor("#ffffff"))
    palette.setColor(QPalette.ColorRole.WindowText, QColor("#111827"))
    palette.setColor(QPalette.ColorRole.Base, QColor("#ffffff"))
    palette.setColor(QPalette.ColorRole.AlternateBase, QColor("#f3f4f6"))
    palette.setColor(QPalette.ColorRole.Text, QColor("#111827"))
    palette.setColor(QPalette.ColorRole.Button, QColor("#ffffff"))
    palette.setColor(QPalette.ColorRole.ButtonText, QColor("#111827"))
    palette.setColor(QPalette.ColorRole.Highlight, QColor("#2563eb"))
    palette.setColor(QPalette.ColorRole.HighlightedText, QColor("#ffffff"))
    palette.setColor(QPalette.ColorRole.ToolTipBase, QColor("#111827"))
    palette.setColor(QPalette.ColorRole.ToolTipText, QColor("#f9fafb"))
    app.setPalette(palette)
    app.setStyleSheet("")
def apply_dark_theme(app):
    """Applies a dark color palette alongside a high-contrast global stylesheet."""
    if app is None:
        return
    app.setStyle("Fusion")
    palette = QPalette()
    palette.setColor(QPalette.ColorRole.Window, QColor("#0f172a"))
    palette.setColor(QPalette.ColorRole.WindowText, QColor("#f8fafc"))
    palette.setColor(QPalette.ColorRole.Base, QColor("#111827"))
    palette.setColor(QPalette.ColorRole.AlternateBase, QColor("#1e293b"))
    palette.setColor(QPalette.ColorRole.Text, QColor("#f8fafc"))
    palette.setColor(QPalette.ColorRole.Button, QColor("#1e293b"))
    palette.setColor(QPalette.ColorRole.ButtonText, QColor("#f8fafc"))
    palette.setColor(QPalette.ColorRole.Highlight, QColor("#2563eb"))
    palette.setColor(QPalette.ColorRole.HighlightedText, QColor("#f8fafc"))
    palette.setColor(QPalette.ColorRole.ToolTipBase, QColor("#f8fafc"))
    palette.setColor(QPalette.ColorRole.ToolTipText, QColor("#0f172a"))
    app.setPalette(palette)
    app.setStyleSheet("""
        QWidget { background-color: #0f172a; color: #f8fafc; }
        QPushButton { background-color: #1e293b; color: #f8fafc; border: 1px solid #334155; }
        QPushButton:hover { background-color: #2563eb; color: #ffffff; }
        QLineEdit, QPlainTextEdit, QTextEdit, QComboBox, QListWidget, QTableWidget, QTableView {
            background-color: #111827;
            color: #f8fafc;
            border: 1px solid #334155;
            selection-background-color: #2563eb;
            selection-color: #f8fafc;
        }
        QHeaderView::section {
            background-color: #1e293b;
            color: #f8fafc;
        }
    """)
def apply_theme(app, mode):
    """
    Applies the requested theme ('light', 'dark', or 'system') to the given QApplication.
    Returns the effective theme that was applied.
    """
    global current_theme_preference, current_theme_effective
    if not mode:
        mode = "system"
    current_theme_preference = mode
    effective = mode
    if mode == "system":
        effective = detect_system_theme()
    if effective == "dark":
        apply_dark_theme(app)
    else:
        effective = "light"
        apply_light_theme(app)
    current_theme_effective = effective
    return effective
def get_theme_tokens(effective_theme=None):
    """
    Returns a dictionary of commonly used colors for the provided theme.
    """
    theme = (effective_theme or current_theme_effective or "light").lower()
    if theme == "dark":
        return {
            "background": "#0f172a",
            "card_bg": "#111827",
            "card_border": "#1f2937",
            "title": "#f8fafc",
            "subtitle": "#94a3b8",
            "text": "#e2e8f0",
            "muted": "#94a3b8",
            "input_bg": "#1e293b",
            "input_border": "#334155",
            "input_text": "#f8fafc",
            "button_primary_bg": "#2563eb",
            "button_primary_text": "#ffffff",
            "button_primary_hover": "#1d4ed8",
            "button_primary_pressed": "#1e40af",
            "button_outline_text": "#cbd5f5",
            "button_outline_border": "#4c5a85",
            "button_outline_hover_bg": "#1e293b",
            "button_outline_hover_border": "#6180ff",
            "toggle_bg": "#1e293b",
            "toggle_hover": "#334155",
            "table_header_bg": "#1f2937",
            "table_header_text": "#f8fafc",
            "table_row_bg": "#111827",
            "table_row_alt_bg": "#182032",
            "table_text": "#e2e8f0",
        }
    return {
        "background": "#f5f7fb",
        "card_bg": "#ffffff",
        "card_border": "#e2e6f0",
        "title": "#1f2a44",
        "subtitle": "#6b7390",
        "text": "#1f2937",
        "muted": "#6b7390",
        "input_bg": "#ffffff",
        "input_border": "#ced3e3",
        "input_text": "#1f2937",
        "button_primary_bg": "#5c7cfa",
        "button_primary_text": "#ffffff",
        "button_primary_hover": "#4b6ae0",
        "button_primary_pressed": "#3f5bc4",
        "button_outline_text": "#4b5ecf",
        "button_outline_border": "#c3c9e8",
        "button_outline_hover_bg": "#eef1ff",
        "button_outline_hover_border": "#5c7cfa",
        "toggle_bg": "#eef1fb",
        "toggle_hover": "#e1e6fb",
        "table_header_bg": "#f0f3fb",
        "table_header_text": "#47506a",
        "table_row_bg": "#ffffff",
        "table_row_alt_bg": "#f7f8fc",
        "table_text": "#1f2937",
    }
def render_receipt_text(canvas_obj, receipt_text, layout, start_x, start_y):
    """
    Renders wrapped receipt text on the supplied canvas using the computed layout.
    Returns the final Y position after rendering.
    """
    font_name = layout["font_name"]
    base_font_size = layout["font_size"]
    max_chars_per_line = max(int(layout["total_width"]), 1)
    bold_offset = layout.get("bold_offset", RECEIPT_BOLD_OFFSET_PT)
    printable_width = layout.get("printable_width", 0)
    current_y = start_y
    line_spacing = layout.get("line_spacing", RECEIPT_LINE_SPACING_MULTIPLIER)
    size_tag_pattern = RECEIPT_SIZE_TAG_PATTERN
    booth_prefix = layout.get("booth_header_prefix")
    booth_size = layout.get("booth_header_size")
    booth_applied = False
    for line in receipt_text.split("\n"):
        is_booth_line = False
        line_font_size = base_font_size
        match = size_tag_pattern.match(line)
        if match:
            try:
                line_font_size = float(match.group(1))
            except ValueError:
                line_font_size = base_font_size
            line = line[match.end():]
        elif booth_prefix and booth_size and not booth_applied:
            if line.strip().startswith(booth_prefix):
                line_font_size = booth_size
                booth_applied = True
                is_booth_line = True
        current_line_height = line_font_size * line_spacing
        if line:
            if is_booth_line and printable_width:
                text_to_draw = line.strip()
                try:
                    text_width = pdfmetrics.stringWidth(text_to_draw, font_name, line_font_size)
                except Exception:
                    text_width = pdfmetrics.stringWidth(text_to_draw, FALLBACK_RECEIPT_FONT_NAME, line_font_size)
                text_x = start_x + max((printable_width - text_width) / 2, 0)
                _draw_bold_text(canvas_obj, text_x, current_y, text_to_draw, font_name, line_font_size, bold_offset)
                current_y -= current_line_height
            else:
                remaining = line
                while remaining:
                    segment = remaining[:max_chars_per_line]
                    _draw_bold_text(canvas_obj, start_x, current_y, segment, font_name, line_font_size, bold_offset)
                    remaining = remaining[max_chars_per_line:]
                    current_y -= current_line_height
        else:
            current_y -= current_line_height
    return current_y


def load_admin_password():
    if os.path.exists(ADMIN_PASSWORD_FILE):
        try:
            with open(ADMIN_PASSWORD_FILE, "r", encoding="utf-8") as f:
                password = f.read().strip()
                if password:
                    return password
        except Exception as e:
            print(f"Warning: unable to read admin password file: {e}")
    # If file missing or empty or error, write default password
    try:
        with open(ADMIN_PASSWORD_FILE, "w", encoding="utf-8") as f:
            f.write(DEFAULT_ADMIN_PASSWORD)
    except Exception as e:
        print(f"Warning: unable to write default admin password file: {e}")
    return DEFAULT_ADMIN_PASSWORD
def save_admin_password(new_password):
    try:
        with open(ADMIN_PASSWORD_FILE, "w", encoding="utf-8") as f:
            f.write(new_password)
        return True
    except Exception as e:
        print(f"Error saving admin password: {e}")
        return False
def load_activity_logs():
    """Return all recorded activity log entries from disk."""
    if not os.path.exists(ACTIVITY_LOG_FILE):
        return []
    entries = []
    try:
        with open(ACTIVITY_LOG_FILE, "r", encoding="utf-8") as f:
            for line in f:
                record = line.strip()
                if not record:
                    continue
                try:
                    entries.append(json.loads(record))
                except ValueError as exc:
                    print(f"Warning: skipping malformed activity log entry: {exc}")
    except Exception as exc:
        print(f"Warning: unable to load activity logs: {exc}")
    return entries
def append_activity_log_entry(entry):
    """Append a single activity log entry to the log file."""
    try:
        directory = os.path.dirname(ACTIVITY_LOG_FILE)
        if directory and not os.path.exists(directory):
            os.makedirs(directory, exist_ok=True)
        with open(ACTIVITY_LOG_FILE, "a", encoding="utf-8") as f:
            f.write(json.dumps(entry) + "\n")
    except Exception as exc:
        print(f"Warning: unable to append activity log entry: {exc}")
# Load admin password at runtime
ADMIN_PASSWORD = load_admin_password()
# ================== Utility MessageBox Helpers ===================
def show_error(title, message, parent=None):
    msg = QMessageBox(parent)
    msg.setIcon(QMessageBox.Icon.Critical)
    msg.setWindowTitle(title)
    msg.setText(message)
    msg.exec()
def show_warning(title, message, parent=None):
    msg = QMessageBox(parent)
    msg.setIcon(QMessageBox.Icon.Warning)
    msg.setWindowTitle(title)
    msg.setText(message)
    msg.exec()
def show_info(title, message, parent=None):
    msg = QMessageBox(parent)
    msg.setIcon(QMessageBox.Icon.Information)
    msg.setWindowTitle(title)
    msg.setText(message)
    msg.exec()


def promo_quantity_multiplier(promo_code):
    """Return the quantity multiplier for common promo patterns such as B1T1."""
    if not promo_code:
        return 1
    code = str(promo_code).upper()
    if "B1T1" in code:
        return 2
    if "B3T1" in code:
        return 4
    return 1
def ensure_api_settings_loaded(parent=None):
    """
    Loads the API settings from disk, creating a template if missing.
    """
    global api_settings
    if api_settings is not None:
        return True
    if not os.path.exists(API_SETTINGS_FILE):
        try:
            with open(API_SETTINGS_FILE, "w", encoding="utf-8") as f:
                json.dump(DEFAULT_API_SETTINGS, f, indent=2)
        except Exception as exc:
            show_error("API Settings Error", f"Failed to create default API settings file:\n{exc}", parent)
            return False
        show_warning(
            "API Settings Missing",
            "Created api_settings.json with placeholder values. Update the file with valid credentials and retry.",
            parent,
        )
        return False
    try:
        with open(API_SETTINGS_FILE, "r", encoding="utf-8") as f:
            loaded = json.load(f)
    except Exception as exc:
        show_error("API Settings Error", f"Failed to read api_settings.json:\n{exc}", parent)
        return False
    if not isinstance(loaded, dict):
        show_error("API Settings Error", "api_settings.json must contain a JSON object.", parent)
        return False
    settings = DEFAULT_API_SETTINGS.copy()
    settings.update(loaded)
    settings["base_url"] = str(settings.get("base_url") or "").strip().rstrip("/")
    if not settings["base_url"]:
        show_error("API Settings Error", "The base_url in api_settings.json is required.", parent)
        return False
    try:
        settings["warehouse_id"] = int(settings.get("warehouse_id"))
    except (TypeError, ValueError):
        show_error("API Settings Error", "warehouse_id must be an integer.", parent)
        return False
    try:
        settings["customer_id"] = int(settings.get("customer_id"))
    except (TypeError, ValueError):
        show_error("API Settings Error", "customer_id must be an integer.", parent)
        return False
    if settings["customer_id"] <= 0:
        show_error("API Settings Error", "customer_id must be greater than zero.", parent)
        return False
    identity = str(settings.get("login_identity") or "").strip()
    password = str(settings.get("login_password") or "").strip()
    if not identity or not password:
        show_error("API Settings Error", "login_identity and login_password are required.", parent)
        return False
    try:
        ttl = int(settings.get("token_ttl_seconds") or DEFAULT_API_SETTINGS["token_ttl_seconds"])
        settings["token_ttl_seconds"] = max(60, ttl)
    except (TypeError, ValueError):
        settings["token_ttl_seconds"] = DEFAULT_API_SETTINGS["token_ttl_seconds"]
    try:
        timeout = float(settings.get("request_timeout_seconds") or DEFAULT_API_SETTINGS["request_timeout_seconds"])
        settings["request_timeout_seconds"] = max(5.0, timeout)
    except (TypeError, ValueError):
        settings["request_timeout_seconds"] = DEFAULT_API_SETTINGS["request_timeout_seconds"]
    settings["include_zero"] = bool(settings.get("include_zero"))
    settings["force_new_token_on_login"] = bool(settings.get("force_new_token_on_login"))
    settings["include_unit_price"] = bool(settings.get("include_unit_price"))
    settings["clear_sales_summary_after_post"] = bool(settings.get("clear_sales_summary_after_post"))
    settings["use_inventory_stub"] = bool(settings.get("use_inventory_stub"))
    settings["inventory_stub_file"] = str(settings.get("inventory_stub_file") or "").strip()
    settings["use_sales_stub"] = bool(settings.get("use_sales_stub"))
    settings["sales_stub_file"] = str(settings.get("sales_stub_file") or "").strip()
    api_settings = settings
    return True
def build_api_url(*segments):
    if not ensure_api_settings_loaded():
        return ""
    base = api_settings.get("base_url", "").rstrip("/")
    path_segments = [str(seg).strip("/") for seg in segments if seg not in (None, "", False)]
    if path_segments:
        return f"{base}/{'/'.join(path_segments)}"
    return base
def load_api_token_cache():
    global api_token_cache
    if api_token_cache is not None:
        return api_token_cache
    if not os.path.exists(API_TOKEN_CACHE_FILE):
        return None
    try:
        with open(API_TOKEN_CACHE_FILE, "r", encoding="utf-8") as f:
            api_token_cache = json.load(f)
    except Exception:
        api_token_cache = None
    return api_token_cache
def save_api_token_cache(data):
    global api_token_cache
    api_token_cache = data
    try:
        with open(API_TOKEN_CACHE_FILE, "w", encoding="utf-8") as f:
            json.dump(data, f, indent=2)
    except Exception as exc:
        print(f"Warning: failed to persist API token cache: {exc}")
def clear_api_token_cache():
    global api_token_cache
    api_token_cache = None
    try:
        if os.path.exists(API_TOKEN_CACHE_FILE):
            os.remove(API_TOKEN_CACHE_FILE)
    except Exception as exc:
        print(f"Warning: failed to clear API token cache: {exc}")
def parse_api_expiry(value):
    if not value:
        return None
    if isinstance(value, (int, float)):
        try:
            return datetime.fromtimestamp(value)
        except Exception:
            return None
    if isinstance(value, str):
        for fmt in ("%Y-%m-%d %H:%M:%S", "%Y-%m-%dT%H:%M:%S", "%Y-%m-%dT%H:%M:%S%z"):
            try:
                return datetime.strptime(value, fmt)
            except ValueError:
                continue
        try:
            return datetime.fromisoformat(value)
        except ValueError:
            return None
    return None
def is_cached_token_valid(cache):
    if not cache or "token" not in cache:
        return False
    if not ensure_api_settings_loaded():
        return False
    if cache.get("identity") != api_settings.get("login_identity"):
        return False
    if cache.get("base_url") != api_settings.get("base_url"):
        return False
    expires_at = parse_api_expiry(cache.get("expires_at"))
    if not expires_at:
        return False
    if expires_at.tzinfo is not None:
        expires_at = expires_at.astimezone().replace(tzinfo=None)
    return expires_at > datetime.now() + timedelta(minutes=1)
def get_api_token(parent=None, force_refresh=False):
    if not ensure_api_settings_loaded(parent):
        return None
    if not force_refresh:
        cache = load_api_token_cache()
        if is_cached_token_valid(cache):
            return cache["token"]
    login_url = build_api_url("auth", "login")
    if not login_url:
        return None
    payload = {
        "identity": api_settings["login_identity"],
        "password": api_settings["login_password"],
        "ttlSeconds": api_settings["token_ttl_seconds"],
        "forceNewToken": api_settings["force_new_token_on_login"],
    }
    try:
        response = requests.post(
            login_url,
            json=payload,
            timeout=api_settings.get("request_timeout_seconds", DEFAULT_API_SETTINGS["request_timeout_seconds"]),
        )
    except requests.exceptions.RequestException as exc:
        show_error("Login Failed", f"Login request failed:\n{exc}", parent)
        return None
    if response.status_code != 200:
        show_error("Login Failed", f"API returned {response.status_code} during login:\n{response.text}", parent)
        return None
    try:
        body = response.json()
    except ValueError as exc:
        show_error("Login Failed", f"Invalid JSON received from login endpoint:\n{exc}", parent)
        return None
    data = (body or {}).get("data") or {}
    token = data.get("token") or body.get("token")
    expires_at = data.get("expiresAt") or data.get("expires_at")
    if not token:
        show_error("Login Failed", "Login response did not include an access token.", parent)
        return None
    cache_payload = {
        "token": token,
        "expires_at": expires_at,
        "identity": api_settings["login_identity"],
        "base_url": api_settings["base_url"],
    }
    save_api_token_cache(cache_payload)
    return token
def api_request(method, *segments, parent=None, params=None, json_payload=None, force_refresh=False):
    if not ensure_api_settings_loaded(parent):
        return None
    token = get_api_token(parent=parent, force_refresh=force_refresh)
    if not token:
        return None
    url = build_api_url(*segments)
    headers = {
        "Authorization": f"Bearer {token}",
        "Accept": "application/json",
    }
    if method.upper() in {"POST", "PUT", "PATCH"}:
        headers["Content-Type"] = "application/json"
    try:
        response = requests.request(
            method=method,
            url=url,
            headers=headers,
            params=params,
            json=json_payload,
            timeout=api_settings.get("request_timeout_seconds", DEFAULT_API_SETTINGS["request_timeout_seconds"]),
        )
    except requests.exceptions.RequestException as exc:
        show_error("API Request Failed", f"Request to {url} failed:\n{exc}", parent)
        return None
    if response.status_code == 401 and not force_refresh:
        clear_api_token_cache()
        return api_request(
            method,
            *segments,
            parent=parent,
            params=params,
            json_payload=json_payload,
            force_refresh=True,
        )
    return response
def load_inventory_stub_payload(parent=None):
    if not ensure_api_settings_loaded(parent):
        return None
    file_path = api_settings.get("inventory_stub_file") or "inventory_stub.json"
    if not ensure_inventory_stub_file(file_path, parent):
        return {}
    candidate = os.path.abspath(file_path)
    try:
        with open(candidate, "r", encoding="utf-8") as f:
            data = json.load(f)
            if isinstance(data, dict):
                return data
        show_warning("Inventory Stub", f"Inventory stub file '{candidate}' does not contain a JSON object.", parent)
    except Exception as exc:
        show_warning("Inventory Stub", f"Failed to read inventory stub file '{candidate}':\n{exc}", parent)
    return {}
def ensure_sales_invoice_stub_file(file_path, parent=None):
    """
    Validates that the configured sales stub file exists on disk.
    """
    candidate = os.path.abspath(file_path)
    if os.path.exists(candidate):
        return True
    show_warning("Sales Stub", f"Sales stub file '{candidate}' was not found.", parent)
    return False
def load_sales_invoice_stub_response(parent=None):
    if not ensure_api_settings_loaded(parent):
        return None
    file_path = api_settings.get("sales_stub_file") or "sales_invoice_stub.json"
    if not ensure_sales_invoice_stub_file(file_path, parent):
        return {}
    candidate = os.path.abspath(file_path)
    try:
        with open(candidate, "r", encoding="utf-8") as fh:
            data = json.load(fh)
            if isinstance(data, dict):
                return data
            show_warning("Sales Stub", f"Sales stub file '{candidate}' does not contain a JSON object.", parent)
    except Exception as exc:
        show_warning("Sales Stub", f"Failed to read sales stub file '{candidate}':\n{exc}", parent)
    return {}


class BarcodeScannerWorker(QThread):
    """
    Background worker that listens to the first available serial port for barcode/QR scans.
    """

    barcode_scanned = pyqtSignal(str)
    status_changed = pyqtSignal(str)

    def __init__(self, baudrate=9600, poll_interval=1.0, read_timeout=0.1, parent=None):
        super().__init__(parent)
        self.baudrate = baudrate
        self.poll_interval = poll_interval
        self.read_timeout = read_timeout
        self._serial = None
        self._current_port = None
        self._buffer = ""
        self._running = False

    def run(self):
        if serial is None or list_ports is None:
            self.status_changed.emit("pyserial not installed")
            return
        self._running = True
        self.status_changed.emit("Waiting for scanner…")
        while self._running:
            if self._serial is None:
                self._open_available_port()
                time.sleep(self.poll_interval)
                continue
            try:
                data = self._serial.read(64)
                if data:
                    try:
                        decoded = data.decode("utf-8", errors="ignore")
                    except Exception:
                        decoded = "".join(chr(b) for b in data if 32 <= b <= 126)
                    if decoded:
                        self._buffer += decoded
                        while True:
                            separator_index = None
                            separator_length = 0
                            for separator in ("\r\n", "\n", "\r"):
                                idx = self._buffer.find(separator)
                                if idx != -1:
                                    separator_index = idx
                                    separator_length = len(separator)
                                    break
                            if separator_index is None:
                                break
                            chunk = self._buffer[:separator_index].strip()
                            self._buffer = self._buffer[separator_index + separator_length :]
                            if chunk:
                                self.barcode_scanned.emit(chunk)
                    else:
                        time.sleep(0.05)
                else:
                    time.sleep(0.05)
            except (serial.SerialException, OSError):
                self.status_changed.emit("Scanner disconnected")
                self._close_port()
                time.sleep(self.poll_interval)
        self._close_port()
        self.status_changed.emit("Scanner stopped")

    def stop(self):
        self._running = False
        if self.isRunning():
            self.wait()
        else:
            self._close_port()

    def _open_available_port(self):
        if not self._running:
            return
        ports = list(list_ports.comports())
        usb_ports = [info for info in ports if self._is_usb_port(info)]
        if not usb_ports:
            self.status_changed.emit("Waiting for USB scanner…")
            return
        for port_info in usb_ports:
            if not self._running:
                return
            try:
                ser = serial.Serial(port_info.device, baudrate=self.baudrate, timeout=self.read_timeout)
            except (serial.SerialException, OSError):
                continue
            self._serial = ser
            self._current_port = port_info.device
            self._buffer = ""
            description = port_info.description or self._current_port
            self.status_changed.emit(f"Connected ({description})")
            return
        self.status_changed.emit("USB scanner busy/unavailable")

    def _close_port(self):
        if self._serial:
            try:
                self._serial.close()
            except Exception:
                pass
            self._serial = None
        self._current_port = None

    @staticmethod
    def _is_usb_port(port_info):
        if port_info is None:
            return False
        hwid = getattr(port_info, "hwid", "") or ""
        description = getattr(port_info, "description", "") or ""
        device = getattr(port_info, "device", "") or ""
        combined = " ".join([hwid, description, device]).upper()
        return "USB" in combined

def fetch_inventory_payload(parent=None):
    if not ensure_api_settings_loaded(parent):
        return None
    if api_settings.get("use_inventory_stub"):
        return load_inventory_stub_payload(parent)
    params = {"includeZero": 1 if api_settings.get("include_zero") else 0}
    response = api_request("GET", "inventory", api_settings["warehouse_id"], parent=parent, params=params)
    if response is None:
        return None
    if response.status_code != 200:
        try:
            error_body = response.json()
        except ValueError:
            error_body = response.text
        show_error("Inventory Sync Failed", f"API returned {response.status_code}:\n{error_body}", parent)
        return None
    try:
        payload = response.json()
    except ValueError as exc:
        show_error("Inventory Sync Failed", f"Unable to decode response JSON:\n{exc}", parent)
        return None
    if not isinstance(payload, dict):
        show_error("Inventory Sync Failed", "Unexpected response format from API.", parent)
        return None
    return payload
# --- Product Persistence ---
def load_products_from_database(parent=None):
    """
    Legacy entry point kept for compatibility with the original code.
    Now loads the complete product catalog (including promo pricing) from MySQL.
    """
    global products, sales_summary, product_promo_columns
    products = {}
    sales_summary = {}
    product_promo_columns = []
    conn = get_db_connection(parent)
    if not conn:
        return False
    try:
        supports_product_codes = ensure_product_code_column(conn)
        supports_promo_prices = ensure_promo_price_column(conn)
        with conn.cursor(dictionary=True) as cursor:
            select_columns = "product_id, stock_no, name, price, stock, image_filename"
            if supports_product_codes:
                select_columns += ", code"
            cursor.execute(
                f"""
                SELECT {select_columns}
                FROM products
                ORDER BY stock_no, product_id
                """
            )
            product_rows = cursor.fetchall()
            if not product_rows:
                show_warning(
                    "No Products Found",
                    "No products were found in the database. Please populate the 'products' table.",
                    parent,
                )
                return False
            if supports_promo_prices:
                cursor.execute(
                    """
                    SELECT product_id, promo_code, promo_price
                    FROM product_promotions
                    """
                )
            else:
                cursor.execute(
                    """
                    SELECT product_id, promo_code
                    FROM product_promotions
                    """
                )
            promo_rows = cursor.fetchall()
        promos_by_product = {}
        unique_promo_codes = []
        for promo in promo_rows:
            pid = promo["product_id"]
            promo_code = promo["promo_code"]
            promo_price = promo.get("promo_price") if supports_promo_prices else None
            promos_by_product.setdefault(pid, {})[promo_code] = (
                float(promo_price) if promo_price is not None else None
            )
            if promo_code not in unique_promo_codes:
                unique_promo_codes.append(promo_code)
        product_promo_columns = unique_promo_codes
        for row in product_rows:
            barcode = row["stock_no"]
            raw_promos = promos_by_product.get(row["product_id"], {})
            normalized_promos = {}
            for code, price in raw_promos.items():
                if price is None:
                    normalized_promos[code] = float(row["price"])
                else:
                    normalized_promos[code] = float(price)
            variant_entry = {
                "name": row["name"],
                "price": float(row["price"]),
                "stock": int(row["stock"]),
                "original_stock": int(row["stock"]),
                "image_filename": resolve_product_image_filename(barcode, row.get("image_filename")),
                "code": normalize_product_code(row.get("code")) if supports_product_codes else None,
                "promos": normalized_promos,
                "_product_id": row["product_id"],
            }
            products.setdefault(barcode, []).append(variant_entry)
            sales_summary.setdefault(barcode, {"qty_sold": 0, "revenue": 0.0})
        return True
    except Error as exc:
        show_error("Database Error", f"Failed to load products: {exc}", parent)
        return False
    finally:
        try:
            conn.close()
        except Exception:
            pass
def load_promo_inventory(parent=None):
    """
    Loads the promo inventory mapping from the database.
    """
    global promo_inventory_map
    promo_inventory_map = {}
    conn = get_db_connection(parent)
    if not conn:
        return False
    try:
        with conn.cursor(dictionary=True) as cursor:
            cursor.execute("SELECT promo_code, units_per_sale FROM promo_types")
            rows = cursor.fetchall()
            for row in rows:
                promo_inventory_map[row["promo_code"]] = row["units_per_sale"]
        return True
    except Error as exc:
        show_error("Database Error", f"Failed to load promo inventory: {exc}", parent)
        return False
    finally:
        try:
            conn.close()
        except Exception:
            pass
def load_bundle_promos(parent=None):
    """
    Loads saved bundle promo definitions that map a bundle code to component products and price.
    """
    global bundle_promos
    bundle_promos = {}
    conn = get_db_connection(parent)
    if not conn:
        return False
    try:
        supports_images = ensure_bundle_image_column(conn)
        with conn.cursor(dictionary=True) as cursor:
            select_cols = "bundle_id, bundle_code, name, price, sku"
            if supports_images:
                select_cols += ", image_filename"
            cursor.execute(f"SELECT {select_cols} FROM bundles")
            bundles = cursor.fetchall()
            if not bundles:
                return True
            for bundle in bundles:
                code = bundle["bundle_code"]
                bundle_promos[code] = {
                    "code": code,
                    "name": bundle["name"],
                    "price": float(bundle["price"]),
                    "sku": bundle.get("sku"),
                    "components": [],
                    "image_filename": resolve_product_image_filename(
                        bundle.get("sku"), bundle.get("image_filename")
                    ) if supports_images else "",
                }
                cursor.execute(
                    """
                    SELECT product_stock_no, variant_index, quantity
                    FROM bundle_components
                    WHERE bundle_id = %s
                    """,
                    (bundle["bundle_id"],),
                )
                components = cursor.fetchall()
                for comp in components:
                    bundle_promos[code]["components"].append(
                        {
                            "barcode": comp["product_stock_no"],
                            "variant_index": int(comp["variant_index"]),
                            "quantity": int(comp["quantity"]),
                        }
                    )
        return True
    except Error as exc:
        show_error("Database Error", f"Failed to load bundle promos: {exc}", parent)
        return False
    finally:
        try:
            conn.close()
        except Exception:
            pass
def save_bundle_promos(parent=None):
    """
    Persists bundle promo definitions to disk.
    """
    conn = get_db_connection(parent)
    if not conn:
        return False
    try:
        supports_images = ensure_bundle_image_column(conn)
        with conn.cursor() as cursor:
            cursor.execute("DELETE FROM bundle_components")
            cursor.execute("DELETE FROM bundles")
            if supports_images:
                insert_bundle = """
                    INSERT INTO bundles (bundle_code, name, price, sku, image_filename)
                    VALUES (%s, %s, %s, %s, %s)
                """
            else:
                insert_bundle = """
                    INSERT INTO bundles (bundle_code, name, price, sku)
                    VALUES (%s, %s, %s, %s)
                """
            insert_component = """
                INSERT INTO bundle_components (bundle_id, product_stock_no, variant_index, quantity)
                VALUES (%s, %s, %s, %s)
            """
            for code, bundle in bundle_promos.items():
                bundle_args = (
                    code,
                    bundle.get("name"),
                    float(bundle.get("price", 0)),
                    bundle.get("sku"),
                )
                if supports_images:
                    bundle_args = bundle_args + (bundle.get("image_filename"),)
                cursor.execute(insert_bundle, bundle_args)
                bundle_id = cursor.lastrowid
                for comp in bundle.get("components", []):
                    cursor.execute(
                        insert_component,
                        (
                            bundle_id,
                            comp.get("barcode"),
                            int(comp.get("variant_index", 0)),
                            int(comp.get("quantity", 1)),
                        ),
                    )
        conn.commit()
        return True
    except Error as exc:
        conn.rollback()
        show_error("Save Error", f"Failed to save bundle promos: {exc}", parent)
        return False
    finally:
        try:
            conn.close()
        except Exception:
            pass
def save_basket_promos(parent=None):
    """
    Persists basket-size promo tiers to the database.
    """
    conn = get_db_connection(parent)
    if not conn:
        return False
    try:
        with conn.cursor() as cursor:
            cursor.execute("DELETE FROM basket_promo_freebies")
            cursor.execute("DELETE FROM basket_promos")
            insert_promo = """
                INSERT INTO basket_promos (code, name, threshold, message)
                VALUES (%s, %s, %s, %s)
            """
            insert_freebie = """
                INSERT INTO basket_promo_freebies (promo_id, product_stock_no, variant_index, quantity)
                VALUES (%s, %s, %s, %s)
            """
            for promo in basket_promos:
                cursor.execute(
                    insert_promo,
                    (
                        promo.get("code"),
                        promo.get("name"),
                        float(promo.get("threshold", 0)),
                        promo.get("message", ""),
                    ),
                )
                promo_id = cursor.lastrowid
                for freebie in promo.get("freebies", []):
                    cursor.execute(
                        insert_freebie,
                        (
                            promo_id,
                            freebie.get("barcode"),
                            int(freebie.get("variant_index", 0)),
                            int(freebie.get("quantity", 1)),
                        ),
                    )
        conn.commit()
        return True
    except Error as exc:
        conn.rollback()
        show_error("Save Error", f"Failed to save basket promos: {exc}", parent)
        return False
    finally:
        try:
            conn.close()
        except Exception:
            pass
def load_basket_promos(parent=None):
    """
    Loads basket-size promos that award freebies when order totals reach defined thresholds.
    """
    global basket_promos
    basket_promos = []
    conn = get_db_connection(parent)
    if not conn:
        return False
    try:
        with conn.cursor(dictionary=True) as cursor:
            cursor.execute(
                "SELECT promo_id, code, name, threshold, message FROM basket_promos ORDER BY threshold"
            )
            promos = cursor.fetchall()
            for promo in promos:
                entry = {
                    "code": promo["code"],
                    "name": promo["name"],
                    "threshold": float(promo["threshold"]),
                    "message": promo.get("message", ""),
                    "freebies": [],
                }
                cursor.execute(
                    """
                    SELECT product_stock_no, variant_index, quantity
                    FROM basket_promo_freebies
                    WHERE promo_id = %s
                    """,
                    (promo["promo_id"],),
                )
                freebies = cursor.fetchall()
                for freebie in freebies:
                    entry["freebies"].append(
                        {
                            "barcode": freebie["product_stock_no"],
                            "variant_index": int(freebie["variant_index"]),
                            "quantity": int(freebie["quantity"]),
                        }
                    )
                basket_promos.append(entry)
        basket_promos.sort(key=lambda x: x["threshold"])
        return True
    except Error as exc:
        show_error("Database Error", f"Failed to load basket promos: {exc}", parent)
        return False
    finally:
        try:
            conn.close()
        except Exception:
            pass
def save_promo_inventory(parent=None):
    """
    Persists the promo inventory mapping to the database.
    """
    conn = get_db_connection(parent)
    if not conn:
        return False
    try:
        with conn.cursor() as cursor:
            cursor.execute("DELETE FROM promo_types")
            insert_query = """
                INSERT INTO promo_types (promo_code, units_per_sale, name)
                VALUES (%s, %s, %s)
            """
            for promo_code in sorted(promo_inventory_map.keys()):
                cursor.execute(
                    insert_query,
                    (
                        promo_code,
                        promo_inventory_map[promo_code],
                        promo_code,
                    ),
                )
        conn.commit()
        return True
    except Error as exc:
        conn.rollback()
        show_error("Save Error", f"Failed to save promo inventory: {exc}", parent)
        return False
    finally:
        try:
            conn.close()
        except Exception:
            pass
def rebuild_product_variant_lookup():
    """
    Builds a flat lookup mapping SKU codes (including promo variants) to their base product information.
    """
    global product_variant_lookup, product_id_lookup
    product_variant_lookup = {}
    product_id_lookup = {}
    for barcode, variants in products.items():
        for index, variant in enumerate(variants):
            product_id = variant.get("_product_id")
            if product_id is not None:
                try:
                    product_id_lookup[int(product_id)] = (barcode, index)
                except (TypeError, ValueError):
                    pass
            base_entry = {
                "sku": barcode,
                "base_barcode": barcode,
                "variant_index": index,
                "promo_code": None,
                "price": variant['price'],
                "name": variant['name'],
                "inventory_usage": 1,
                "image_filename": variant.get('image_filename', ''),
                "code": variant.get('code'),
            }
            # Only set the base barcode entry once to preserve the primary lookup
            product_variant_lookup.setdefault(barcode, base_entry)
            promos = variant.get('promos', {}) or {}
            for promo_code, promo_price in promos.items():
                promo_sku = f"{barcode}_{promo_code}"
                inventory_usage = promo_inventory_map.get(promo_code, 1)
                if promo_code not in promo_inventory_map:
                    print(
                        f"Warning: promo code '{promo_code}' is missing from the promo inventory map. "
                        "Defaulting inventory usage to 1."
                    )
                promo_price_value = promo_price if promo_price is not None else variant['price']
                product_variant_lookup[promo_sku] = {
                    "sku": promo_sku,
                    "base_barcode": barcode,
                    "variant_index": index,
                    "promo_code": promo_code,
                    "price": promo_price_value,
                    "name": variant['name'],
                    "inventory_usage": inventory_usage,
                    "image_filename": variant.get('image_filename', ''),
                    "code": variant.get('code'),
                }
    for bundle_code, bundle in bundle_promos.items():
        components = bundle.get("components") or []
        resolved_components = []
        for component in components:
            barcode = component.get("barcode")
            variant_index = component.get("variant_index", 0)
            quantity = component.get("quantity", 1)
            if not barcode or quantity <= 0:
                continue
            variants = products.get(barcode, [])
            if not variants:
                print(f"Warning: bundle '{bundle_code}' references missing product '{barcode}'.")
                continue
            if variant_index >= len(variants):
                print(f"Warning: bundle '{bundle_code}' references invalid variant index for '{barcode}'. Using first variant.")
                variant_index = 0
            variant = variants[variant_index]
            resolved_components.append({
                "barcode": barcode,
                "variant_index": variant_index,
                "quantity": quantity,
                "name": variant.get("name", barcode),
                "base_price": float(variant.get("price", 0))
            })
        if not resolved_components:
            continue
        sku = bundle.get("sku") or bundle_code
        bundle_name = bundle.get("name") or f"Bundle {bundle_code}"
        bundle_price = float(bundle.get("price", 0))
        image_filename = bundle.get("image_filename", "")
        display_components = [
            f"{comp['quantity']} x {comp['name']} ({comp['barcode']})"
            for comp in resolved_components
        ]
        product_variant_lookup[sku] = {
            "sku": sku,
            "base_barcode": None,
            "variant_index": None,
            "promo_code": bundle_code,
            "bundle_code": bundle_code,
            "price": bundle_price,
            "name": bundle_name,
            "inventory_usage": None,
            "image_filename": image_filename,
            "bundle_components": resolved_components,
            "display_components": display_components,
            "code": None,
        }


def locate_variant_by_product_id(product_id):
    """
    Return (stock_no, variant_dict, variant_index) for a given product_id if available.
    """
    if product_id is None:
        return None, None, None
    try:
        normalized_id = int(product_id)
    except (TypeError, ValueError):
        return None, None, None
    mapping = product_id_lookup.get(normalized_id)
    if not mapping:
        return None, None, None
    barcode, variant_index = mapping
    variants = products.get(barcode, [])
    if variant_index is None or variant_index >= len(variants):
        return barcode, None, variant_index
    return barcode, variants[variant_index], variant_index
def save_products_to_database(parent=None):
    """
    Saves the current product data (including updated stock and image filename) to the database.
    """
    conn = get_db_connection(parent)
    if not conn:
        return
    try:
        supports_product_codes = ensure_product_code_column(conn)
        supports_promo_prices = ensure_promo_price_column(conn)
        with conn.cursor() as cursor:
            if supports_product_codes:
                update_query = """
                    UPDATE products
                       SET code = %s,
                           name = %s,
                           price = %s,
                           stock = %s,
                           image_filename = %s
                     WHERE product_id = %s
                """
                insert_query = """
                    INSERT INTO products (stock_no, code, name, price, stock, image_filename)
                    VALUES (%s, %s, %s, %s, %s, %s)
                """
            else:
                update_query = """
                    UPDATE products
                       SET name = %s,
                           price = %s,
                           stock = %s,
                           image_filename = %s
                     WHERE product_id = %s
                """
                insert_query = """
                    INSERT INTO products (stock_no, name, price, stock, image_filename)
                    VALUES (%s, %s, %s, %s, %s)
                """
            delete_promos_query = "DELETE FROM product_promotions WHERE product_id = %s"
            if supports_promo_prices:
                promo_insert_query = """
                    INSERT INTO product_promotions (product_id, promo_code, promo_price)
                    VALUES (%s, %s, %s)
                    ON DUPLICATE KEY UPDATE promo_price = VALUES(promo_price)
                """
            else:
                warn_missing_promo_price_support()
                promo_insert_query = """
                    INSERT INTO product_promotions (product_id, promo_code)
                    VALUES (%s, %s)
                """
            for barcode, variants in products.items():
                for variant in variants:
                    product_id = variant.get("_product_id")
                    name = variant["name"]
                    price = float(variant["price"])
                    stock = int(variant["stock"])
                    image_filename = variant.get("image_filename") or None
                    code_value = normalize_product_code(variant.get("code"))
                    variant["code"] = code_value
                    if product_id:
                        if supports_product_codes:
                            cursor.execute(
                                update_query,
                                (code_value, name, price, stock, image_filename, product_id),
                            )
                        else:
                            cursor.execute(
                                update_query,
                                (name, price, stock, image_filename, product_id),
                            )
                    else:
                        if supports_product_codes:
                            cursor.execute(
                                insert_query,
                                (barcode, code_value, name, price, stock, image_filename),
                            )
                        else:
                            cursor.execute(
                                insert_query,
                                (barcode, name, price, stock, image_filename),
                            )
                        product_id = cursor.lastrowid
                        variant["_product_id"] = product_id
                    cursor.execute(delete_promos_query, (product_id,))
                    promos = variant.get("promos") or {}
                    if supports_promo_prices:
                        for promo_code, promo_price in promos.items():
                            cursor.execute(
                                promo_insert_query,
                                (product_id, promo_code, float(promo_price)),
                            )
                    else:
                        for promo_code in promos.keys():
                            cursor.execute(
                                promo_insert_query,
                                (product_id, promo_code),
                            )
        conn.commit()
    except Error as exc:
        conn.rollback()
        show_error("Save Error", f"Failed to persist products to the database: {exc}", parent)
    finally:
        try:
            conn.close()
        except Exception:
            pass
# --- User Management Functions ---
def load_users(parent=None):
    """
    Loads usernames and password hashes from the database.
    Falls back to creating a default cashier account if table is empty.
    """
    global users_data
    users_data = {}
    conn = get_db_connection(parent)
    if not conn:
        return False
    try:
        with conn.cursor(dictionary=True) as cursor:
            cursor.execute("SELECT username, password_hash, is_admin FROM users")
            records = cursor.fetchall()
            for row in records:
                users_data[row["username"]] = {
                    "password_hash": row["password_hash"],
                    "is_admin": bool(row.get("is_admin", 0)),
                }
            if not users_data:
                default_hash = generate_password_hash("cashier123")
                cursor.execute(
                    """
                    INSERT INTO users (username, password_hash, is_admin)
                    VALUES (%s, %s, %s)
                    """,
                    ("cashier", default_hash, False),
                )
                conn.commit()
                users_data["cashier"] = {
                    "password_hash": default_hash,
                    "is_admin": False,
                }
        return True
    except Error as exc:
        show_error("Database Error", f"Failed to load users: {exc}", parent)
        return False
    finally:
        try:
            conn.close()
        except Exception:
            pass
def save_users(parent=None):
    """
    Persists the in-memory users_data mapping to the database.
    """
    conn = get_db_connection(parent)
    if not conn:
        return False
    try:
        with conn.cursor() as cursor:
            upsert_query = """
                INSERT INTO users (username, password_hash, is_admin)
                VALUES (%s, %s, %s)
                ON DUPLICATE KEY UPDATE
                    password_hash = VALUES(password_hash),
                    is_admin = VALUES(is_admin)
            """
            for username, entry in users_data.items():
                cursor.execute(
                    upsert_query,
                    (
                        username,
                        entry["password_hash"],
                        bool(entry.get("is_admin", False)),
                    ),
                )
        conn.commit()
        return True
    except Error as exc:
        conn.rollback()
        show_error("Database Error", f"Failed to save users: {exc}", parent)
        return False
    finally:
        try:
            conn.close()
        except Exception:
            pass
def save_tendered_amounts():
    """Persists tendered totals to the tendered_totals table."""
    global total_cash_tendered, total_gcash_tendered
    conn = get_db_connection()
    if not conn:
        return
    try:
        with conn.cursor() as cursor:
            query = """
                INSERT INTO tendered_totals (payment_method, total_amount)
                VALUES (%s, %s)
                ON DUPLICATE KEY UPDATE total_amount = VALUES(total_amount)
            """
            cursor.execute(query, ("cash", float(total_cash_tendered)))
            cursor.execute(query, ("gcash", float(total_gcash_tendered)))
        conn.commit()
    except Error as exc:
        conn.rollback()
        print(f"Error saving tendered amounts: {exc}")
    finally:
        try:
            conn.close()
        except Exception:
            pass
def load_tendered_amounts():
    """Loads tendered totals from the tendered_totals table."""
    global total_cash_tendered, total_gcash_tendered
    conn = get_db_connection()
    if not conn:
        total_cash_tendered = 0.0
        total_gcash_tendered = 0.0
        return
    try:
        with conn.cursor(dictionary=True) as cursor:
            cursor.execute("SELECT payment_method, total_amount FROM tendered_totals")
            rows = cursor.fetchall()
            totals = {row["payment_method"]: float(row["total_amount"]) for row in rows}
            total_cash_tendered = totals.get("cash", 0.0)
            total_gcash_tendered = totals.get("gcash", 0.0)
    except Error as exc:
        print(f"Error loading tendered amounts: {exc}")
        total_cash_tendered = 0.0
        total_gcash_tendered = 0.0
    finally:
        try:
            conn.close()
        except Exception:
            pass
# Place this function at the top of your script, before any class definitions
def save_receipt_pdf(receipt_text, file_path):
    layout = compute_receipt_layout()
    width_mm = RECEIPT_PAGE_WIDTH_MM
    height_mm = 297
    margin_left_right = RECEIPT_MARGIN_MM * mm
    margin_top_bottom = RECEIPT_TOP_MARGIN_MM * mm
    page_width = width_mm * mm
    page_height = height_mm * mm
    c = canvas.Canvas(file_path, pagesize=(page_width, page_height))
    font_name = layout["font_name"]
    font_size = layout["font_size"]
    c.setFont(font_name, font_size)
    x_start = margin_left_right
    y_start = page_height - margin_top_bottom
    render_receipt_text(c, receipt_text, layout, x_start, y_start)
    c.showPage()
    c.save()
def save_inventory_summary():
    """Inventory data is persisted in MySQL; nothing to export."""
    return True
def save_sales_summary():
    """Sales data is stored in MySQL; no file save required."""
    return True
def purge_sales_tables(parent=None):
    """Delete all rows from sales_transactions and sales_items."""
    conn = get_db_connection(parent)
    if not conn:
        return False
    try:
        with conn.cursor() as cursor:
            cursor.execute("DELETE FROM sales_items")
            cursor.execute("DELETE FROM sales_transactions")
        conn.commit()
        return True
    except Error as exc:
        try:
            conn.rollback()
        except Exception:
            pass
        show_error("Database Error", f"Failed to clear sales tables:\n{exc}", parent)
        return False
    finally:
        try:
            conn.close()
        except Exception:
            pass
def ensure_sales_vault_started():
    """Ensure the vault has a period start timestamp."""
    global sales_vault_period_start
    if not sales_vault_period_start:
        sales_vault_period_start = datetime.now().isoformat(timespec="seconds")
def load_sales_vault():
    """Load the persisted sales vault ledger from disk."""
    global sales_summary_vault, total_cash_tendered_vault, total_gcash_tendered_vault, sales_vault_period_start, transaction_tracking_index
    if not os.path.exists(SALES_VAULT_FILE):
        ensure_sales_vault_started()
        return
    try:
        with open(SALES_VAULT_FILE, "r", encoding="utf-8") as f:
            data = json.load(f) or {}
    except Exception as exc:
        print(f"Warning: unable to load sales vault: {exc}")
        ensure_sales_vault_started()
        return
    sales_summary_vault = data.get("summary", {}) or {}
    total_cash_tendered_vault = float(data.get("cash_total", 0.0) or 0.0)
    total_gcash_tendered_vault = float(data.get("gcash_total", 0.0) or 0.0)
    sales_vault_period_start = data.get("period_start") or None
    transaction_tracking_index = data.get("transactions", {}) or {}
    ensure_sales_vault_started()
def save_sales_vault():
    """Persist the running vault ledger to disk."""
    ensure_sales_vault_started()
    payload = {
        "summary": sales_summary_vault,
        "cash_total": float(total_cash_tendered_vault),
        "gcash_total": float(total_gcash_tendered_vault),
        "period_start": sales_vault_period_start,
        "last_saved": datetime.now().isoformat(timespec="seconds"),
        "transactions": transaction_tracking_index,
    }
    try:
        with open(SALES_VAULT_FILE, "w", encoding="utf-8") as f:
            json.dump(payload, f, indent=2)
    except Exception as exc:
        print(f"Warning: unable to save sales vault: {exc}")
def reset_sales_vault(new_start=None):
    """Clear the vault ledger but immediately begin a new period."""
    global sales_summary_vault, total_cash_tendered_vault, total_gcash_tendered_vault, sales_vault_period_start, transaction_tracking_index
    sales_summary_vault = {}
    total_cash_tendered_vault = 0.0
    total_gcash_tendered_vault = 0.0
    sales_vault_period_start = new_start or datetime.now().isoformat(timespec="seconds")
    transaction_tracking_index = {}
    save_sales_vault()


def generate_transaction_uuid():
    """Return a unique identifier for checkout grouping."""
    return uuid.uuid4().hex


def generate_reference_code(prefix=TRANSACTION_REFERENCE_PREFIX, seed=None):
    """Generate a human-friendly reference that embeds the business prefix and date."""
    safe_prefix = (prefix or TRANSACTION_REFERENCE_PREFIX or "POS").strip().upper()
    date_token = datetime.now().strftime("%Y%m%d")
    if seed:
        sanitized = str(seed).replace("-", "").strip()
        random_token = (sanitized[:6] or uuid.uuid4().hex[:6]).upper()
    else:
        random_token = uuid.uuid4().hex[:6].upper()
    return f"{safe_prefix}-{date_token}-{random_token}"


def register_transaction_ledger_entry(entry):
    """Persist a structured record of a completed checkout for later reconciliation."""
    global transaction_tracking_index
    if not isinstance(entry, dict):
        return
    transaction_uuid = (entry.get("transaction_uuid") or "").strip()
    if not transaction_uuid:
        return
    entry.setdefault("created_at", datetime.now().strftime(REFERENCE_TIMESTAMP_FORMAT))
    transaction_tracking_index[transaction_uuid] = entry
    save_sales_vault()


def tag_transaction_lines_with_reference(ref_no, target_skus=None, reason="manual"):
    """
    Update ledger lines that match the provided SKUs with the supplied reference.
    Target SKUs of None indicates that the reference applies to every pending line.
    """
    if not transaction_tracking_index or not ref_no:
        return
    normalized_ref = str(ref_no).strip()
    if not normalized_ref:
        return
    now_ts = datetime.now().strftime(REFERENCE_TIMESTAMP_FORMAT)
    target_set = {str(sku).strip() for sku in (target_skus or []) if str(sku).strip()}
    target_set = target_set or None
    updated_any = False
    for txn_uuid, txn_data in transaction_tracking_index.items():
        line_items = txn_data.get("line_items") or []
        txn_updated = False
        for line in line_items:
            sku_text = str(line.get("sku") or "").strip()
            if target_set is not None and sku_text not in target_set:
                continue
            if line.get("status") == "voided":
                continue
            line["status"] = reason or "tagged"
            line["ref_no"] = normalized_ref
            line["status_updated_at"] = now_ts
            history = line.setdefault("status_history", [])
            history.append(
                {
                    "timestamp": now_ts,
                    "reason": reason or "manual",
                    "ref_no": normalized_ref,
                }
            )
            txn_updated = True
        if txn_updated:
            txn_data["last_reference"] = normalized_ref
            txn_data["last_reference_reason"] = reason or "manual"
            clear_history = txn_data.setdefault("clear_history", [])
            clear_history.append(
                {
                    "timestamp": now_ts,
                    "reason": reason or "manual",
                    "ref_no": normalized_ref,
                    "skus": list(target_set) if target_set is not None else None,
                }
            )
            txn_data["fully_cleared_at"] = txn_data.get("fully_cleared_at") or (
                now_ts if all((line.get("status") != "pending") for line in line_items) else None
            )
            updated_any = True
    if updated_any:
        save_sales_vault()


def mark_transaction_voided(transaction_uuid):
    """Flag ledger entries as voided so they are not mistaken for posted/exported sales."""
    if not transaction_uuid:
        return
    txn = transaction_tracking_index.get(transaction_uuid)
    if not txn:
        return
    now_ts = datetime.now().strftime(REFERENCE_TIMESTAMP_FORMAT)
    txn["voided"] = True
    txn["voided_at"] = now_ts
    for line in txn.get("line_items") or []:
        line["status"] = "voided"
        line["status_updated_at"] = now_ts
        history = line.setdefault("status_history", [])
        history.append({"timestamp": now_ts, "reason": "voided", "ref_no": line.get("ref_no")})
    save_sales_vault()
def fetch_highest_sales_identifiers(parent=None):
    """Return the highest sales_no and transaction_no recorded in the database."""
    conn = get_db_connection(parent)
    if not conn:
        return 0, 0
    max_sales = 0
    max_trans = 0
    try:
        with conn.cursor(dictionary=True) as cursor:
            cursor.execute("SHOW COLUMNS FROM sales_transactions LIKE 'transaction_no'")
            has_transaction_column = cursor.fetchone() is not None
            select_sql = [
                "SELECT MAX(CAST(sales_no AS UNSIGNED)) AS max_sales_no",
                ", MAX(CAST(transaction_no AS UNSIGNED)) AS max_transaction_no" if has_transaction_column else ", NULL AS max_transaction_no",
                " FROM sales_transactions",
            ]
            cursor.execute("".join(select_sql))
            row = cursor.fetchone()
            if row:
                max_sales = int(row.get("max_sales_no") or 0)
                max_trans = int(row.get("max_transaction_no") or 0)
                if not has_transaction_column:
                    max_trans = max_sales
    except Exception as exc:
        print(f"Warning: unable to query sales identifiers: {exc}")
    finally:
        try:
            conn.close()
        except Exception:
            pass
    return max_sales, max_trans
def save_receipts_archive():
    """
    Synchronize the in-memory receipts archive with the database table.
    Ensures that added or removed receipts persist across application restarts.
    """
    global receipts_archive
    conn = get_db_connection()
    if not conn:
        return False
    try:
        with conn.cursor(dictionary=True) as cursor:
            cursor.execute("SELECT sales_key FROM receipts")
            existing_keys = {row["sales_key"] for row in cursor.fetchall()}
        current_keys = set(receipts_archive.keys())
        keys_to_delete = existing_keys - current_keys
        with conn.cursor() as cursor:
            if keys_to_delete:
                cursor.executemany(
                    "DELETE FROM receipts WHERE sales_key = %s",
                    [(key,) for key in keys_to_delete],
                )
            if receipts_archive:
                upsert_sql = (
                    "INSERT INTO receipts (transaction_id, sales_key, receipt_text) "
                    "VALUES (%s, %s, %s) "
                    "ON DUPLICATE KEY UPDATE receipt_text = VALUES(receipt_text)"
                )
                cursor.executemany(
                    upsert_sql,
                    [(None, key, text) for key, text in receipts_archive.items()],
                )
            elif not current_keys:
                cursor.execute("DELETE FROM receipts")
        conn.commit()
        return True
    except Error as exc:
        try:
            conn.rollback()
        except Exception:
            pass
        print(f"Error saving receipts archive: {exc}")
        return False
    finally:
        try:
            conn.close()
        except Exception:
            pass
def load_inventory_summary():
    """
    Builds the inventory summary snapshot from the products and sales_items tables.
    """
    global inventory_summary, sales_summary
    inventory_summary = {}
    conn = get_db_connection()
    if not conn:
        return False
    try:
        with conn.cursor(dictionary=True) as cursor:
            cursor.execute("SELECT product_id, stock_no, name, price, stock FROM products")
            product_rows = cursor.fetchall()
            product_id_to_stock = {}
            for row in product_rows:
                product_id_to_stock[row["product_id"]] = row["stock_no"]
                inventory_summary[row["stock_no"]] = {
                    "name": row["name"],
                    "price": float(row["price"]),
                    "stock": int(row["stock"]),
                    "original_stock": int(row["stock"]),
                    "qty_sold": 0,
                    "revenue": 0.0,
                }
            cursor.execute(
                """
                SELECT product_id, SUM(quantity) AS qty_sold, SUM(total_price) AS revenue
                  FROM sales_items
                 WHERE is_freebie = FALSE
              GROUP BY product_id
                """
            )
            sales_rows = cursor.fetchall()
            for row in sales_rows:
                stock_no = product_id_to_stock.get(row["product_id"])
                if not stock_no or stock_no not in inventory_summary:
                    continue
                qty = int(row["qty_sold"] or 0)
                revenue = float(row["revenue"] or 0.0)
                entry = inventory_summary[stock_no]
                entry["qty_sold"] = qty
                entry["revenue"] = revenue
                entry["original_stock"] += qty
                sales_summary[stock_no] = {"qty_sold": qty, "revenue": revenue}
                # Update the primary variant snapshot so UI summaries stay accurate
                if stock_no in products and products[stock_no]:
                    products[stock_no][0]["original_stock"] = entry["original_stock"]
        return True
    except Error as exc:
        show_error("Database Error", f"Failed to build inventory summary: {exc}")
        return False
    finally:
        try:
            conn.close()
        except Exception:
            pass
def load_sales_summary():
    """Rebuilds sales_summary from the sales_items table."""
    global sales_summary
    sales_summary = {}
    conn = get_db_connection()
    if not conn:
        return False
    supports_ref_column = ensure_sales_reference_columns(conn)
    try:
        with conn.cursor(dictionary=True) as cursor:
            query = [
                "SELECT p.stock_no, SUM(si.quantity) AS qty_sold, SUM(si.total_price) AS revenue",
                "  FROM sales_items si",
                "  JOIN products p ON si.product_id = p.product_id",
                " WHERE si.is_freebie = FALSE",
            ]
            if supports_ref_column:
                query.append("   AND (si.ref_no IS NULL OR si.ref_no = '')")
            query.append("GROUP BY p.stock_no")
            cursor.execute("\n".join(query))
            rows = cursor.fetchall()
            for row in rows:
                sales_summary[row["stock_no"]] = {
                    "qty_sold": int(row["qty_sold"] or 0),
                    "revenue": float(row["revenue"] or 0.0),
                }
        return True
    except Error as exc:
        show_error("Database Error", f"Failed to load sales summary: {exc}")
        return False
    finally:
        try:
            conn.close()
        except Exception:
            pass
def load_receipts_archive():
    """Loads receipts from the receipts table and sets the next counters."""
    global receipts_archive, current_sales_number, current_transaction_number
    receipts_archive = {}
    conn = get_db_connection()
    if not conn:
        return False
    max_sales_no = 0
    try:
        with conn.cursor(dictionary=True) as cursor:
            cursor.execute("SELECT sales_key, receipt_text FROM receipts")
            rows = cursor.fetchall()
            for row in rows:
                key = row["sales_key"]
                receipts_archive[key] = row["receipt_text"]
                match = re.search(r"SALES#: (\d+)", key)
                if match:
                    max_sales_no = max(max_sales_no, int(match.group(1)))
        current_sales_number = max_sales_no + 1
        current_transaction_number = max_sales_no + 1
        return True
    except Error as exc:
        show_error("Database Error", f"Failed to load receipts archive: {exc}")
        return False
    finally:
        try:
            conn.close()
        except Exception:
            pass
# Ensure the ReceiptDialog class follows after the function definition
class ReceiptDialog(QDialog):
    def __init__(self, receipt_text_content, parent=None):
        super().__init__(parent)
        self.setWindowTitle("Sales Receipt")
        self.resize(400, 700)
        self._receipt_text_content = receipt_text_content
        layout = QVBoxLayout()
        self.setLayout(layout)
        self.text_edit = QTextEdit()
        self.text_edit.setReadOnly(True)
        layout_info = compute_receipt_layout()
        preview_font = QFont(get_receipt_font_name())
        preview_font.setPointSizeF(layout_info["font_size"])
        self.text_edit.setFont(preview_font)
        self.text_edit.setText(receipt_text_content)
        layout.addWidget(self.text_edit)
        self.print_two_checkbox = QCheckBox("Print 2 copies")
        self.print_two_checkbox.setToolTip("Default prints 1 copy. Check to print 2 copies.")
        layout.addWidget(self.print_two_checkbox)
        btn_layout = QHBoxLayout()
        layout.addLayout(btn_layout)
        btn_print = QPushButton("Print Receipt")
        btn_print.setStyleSheet("background-color: #007BFF; color: white; font-weight: bold;")
        btn_print.clicked.connect(self._handle_print_clicked)
        btn_layout.addWidget(btn_print)
        btn_save_pdf = QPushButton("Save as PDF")
        btn_save_pdf.setStyleSheet("background-color: #28A745; color: white; font-weight: bold;")
        btn_save_pdf.clicked.connect(lambda: self.save_receipt_as_pdf(receipt_text_content))
        btn_layout.addWidget(btn_save_pdf)
        btn_close = QPushButton("Close")
        btn_close.clicked.connect(self.accept)
        btn_layout.addWidget(btn_close)
        self.reprint_shortcut = QShortcut(QKeySequence("Ctrl+R"), self)
        self.reprint_shortcut.activated.connect(self._handle_reprint_shortcut)

    def _handle_print_clicked(self):
        copies = 2 if self.print_two_checkbox.isChecked() else 1
        print_receipt_pdf(self._receipt_text_content, self, copies)

    def _handle_reprint_shortcut(self):
        print_receipt_pdf(self._receipt_text_content, self, copies=1)

    def save_receipt_as_pdf(self, receipt_text_content):
        file_path, _ = QFileDialog.getSaveFileName(self, "Save Receipt as PDF", "", "PDF Files (*.pdf)")
        if file_path:
            if not file_path.lower().endswith('.pdf'):
                file_path += '.pdf'
            save_receipt_pdf(receipt_text_content, file_path)
            show_info("Save Successful", f"Receipt saved as PDF: {file_path}", self)
# =================== PyQt6 UI Classes ===================
class LoginDialog(QDialog):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setWindowTitle("Sunnyware POS Login")
        self.setFixedSize(420, 360)
        self.current_user_name = None
        self.all_usernames_list = list(users_data.keys())
        self.password_visible = False
        outer_layout = QVBoxLayout(self)
        outer_layout.setContentsMargins(32, 26, 32, 26)
        outer_layout.setSpacing(14)
        title = QLabel("Welcome Back", self)
        title.setObjectName("LoginTitle")
        title.setAlignment(Qt.AlignmentFlag.AlignCenter)
        outer_layout.addWidget(title)
        subtitle = QLabel("Sign in to continue to Sunnyware POS", self)
        subtitle.setObjectName("LoginSubtitle")
        subtitle.setAlignment(Qt.AlignmentFlag.AlignCenter)
        outer_layout.addWidget(subtitle)
        card = QFrame(self)
        card.setObjectName("LoginCard")
        card_layout = QVBoxLayout(card)
        card_layout.setContentsMargins(24, 24, 24, 24)
        card_layout.setSpacing(14)
        lbl_username = QLabel("Username", card)
        card_layout.addWidget(lbl_username)
        self.combo_username = QComboBox(card)
        self.combo_username.setEditable(True)
        self.combo_username.addItems(self.all_usernames_list)
        if self.all_usernames_list:
            self.combo_username.setCurrentIndex(0)
        card_layout.addWidget(self.combo_username)
        lbl_password = QLabel("Password", card)
        card_layout.addWidget(lbl_password)
        password_layout = QHBoxLayout()
        password_layout.setSpacing(4)
        self.entry_password = QLineEdit(card)
        self.entry_password.setEchoMode(QLineEdit.EchoMode.Password)
        password_layout.addWidget(self.entry_password)
        self.btn_toggle_password = QToolButton(card)
        self.btn_toggle_password.setObjectName("EyeButton")
        self.btn_toggle_password.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_toggle_password.setIcon(build_eye_icon(False))
        self.btn_toggle_password.setIconSize(QSize(20, 20))
        self.btn_toggle_password.setCheckable(True)
        self.btn_toggle_password.clicked.connect(self.toggle_password_visibility)
        password_layout.addWidget(self.btn_toggle_password)
        card_layout.addLayout(password_layout)
        outer_layout.addWidget(card)
        button_row = QHBoxLayout()
        button_row.setSpacing(16)
        btn_login = QPushButton("Login", self)
        btn_login.setObjectName("PrimaryButton")
        btn_login.clicked.connect(self.do_login)
        button_row.addWidget(btn_login)
        btn_create_account = QPushButton("Create Account", self)
        btn_create_account.setObjectName("SecondaryButton")
        btn_create_account.clicked.connect(self.create_account_flow)
        button_row.addWidget(btn_create_account)
        outer_layout.addLayout(button_row)
        # Connect completer-like behavior manually
        self.combo_username.lineEdit().textEdited.connect(self.update_username_options)
        self.combo_username.activated.connect(self.handle_combobox_selection)
        self.combo_username.setFocus()
        self.apply_theme_styles()
    def toggle_password_visibility(self):
        self.password_visible = not self.password_visible
        self.entry_password.setEchoMode(
            QLineEdit.EchoMode.Normal if self.password_visible else QLineEdit.EchoMode.Password
        )
        self.btn_toggle_password.setIcon(build_eye_icon(self.password_visible))
    def update_username_options(self, text):
        typed_text = text.lower()
        if not typed_text:
            filtered_options = self.all_usernames_list
        else:
            filtered_options = [u for u in self.all_usernames_list if u.lower().startswith(typed_text)]
        current_text = self.combo_username.currentText()
        self.combo_username.clear()
        self.combo_username.addItems(filtered_options)
        self.combo_username.setCurrentText(current_text)
    def handle_combobox_selection(self, index):
        self.combo_username.setCurrentIndex(index)
    def apply_theme_styles(self):
        tokens = get_theme_tokens()
        self.setStyleSheet(f"""
            QDialog {{
                background-color: {tokens['background']};
            }}
            QLabel#LoginTitle {{
                font-size: 20px;
                font-weight: 600;
                color: {tokens['title']};
            }}
            QLabel#LoginSubtitle {{
                font-size: 12px;
                color: {tokens['subtitle']};
            }}
            QLabel {{
                font-size: 12px;
                color: {tokens['text']};
            }}
            QFrame#LoginCard {{
                background: {tokens['card_bg']};
                border-radius: 14px;
                border: 1px solid {tokens['card_border']};
            }}
            QLineEdit, QComboBox {{
                padding: 8px 10px;
                border-radius: 6px;
                border: 1px solid {tokens['input_border']};
                font-size: 13px;
                color: {tokens['input_text']};
                background-color: {tokens['input_bg']};
            }}
            QLineEdit:focus, QComboBox:focus {{
                border: 1px solid {tokens['button_primary_bg']};
            }}
            QPushButton#PrimaryButton {{
                background-color: {tokens['button_primary_bg']};
                color: {tokens['button_primary_text']};
                border-radius: 6px;
                padding: 10px;
                font-weight: 600;
            }}
            QPushButton#PrimaryButton:hover {{
                background-color: {tokens['button_primary_hover']};
            }}
            QPushButton#PrimaryButton:pressed {{
                background-color: {tokens['button_primary_pressed']};
            }}
            QPushButton#SecondaryButton {{
                background-color: transparent;
                color: {tokens['button_outline_text']};
                border: 1px solid {tokens['button_outline_border']};
                border-radius: 6px;
                padding: 10px;
                font-weight: 600;
            }}
            QPushButton#SecondaryButton:hover {{
                background-color: {tokens['button_outline_hover_bg']};
                border-color: {tokens['button_outline_hover_border']};
            }}
            QPushButton#ToggleButton {{
                background-color: {tokens['toggle_bg']};
                color: {tokens['text']};
                border-radius: 6px;
                padding: 6px 12px;
            }}
            QPushButton#ToggleButton:hover {{
                background-color: {tokens['toggle_hover']};
            }}
            QToolButton#EyeButton {{
                background-color: transparent;
                border: none;
                padding: 0;
            }}
            QToolButton#EyeButton:hover {{
                background-color: rgba(92, 124, 250, 0.12);
                border-radius: 10px;
            }}
        """)
    def do_login(self):
        username = self.combo_username.currentText().strip()
        password = self.entry_password.text()
        if not username or not password:
            show_error("Login Error", "Please enter both username and password.", self)
            return
        if username not in users_data:
            show_error("Login Error", "User  not found.", self)
            return
        stored = users_data.get(username, {})
        stored_hash = stored.get("password_hash")
        if stored_hash and check_password_hash(stored_hash, password):
            self.current_user_name = username
            self.accept()
        else:
            show_error("Login Error", "Invalid password.", self)
    def create_account_flow(self):
        admin_pw, ok = QInputDialog.getText(self, "Admin Password Required", "Enter admin password to create a new user:", echo=QLineEdit.EchoMode.Password)
        if not ok:
            return
        if admin_pw != ADMIN_PASSWORD:
            show_error("Authorization Failed", "Invalid admin password.", self)
            return
        dlg = CreateAccountDialog(self)
        if dlg.exec() == QDialog.DialogCode.Accepted:
            new_username = dlg.entry_new_username.text().strip()
            # Update the usernames list and combobox
            self.all_usernames_list = list(users_data.keys())
            self.combo_username.clear()
            self.combo_username.addItems(self.all_usernames_list)
            self.combo_username.setCurrentText(new_username)
class CreateAccountDialog(QDialog):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setWindowTitle("Create New Account")
        self.setFixedSize(400, 380)
        self.new_password_visible = False
        self.confirm_password_visible = False
        layout = QVBoxLayout()
        lbl_new_username = QLabel("New Username:")
        lbl_new_username.setFont(QFont("Arial", 10))
        layout.addWidget(lbl_new_username)
        self.entry_new_username = QLineEdit()
        self.entry_new_username.setFixedWidth(300)
        layout.addWidget(self.entry_new_username)
        lbl_new_password = QLabel("New Password:")
        lbl_new_password.setFont(QFont("Arial", 10))
        layout.addWidget(lbl_new_password)
        pass_layout = QHBoxLayout()
        pass_layout.setSpacing(4)
        self.entry_new_password = QLineEdit()
        self.entry_new_password.setEchoMode(QLineEdit.EchoMode.Password)
        self.entry_new_password.setFixedWidth(300)
        pass_layout.addWidget(self.entry_new_password)
        self.btn_toggle_new_password = QToolButton()
        self.btn_toggle_new_password.setObjectName("EyeButton")
        self.btn_toggle_new_password.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_toggle_new_password.setIcon(build_eye_icon(False))
        self.btn_toggle_new_password.setIconSize(QSize(20, 20))
        self.btn_toggle_new_password.clicked.connect(self.toggle_password_visibility_new)
        pass_layout.addWidget(self.btn_toggle_new_password)
        layout.addLayout(pass_layout)
        lbl_confirm_password = QLabel("Confirm Password:")
        lbl_confirm_password.setFont(QFont("Arial", 10))
        layout.addWidget(lbl_confirm_password)
        conf_pass_layout = QHBoxLayout()
        conf_pass_layout.setSpacing(4)
        self.entry_confirm_password = QLineEdit()
        self.entry_confirm_password.setEchoMode(QLineEdit.EchoMode.Password)
        self.entry_confirm_password.setFixedWidth(300)
        conf_pass_layout.addWidget(self.entry_confirm_password)
        self.btn_toggle_confirm_password = QToolButton()
        self.btn_toggle_confirm_password.setObjectName("EyeButton")
        self.btn_toggle_confirm_password.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_toggle_confirm_password.setIcon(build_eye_icon(False))
        self.btn_toggle_confirm_password.setIconSize(QSize(20, 20))
        self.btn_toggle_confirm_password.clicked.connect(self.toggle_password_visibility_confirm)
        conf_pass_layout.addWidget(self.btn_toggle_confirm_password)
        layout.addLayout(conf_pass_layout)
        btn_create_account = QPushButton("Create Account")
        btn_create_account.setObjectName("PrimaryButton")
        btn_create_account.clicked.connect(self.save_new_user)
        btn_create_account.setFixedWidth(150)
        layout.addWidget(btn_create_account, alignment=Qt.AlignmentFlag.AlignCenter)
        self.setLayout(layout)
        self.apply_theme_styles()
    def toggle_password_visibility_new(self):
        self.new_password_visible = not self.new_password_visible
        self.entry_new_password.setEchoMode(
            QLineEdit.EchoMode.Normal if self.new_password_visible else QLineEdit.EchoMode.Password
        )
        self.btn_toggle_new_password.setIcon(build_eye_icon(self.new_password_visible))
    def toggle_password_visibility_confirm(self):
        self.confirm_password_visible = not self.confirm_password_visible
        self.entry_confirm_password.setEchoMode(
            QLineEdit.EchoMode.Normal if self.confirm_password_visible else QLineEdit.EchoMode.Password
        )
        self.btn_toggle_confirm_password.setIcon(build_eye_icon(self.confirm_password_visible))
    def save_new_user(self):
        new_username = self.entry_new_username.text().strip()
        new_password = self.entry_new_password.text().strip()
        confirm_password = self.entry_confirm_password.text().strip()
        if not new_username or not new_password or not confirm_password:
            show_error("Input Error", "All fields are required.", self)
            return
        if new_username in users_data:
            show_error("Input Error", "Username already exists. Please choose a different one.", self)
            return
        if new_password != confirm_password:
            show_error("Input Error", "Passwords do not match.", self)
            return
        # Password requirements validation
        if len(new_password) < 8:
            show_error("Password Policy", "Password must be at least 8 characters long.", self)
            return
        if not any(char.isupper() for char in new_password):
            show_error("Password Policy", "Password must contain at least one uppercase letter.", self)
            return
        if not any(char.isdigit() for char in new_password):
            show_error("Password Policy", "Password must contain at least one number.", self)
            return
        users_data[new_username] = {
            "password_hash": generate_password_hash(new_password),
            "is_admin": False
        }
        save_users(self)
        show_info("Success", f"User  '{new_username}' created successfully. You can now login with this account.", self)
        self.accept()
    def apply_theme_styles(self):
        tokens = get_theme_tokens()
        self.setStyleSheet(f"""
            QDialog {{
                background-color: {tokens['background']};
                color: {tokens['text']};
            }}
            QLabel {{
                color: {tokens['text']};
                font-size: 12px;
            }}
            QLineEdit {{
                padding: 8px 10px;
                border-radius: 6px;
                border: 1px solid {tokens['input_border']};
                background-color: {tokens['input_bg']};
                color: {tokens['input_text']};
            }}
            QLineEdit:focus {{
                border: 1px solid {tokens['button_primary_bg']};
            }}
            QPushButton#PrimaryButton {{
                background-color: {tokens['button_primary_bg']};
                color: {tokens['button_primary_text']};
                border-radius: 6px;
                padding: 10px;
                font-weight: 600;
            }}
            QPushButton#PrimaryButton:hover {{
                background-color: {tokens['button_primary_hover']};
            }}
            QPushButton#PrimaryButton:pressed {{
                background-color: {tokens['button_primary_pressed']};
            }}
            QToolButton#EyeButton {{
                background-color: transparent;
                border: none;
                padding: 0;
            }}
            QToolButton#EyeButton:hover {{
                background-color: rgba(92, 124, 250, 0.12);
                border-radius: 10px;
            }}
        """)
class InventoryManagementDialog(QDialog):
    def __init__(self, products, parent=None):
        super().__init__(parent)
        self.setWindowTitle("Inventory Management")
        self.resize(880, 620)
        self.products = products  # Store the products dictionary
        main_layout = QVBoxLayout(self)
        main_layout.setContentsMargins(28, 20, 28, 20)
        main_layout.setSpacing(12)
        title = QLabel("Inventory Dashboard", self)
        title.setObjectName("InventoryTitle")
        main_layout.addWidget(title)
        subtitle = QLabel("Monitor stocks at a glance, then deep-dive into bundles, promos, or basket rewards without leaving this dashboard.", self)
        subtitle.setObjectName("InventorySubtitle")
        subtitle.setWordWrap(True)
        main_layout.addWidget(subtitle)
        self.tabs = QTabWidget()
        self.tabs.setDocumentMode(True)
        self.tabs.setStyleSheet("QTabWidget::pane { border: none; }")
        main_layout.addWidget(self.tabs)
        self.tabs.addTab(self.build_inventory_tab(), "Inventory Overview")
        self.tabs.addTab(self.build_bundles_tab(), "Bundles")
        self.tabs.addTab(self.build_promos_tab(), "Promos")
        self.tabs.addTab(self.build_basket_tab(), "Basket Rewards")
        button_box = QDialogButtonBox(QDialogButtonBox.StandardButton.Close)
        close_btn = button_box.button(QDialogButtonBox.StandardButton.Close)
        close_btn.setText("Close Dashboard")
        close_btn.setObjectName("AccentButton")
        close_btn.clicked.connect(self.reject)
        main_layout.addWidget(button_box, alignment=Qt.AlignmentFlag.AlignRight)
        self.apply_theme_styles()
        self.populate_table()
        self.populate_bundle_table()
        self.populate_promos_table()
        self.populate_basket_table()
    def build_inventory_tab(self):
        tab = QWidget()
        layout = QVBoxLayout(tab)
        layout.setContentsMargins(0, 0, 0, 0)
        card = QFrame(self)
        card.setObjectName("InventoryCard")
        card_layout = QVBoxLayout(card)
        card_layout.setContentsMargins(20, 20, 20, 20)
        card_layout.setSpacing(16)
        self.inventory_table = QTableWidget(0, 4, card)
        self.inventory_table.setHorizontalHeaderLabels(["Stock No.", "Code", "Product Name", "Stock Left"])
        inventory_header = self.inventory_table.horizontalHeader()
        inventory_header.setStretchLastSection(False)
        inventory_header.setSectionResizeMode(QHeaderView.ResizeMode.Interactive)
        inventory_header.setSectionResizeMode(0, QHeaderView.ResizeMode.ResizeToContents)
        inventory_header.setSectionResizeMode(1, QHeaderView.ResizeMode.ResizeToContents)
        inventory_header.setSectionResizeMode(2, QHeaderView.ResizeMode.Stretch)
        inventory_header.setSectionResizeMode(3, QHeaderView.ResizeMode.ResizeToContents)
        self.inventory_table.setAlternatingRowColors(True)
        self.inventory_table.setWordWrap(False)
        self.inventory_table.setSortingEnabled(True)
        self.inventory_table.setSelectionBehavior(QTableWidget.SelectionBehavior.SelectRows)
        self.inventory_table.setEditTriggers(QTableWidget.EditTrigger.NoEditTriggers)
        card_layout.addWidget(self.inventory_table)
        button_grid = QGridLayout()
        button_grid.setSpacing(12)
        btn_import = QPushButton("Import Excel", self)
        btn_import.clicked.connect(self.import_excel)
        button_grid.addWidget(btn_import, 0, 0)
        btn_replenish = QPushButton("Replenish Stock", self)
        btn_replenish.clicked.connect(self.replenish_stock)
        button_grid.addWidget(btn_replenish, 0, 1)
        btn_export = QPushButton("Export Summary", self)
        btn_export.clicked.connect(self.export_summary)
        button_grid.addWidget(btn_export, 0, 2)
        btn_add_product = QPushButton("Add Product", self)
        btn_add_product.clicked.connect(self.add_new_product)
        button_grid.addWidget(btn_add_product, 1, 0)
        btn_sync_api = QPushButton("Sync via API", self)
        btn_sync_api.clicked.connect(self.sync_inventory_from_api)
        button_grid.addWidget(btn_sync_api, 1, 1, 1, 2)
        card_layout.addLayout(button_grid)
        layout.addWidget(card)
        return tab
    def build_bundles_tab(self):
        tab = QWidget()
        layout = QVBoxLayout(tab)
        layout.setContentsMargins(0, 0, 0, 0)
        card = QFrame(self)
        card.setObjectName("ManagementCard")
        card_layout = QVBoxLayout(card)
        card_layout.setContentsMargins(20, 20, 20, 20)
        card_layout.setSpacing(16)
        header = QLabel("Bundle Library")
        header.setFont(QFont("Arial", 14, QFont.Weight.Bold))
        card_layout.addWidget(header)
        self.bundle_table = QTableWidget(0, 5, card)
        self.bundle_table.setHorizontalHeaderLabels(["Code", "Name", "Price", "Components", "SKU"])
        bundle_header = self.bundle_table.horizontalHeader()
        bundle_header.setStretchLastSection(False)
        bundle_header.setSectionResizeMode(QHeaderView.ResizeMode.Interactive)
        bundle_header.setSectionResizeMode(0, QHeaderView.ResizeMode.ResizeToContents)
        bundle_header.setSectionResizeMode(1, QHeaderView.ResizeMode.Stretch)
        bundle_header.setSectionResizeMode(2, QHeaderView.ResizeMode.ResizeToContents)
        bundle_header.setSectionResizeMode(3, QHeaderView.ResizeMode.Stretch)
        bundle_header.setSectionResizeMode(4, QHeaderView.ResizeMode.ResizeToContents)
        self.bundle_table.setAlternatingRowColors(True)
        self.bundle_table.setWordWrap(False)
        self.bundle_table.setSortingEnabled(True)
        self.bundle_table.setSelectionBehavior(QTableWidget.SelectionBehavior.SelectRows)
        self.bundle_table.setEditTriggers(QTableWidget.EditTrigger.NoEditTriggers)
        card_layout.addWidget(self.bundle_table)
        control_row = QHBoxLayout()
        control_row.addStretch()
        btn_manage = QPushButton("Create / Edit Bundles", self)
        btn_manage.setObjectName("AccentButton")
        btn_manage.clicked.connect(self.manage_bundles)
        control_row.addWidget(btn_manage)
        btn_remove = QPushButton("Remove Bundle", self)
        btn_remove.clicked.connect(self.show_remove_bundle_dialog)
        control_row.addWidget(btn_remove)
        btn_refresh = QPushButton("Refresh List", self)
        btn_refresh.clicked.connect(self.populate_bundle_table)
        control_row.addWidget(btn_refresh)
        card_layout.addLayout(control_row)
        layout.addWidget(card)
        return tab
    def build_promos_tab(self):
        tab = QWidget()
        layout = QVBoxLayout(tab)
        layout.setContentsMargins(0, 0, 0, 0)
        card = QFrame(self)
        card.setObjectName("ManagementCard")
        card_layout = QVBoxLayout(card)
        card_layout.setContentsMargins(20, 20, 20, 20)
        card_layout.setSpacing(16)
        header = QLabel("Promo Programs")
        header.setFont(QFont("Arial", 14, QFont.Weight.Bold))
        card_layout.addWidget(header)
        self.promos_table = QTableWidget(0, 3, card)
        self.promos_table.setHorizontalHeaderLabels(["Promo Code", "Units per Sale", "Linked Items"])
        promos_header = self.promos_table.horizontalHeader()
        promos_header.setStretchLastSection(False)
        promos_header.setSectionResizeMode(QHeaderView.ResizeMode.Interactive)
        promos_header.setSectionResizeMode(0, QHeaderView.ResizeMode.ResizeToContents)
        promos_header.setSectionResizeMode(1, QHeaderView.ResizeMode.ResizeToContents)
        promos_header.setSectionResizeMode(2, QHeaderView.ResizeMode.Stretch)
        self.promos_table.setAlternatingRowColors(True)
        self.promos_table.setWordWrap(False)
        self.promos_table.setSortingEnabled(True)
        self.promos_table.setSelectionBehavior(QTableWidget.SelectionBehavior.SelectRows)
        self.promos_table.setEditTriggers(QTableWidget.EditTrigger.NoEditTriggers)
        card_layout.addWidget(self.promos_table)
        control_row = QHBoxLayout()
        control_row.addStretch()
        btn_manage = QPushButton("Open Promo Builder", self)
        btn_manage.setObjectName("AccentButton")
        btn_manage.clicked.connect(self.manage_promos)
        control_row.addWidget(btn_manage)
        btn_remove = QPushButton("Remove Promo", self)
        btn_remove.clicked.connect(self.show_remove_promo_dialog)
        control_row.addWidget(btn_remove)
        btn_refresh = QPushButton("Refresh List", self)
        btn_refresh.clicked.connect(self.populate_promos_table)
        control_row.addWidget(btn_refresh)
        card_layout.addLayout(control_row)
        layout.addWidget(card)
        return tab
    def build_basket_tab(self):
        tab = QWidget()
        layout = QVBoxLayout(tab)
        layout.setContentsMargins(0, 0, 0, 0)
        card = QFrame(self)
        card.setObjectName("ManagementCard")
        card_layout = QVBoxLayout(card)
        card_layout.setContentsMargins(20, 20, 20, 20)
        card_layout.setSpacing(16)
        header = QLabel("Basket Rewards")
        header.setFont(QFont("Arial", 14, QFont.Weight.Bold))
        card_layout.addWidget(header)
        self.basket_table = QTableWidget(0, 4, card)
        self.basket_table.setHorizontalHeaderLabels(["Code", "Name", "Threshold", "Freebies"])
        basket_header = self.basket_table.horizontalHeader()
        basket_header.setStretchLastSection(False)
        basket_header.setSectionResizeMode(QHeaderView.ResizeMode.Interactive)
        basket_header.setSectionResizeMode(0, QHeaderView.ResizeMode.ResizeToContents)
        basket_header.setSectionResizeMode(1, QHeaderView.ResizeMode.Stretch)
        basket_header.setSectionResizeMode(2, QHeaderView.ResizeMode.ResizeToContents)
        basket_header.setSectionResizeMode(3, QHeaderView.ResizeMode.Stretch)
        self.basket_table.setAlternatingRowColors(True)
        self.basket_table.setWordWrap(False)
        self.basket_table.setSortingEnabled(True)
        self.basket_table.setSelectionBehavior(QTableWidget.SelectionBehavior.SelectRows)
        self.basket_table.setEditTriggers(QTableWidget.EditTrigger.NoEditTriggers)
        card_layout.addWidget(self.basket_table)
        control_row = QHBoxLayout()
        control_row.addStretch()
        btn_manage = QPushButton("Manage Basket Rewards", self)
        btn_manage.setObjectName("AccentButton")
        btn_manage.clicked.connect(self.manage_basket_promos)
        control_row.addWidget(btn_manage)
        btn_remove = QPushButton("Remove Reward", self)
        btn_remove.clicked.connect(self.show_remove_basket_dialog)
        control_row.addWidget(btn_remove)
        btn_refresh = QPushButton("Refresh List", self)
        btn_refresh.clicked.connect(self.populate_basket_table)
        control_row.addWidget(btn_refresh)
        card_layout.addLayout(control_row)
        layout.addWidget(card)
        return tab
    def manage_promos(self):
        dlg = PromoManagementDialog(self.products, self)
        if dlg.exec() == QDialog.DialogCode.Accepted:
            # Table content may not change, but refresh to reflect any potential data updates.
            self.populate_table()
            self.populate_promos_table()
            parent = self.parent()
            if parent and hasattr(parent, "refresh_product_search_options"):
                parent.refresh_product_search_options()
    def manage_bundles(self):
        dlg = BundlePromoDialog(self.products, self)
        if dlg.exec() == QDialog.DialogCode.Accepted:
            load_bundle_promos(self)
            self.populate_bundle_table()
            parent = self.parent()
            if parent and hasattr(parent, "refresh_product_search_options"):
                parent.refresh_product_search_options()
    def manage_basket_promos(self):
        dlg = BasketPromoDialog(self.products, self)
        if dlg.exec() == QDialog.DialogCode.Accepted:
            load_basket_promos(self)
            self.populate_basket_table()
    def replenish_stock(self):
        file_path, _ = QFileDialog.getOpenFileName(self, "Replenish Stock from Excel", "", "Excel Files (*.xlsx *.xls)")
        if file_path:
            try:
                df = pd.read_excel(file_path)
                # Check headers presence
                expected_headers = ["Stock No", "[Z95] - Exibition Warehouse"]
                if not all(header in df.columns for header in expected_headers):
                    raise ValueError(f"Excel file missing required headers. Expected headers: {expected_headers}")
                replenished_count = 0
                for index, row in df.iterrows():
                    barcode = str(row['Stock No']).strip()  # Get the barcode from the current row
                    z95_stock = row['[Z95] - Exibition Warehouse']  # Extract stock from the 6th column
                    # Check if the barcode is valid and exists in the products
                    if pd.isna(barcode) or barcode not in self.products:
                        continue  # Skip this row if barcode is NaN or not found in products
                    # Check if z95_stock is valid
                    if pd.isna(z95_stock):
                        continue  # Skip this row if z95_stock is NaN
                    try:
                        z95_stock_int = int(z95_stock)  # Convert to integer
                    except Exception:
                        continue  # Skip this row if conversion fails
                    # Update stock by adding the replenished amount
                    for variant in self.products[barcode]:
                        original_stock = variant['stock']  # Store the original stock level
                        variant['stock'] += z95_stock_int  # Add the stock
                        if variant['stock'] != original_stock:  # Check if the stock level actually changed
                            replenished_count += 1  # Increment replenished count
                save_products_to_database(self)  # Persist updated products to MySQL
                self.populate_table()  # Refresh the table
                show_info("Replenish Successful", f"Stocks replenished for {replenished_count} products.", self)
            except Exception as e:
                show_error("Replenish Error", f"Failed to replenish stock from Excel file: {e}", self)
    def add_new_product(self):
        next_product_id = self._fetch_next_product_id()
        if next_product_id is None:
            next_product_id = self._get_next_product_id()
        suggested_stock_no = self._suggest_next_stock_number()
        dialog = AddProductDialog(next_product_id, suggested_stock_no, self)
        if dialog.exec() != QDialog.DialogCode.Accepted:
            return
        details = dialog.get_values()
        if not details:
            return
        stock_no = str(details["stock_no"]).strip()
        code_value = normalize_product_code(details.get("code"))
        name = details["name"].strip()
        price = float(details["price"])
        stock_qty = int(details["stock"])
        if not stock_no:
            show_error("Missing Stock Number", "Please provide a stock number for the new product.", self)
            return
        if not name:
            show_error("Missing Name", "Please provide a product name.", self)
            return
        if stock_no in self.products:
            show_error(
                "Duplicate Stock Number",
                f"The stock number '{stock_no}' is already in use. Please choose a unique value.",
                self,
            )
            return
        product_id = self._insert_product_record(
            stock_no,
            code_value,
            name,
            price,
            stock_qty,
            preferred_product_id=next_product_id,
        )
        if not product_id:
            return
        variant = {
            "name": name,
            "price": price,
            "stock": stock_qty,
            "original_stock": stock_qty,
            "image_filename": "",
            "code": code_value,
            "promos": {},
            "_product_id": product_id,
        }
        self.products.setdefault(stock_no, []).append(variant)
        global sales_summary
        sales_summary.setdefault(stock_no, {"qty_sold": 0, "revenue": 0.0})
        rebuild_product_variant_lookup()
        self.populate_table()
        show_info(
            "Product Added",
            f"Product '{name}' was added with Product ID {product_id} and initial stock of {stock_qty}.",
            self,
        )
    def _get_next_product_id(self):
        max_id = 0
        for variants in self.products.values():
            for variant in variants:
                try:
                    candidate = int(variant.get("_product_id") or 0)
                except (TypeError, ValueError):
                    candidate = 0
                if candidate > max_id:
                    max_id = candidate
        return max_id + 1 if max_id else 1

    def _fetch_next_product_id(self):
        conn = get_db_connection(self)
        if not conn:
            return None
        try:
            with conn.cursor() as cursor:
                cursor.execute("SELECT COALESCE(MAX(product_id), 0) + 1 AS next_id FROM products")
                row = cursor.fetchone()
                if row:
                    value = row[0] if not isinstance(row, dict) else row.get("next_id")
                    return int(value or 1)
                return 1
        except Error as exc:
            show_error("Database Error", f"Unable to determine the next product ID:\n{exc}", self)
            return None
        finally:
            try:
                conn.close()
            except Exception:
                pass
    def _suggest_next_stock_number(self):
        numeric_codes = []
        for code in self.products.keys():
            text = str(code).strip()
            if text.isdigit():
                numeric_codes.append(int(text))
        if numeric_codes:
            return str(max(numeric_codes) + 1)
        return ""
    def _insert_product_record(self, stock_no, code_value, name, price, stock_qty, preferred_product_id=None):
        conn = get_db_connection(self)
        if not conn:
            return None
        try:
            supports_product_codes = ensure_product_code_column(conn)
            normalized_code = normalize_product_code(code_value)
            with conn.cursor() as cursor:
                if preferred_product_id:
                    if supports_product_codes:
                        cursor.execute(
                            """
                            INSERT INTO products (product_id, stock_no, code, name, price, stock, image_filename)
                            VALUES (%s, %s, %s, %s, %s, %s, %s)
                            """,
                            (preferred_product_id, stock_no, normalized_code, name, price, stock_qty, None),
                        )
                    else:
                        cursor.execute(
                            """
                            INSERT INTO products (product_id, stock_no, name, price, stock, image_filename)
                            VALUES (%s, %s, %s, %s, %s, %s)
                            """,
                            (preferred_product_id, stock_no, name, price, stock_qty, None),
                        )
                    new_id = preferred_product_id
                else:
                    if supports_product_codes:
                        cursor.execute(
                            """
                            INSERT INTO products (stock_no, code, name, price, stock, image_filename)
                            VALUES (%s, %s, %s, %s, %s, %s)
                            """,
                            (stock_no, normalized_code, name, price, stock_qty, None),
                        )
                    else:
                        cursor.execute(
                            """
                            INSERT INTO products (stock_no, name, price, stock, image_filename)
                            VALUES (%s, %s, %s, %s, %s)
                            """,
                            (stock_no, name, price, stock_qty, None),
                        )
                    new_id = cursor.lastrowid
            conn.commit()
            return int(new_id)
        except Error as exc:
            try:
                conn.rollback()
            except Exception:
                pass
            show_error("Add Product Failed", f"Unable to add the new product:\n{exc}", self)
            return None
        finally:
            try:
                conn.close()
            except Exception:
                pass
    def populate_table(self):
        if not hasattr(self, "inventory_table"):
            return
        self.inventory_table.setSortingEnabled(False)
        self.inventory_table.setRowCount(0)  # Clear existing rows
        # Sort products by name, but guard against missing values
        def _inventory_sort_key(entry):
            variants = entry[1] or []
            first_variant = variants[0] if variants else {}
            return sanitize_product_name(first_variant.get("name")).lower()

        sorted_products = sorted(self.products.items(), key=_inventory_sort_key)
        for barcode, variants in sorted_products:
            for variant in variants:
                row = self.inventory_table.rowCount()
                self.inventory_table.insertRow(row)
                code_value = variant.get("code") or ""
                self.inventory_table.setItem(row, 0, QTableWidgetItem(barcode))
                self.inventory_table.setItem(row, 1, QTableWidgetItem(code_value))
                name_value = sanitize_product_name(variant.get("name"))
                self.inventory_table.setItem(row, 2, QTableWidgetItem(name_value))
                self.inventory_table.setItem(row, 3, QTableWidgetItem(str(variant["stock"])))
        self.inventory_table.setSortingEnabled(True)
        QTimer.singleShot(0, self._autosize_inventory_columns)
    def populate_bundle_table(self):
        if not hasattr(self, "bundle_table"):
            return
        if not load_bundle_promos(self):
            return
        self.bundle_table.setSortingEnabled(False)
        self.bundle_table.setRowCount(0)
        for code in sorted(bundle_promos.keys()):
            bundle = bundle_promos[code]
            row = self.bundle_table.rowCount()
            self.bundle_table.insertRow(row)
            self.bundle_table.setItem(row, 0, QTableWidgetItem(code))
            self.bundle_table.setItem(row, 1, QTableWidgetItem(bundle.get("name", "")))
            price_item = QTableWidgetItem(f"P{float(bundle.get('price', 0.0)):.2f}")
            price_item.setTextAlignment(Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignVCenter)
            self.bundle_table.setItem(row, 2, price_item)
            components = bundle.get("components") or []
            comp_summary = ", ".join(f"{comp.get('quantity', 1)}x {comp.get('barcode', '-')}" for comp in components) or "-"
            self.bundle_table.setItem(row, 3, QTableWidgetItem(comp_summary))
            self.bundle_table.setItem(row, 4, QTableWidgetItem(bundle.get("sku", "")))
        self.bundle_table.setSortingEnabled(True)
        QTimer.singleShot(0, self._autosize_bundle_columns)
    def show_remove_bundle_dialog(self):
        if not bundle_promos:
            show_info("No Bundles", "There are currently no bundles to remove.", self)
            return
        dlg = QDialog(self)
        dlg.setWindowTitle("Remove Bundles")
        dlg.resize(360, 320)
        layout = QVBoxLayout(dlg)
        layout.addWidget(QLabel("Select bundle(s) to remove:", dlg))
        list_widget = QListWidget(dlg)
        list_widget.setSelectionMode(QListWidget.SelectionMode.MultiSelection)
        for code in sorted(bundle_promos.keys()):
            name = bundle_promos[code].get("name", "")
            item = QListWidgetItem(f"{code} â€” {name}")
            item.setData(Qt.ItemDataRole.UserRole, code)
            list_widget.addItem(item)
        layout.addWidget(list_widget)
        button_box = QDialogButtonBox(QDialogButtonBox.StandardButton.Cancel, dlg)
        remove_btn = button_box.addButton("Remove Selected", QDialogButtonBox.ButtonRole.AcceptRole)
        remove_btn.setEnabled(False)
        layout.addWidget(button_box)
        def update_state():
            remove_btn.setEnabled(bool(list_widget.selectedItems()))
        def do_remove():
            selected = list_widget.selectedItems()
            if not selected:
                return
            codes = [item.data(Qt.ItemDataRole.UserRole) for item in selected]
            confirm = QMessageBox.question(
                self,
                "Confirm Removal",
                "Remove the following bundle(s)?\n- " + "\n- ".join(codes),
            )
            if confirm != QMessageBox.StandardButton.Yes:
                return
            removed = 0
            for code in codes:
                if bundle_promos.pop(code, None) is not None:
                    removed += 1
            if removed:
                save_bundle_promos(self)
                self.populate_bundle_table()
                show_info("Bundles Removed", f"Removed {removed} bundle(s).", self)
            dlg.accept()
        list_widget.itemSelectionChanged.connect(update_state)
        remove_btn.clicked.connect(do_remove)
        button_box.rejected.connect(dlg.reject)
        dlg.exec()
    def populate_promos_table(self):
        if not hasattr(self, "promos_table"):
            return
        if not load_promo_inventory(self):
            return
        self.promos_table.setSortingEnabled(False)
        self.promos_table.setRowCount(0)
        for code in sorted(promo_inventory_map.keys()):
            units = promo_inventory_map.get(code, 1)
            linked = 0
            for variants in self.products.values():
                for variant in variants:
                    promos = variant.get("promos") or {}
                    if code in promos:
                        linked += 1
            row = self.promos_table.rowCount()
            self.promos_table.insertRow(row)
            self.promos_table.setItem(row, 0, QTableWidgetItem(code))
            self.promos_table.setItem(row, 1, QTableWidgetItem(str(units)))
            self.promos_table.setItem(row, 2, QTableWidgetItem(str(linked)))
        self.promos_table.setSortingEnabled(True)
        QTimer.singleShot(0, self._autosize_promos_columns)
    def show_remove_promo_dialog(self):
        if not promo_inventory_map:
            show_info("No Promos", "There are currently no promos to remove.", self)
            return
        dlg = QDialog(self)
        dlg.setWindowTitle("Remove Promos")
        dlg.resize(360, 320)
        layout = QVBoxLayout(dlg)
        layout.addWidget(QLabel("Select promo code(s) to remove:", dlg))
        list_widget = QListWidget(dlg)
        list_widget.setSelectionMode(QListWidget.SelectionMode.MultiSelection)
        for code in sorted(promo_inventory_map.keys()):
            units = promo_inventory_map.get(code, 1)
            item = QListWidgetItem(f"{code} â€” {units} unit(s)")
            item.setData(Qt.ItemDataRole.UserRole, code)
            list_widget.addItem(item)
        layout.addWidget(list_widget)
        button_box = QDialogButtonBox(QDialogButtonBox.StandardButton.Cancel, dlg)
        remove_btn = button_box.addButton("Remove Selected", QDialogButtonBox.ButtonRole.AcceptRole)
        remove_btn.setEnabled(False)
        layout.addWidget(button_box)
        def update_state():
            remove_btn.setEnabled(bool(list_widget.selectedItems()))
        def do_remove():
            selected = list_widget.selectedItems()
            if not selected:
                return
            codes = [item.data(Qt.ItemDataRole.UserRole) for item in selected]
            confirm = QMessageBox.question(
                self,
                "Confirm Removal",
                "Remove the following promo code(s)?\n- " + "\n- ".join(codes),
            )
            if confirm != QMessageBox.StandardButton.Yes:
                return
            removed = 0
            for code in codes:
                if promo_inventory_map.pop(code, None) is not None:
                    removed += 1
                try:
                    product_promo_columns.remove(code)
                except ValueError:
                    pass
                for variants in self.products.values():
                    for variant in variants:
                        promos = variant.get("promos")
                        if promos and code in promos:
                            promos.pop(code, None)
            if removed:
                save_promo_inventory(self)
                save_products_to_database(self)
                self.populate_promos_table()
                self.populate_table()
                show_info("Promos Removed", f"Removed {removed} promo(s).", self)
            dlg.accept()
        list_widget.itemSelectionChanged.connect(update_state)
        remove_btn.clicked.connect(do_remove)
        button_box.rejected.connect(dlg.reject)
        dlg.exec()
    def populate_basket_table(self):
        if not hasattr(self, "basket_table"):
            return
        if not load_basket_promos(self):
            return
        self.basket_table.setSortingEnabled(False)
        self.basket_table.setRowCount(0)
        for entry in basket_promos:
            row = self.basket_table.rowCount()
            self.basket_table.insertRow(row)
            self.basket_table.setItem(row, 0, QTableWidgetItem(entry.get("code", "")))
            self.basket_table.setItem(row, 1, QTableWidgetItem(entry.get("name", "")))
            threshold_item = QTableWidgetItem(f"P{float(entry.get('threshold', 0.0)):.2f}")
            threshold_item.setTextAlignment(Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignVCenter)
            self.basket_table.setItem(row, 2, threshold_item)
            freebies = entry.get("freebies") or []
            freebies_summary = ", ".join(
                f"{freebie.get('quantity', 1)}x {freebie.get('barcode', '')}" for freebie in freebies
            ) or "-"
            self.basket_table.setItem(row, 3, QTableWidgetItem(freebies_summary))
        self.basket_table.setSortingEnabled(True)
        QTimer.singleShot(0, self._autosize_basket_columns)
    def _autosize_inventory_columns(self):
        table = getattr(self, "inventory_table", None)
        if not table:
            return
        table.resizeColumnToContents(0)
        table.resizeColumnToContents(1)
        table.resizeColumnToContents(3)
        stock_width = table.columnWidth(0) + 24
        code_width = table.columnWidth(1) + 24
        qty_width = table.columnWidth(3) + 24
        table.setColumnWidth(0, stock_width)
        table.setColumnWidth(1, code_width)
        table.setColumnWidth(3, qty_width)
        viewport_width = table.viewport().width()
        if viewport_width <= 0:
            return
        padding = 48
        fixed = stock_width + code_width + qty_width + padding
        available = max(220, viewport_width - fixed)
        hint = table.sizeHintForColumn(2) + 24
        target = max(220, min(hint, available))
        table.setColumnWidth(2, target)
    def _autosize_bundle_columns(self):
        table = getattr(self, "bundle_table", None)
        if not table:
            return
        for index in (0, 2, 4):
            table.resizeColumnToContents(index)
        table.setColumnWidth(0, table.columnWidth(0) + 18)
        viewport_width = table.viewport().width()
        if viewport_width <= 0:
            return
        padding = 48
        fixed = sum(table.columnWidth(i) for i in (0, 2, 4)) + padding
        name_hint = table.sizeHintForColumn(1) + 24
        comp_hint = table.sizeHintForColumn(3) + 24
        remaining = viewport_width - fixed
        if remaining <= 0:
            remaining = name_hint + comp_hint
        total_hint = max(1, name_hint + comp_hint)
        scale = min(1.0, remaining / total_hint)
        name_width = max(220, int(name_hint * scale))
        comp_width = max(220, int(comp_hint * scale))
        table.setColumnWidth(1, name_width)
        table.setColumnWidth(3, comp_width)
    def _autosize_promos_columns(self):
        table = getattr(self, "promos_table", None)
        if not table:
            return
        for index in (0, 1):
            table.resizeColumnToContents(index)
        table.setColumnWidth(0, table.columnWidth(0) + 18)
        viewport_width = table.viewport().width()
        if viewport_width <= 0:
            return
        padding = 32
        fixed = table.columnWidth(0) + table.columnWidth(1) + padding
        available = max(220, viewport_width - fixed)
        hint = table.sizeHintForColumn(2) + 24
        table.setColumnWidth(2, max(220, min(hint, available)))
    def _autosize_basket_columns(self):
        table = getattr(self, "basket_table", None)
        if not table:
            return
        for index in (0, 2):
            table.resizeColumnToContents(index)
        table.setColumnWidth(0, table.columnWidth(0) + 18)
        viewport_width = table.viewport().width()
        if viewport_width <= 0:
            return
        padding = 48
        fixed = table.columnWidth(0) + table.columnWidth(2) + padding
        name_hint = table.sizeHintForColumn(1) + 24
        freebies_hint = table.sizeHintForColumn(3) + 24
        remaining = viewport_width - fixed
        if remaining <= 0:
            remaining = name_hint + freebies_hint
        total_hint = max(1, name_hint + freebies_hint)
        scale = min(1.0, remaining / total_hint)
        name_width = max(200, int(name_hint * scale))
        freebies_width = max(220, int(freebies_hint * scale))
        table.setColumnWidth(1, name_width)
        table.setColumnWidth(3, freebies_width)
    def show_remove_basket_dialog(self):
        if not basket_promos:
            show_info("No Basket Rewards", "There are currently no basket rewards to remove.", self)
            return
        dlg = QDialog(self)
        dlg.setWindowTitle("Remove Basket Rewards")
        dlg.resize(360, 320)
        layout = QVBoxLayout(dlg)
        layout.addWidget(QLabel("Select reward(s) to remove:", dlg))
        list_widget = QListWidget(dlg)
        list_widget.setSelectionMode(QListWidget.SelectionMode.MultiSelection)
        for entry in basket_promos:
            code = entry.get("code", "")
            name = entry.get("name", "")
            item = QListWidgetItem(f"{code} â€” {name}")
            item.setData(Qt.ItemDataRole.UserRole, code)
            list_widget.addItem(item)
        layout.addWidget(list_widget)
        button_box = QDialogButtonBox(QDialogButtonBox.StandardButton.Cancel, dlg)
        remove_btn = button_box.addButton("Remove Selected", QDialogButtonBox.ButtonRole.AcceptRole)
        remove_btn.setEnabled(False)
        layout.addWidget(button_box)
        def update_state():
            remove_btn.setEnabled(bool(list_widget.selectedItems()))
        def do_remove():
            selected = list_widget.selectedItems()
            if not selected:
                return
            codes = [item.data(Qt.ItemDataRole.UserRole) for item in selected]
            confirm = QMessageBox.question(
                self,
                "Confirm Removal",
                "Remove the following reward(s)?\n- " + "\n- ".join(codes),
            )
            if confirm != QMessageBox.StandardButton.Yes:
                return
            before = len(basket_promos)
            basket_promos[:] = [entry for entry in basket_promos if entry.get("code") not in codes]
            removed = before - len(basket_promos)
            if removed > 0:
                save_basket_promos(self)
                self.populate_basket_table()
                show_info("Rewards Removed", f"Removed {removed} reward(s).", self)
            dlg.accept()
        list_widget.itemSelectionChanged.connect(update_state)
        remove_btn.clicked.connect(do_remove)
        button_box.rejected.connect(dlg.reject)
        dlg.exec()
    def apply_theme_styles(self):
        tokens = get_theme_tokens()
        self.setStyleSheet(f"""
            QDialog {{
                background-color: {tokens['background']};
                color: {tokens['text']};
            }}
            QLabel#InventoryTitle {{
                font-size: 18px;
                font-weight: 600;
                color: {tokens['title']};
            }}
            QLabel#InventorySubtitle {{
                font-size: 12px;
                color: {tokens['subtitle']};
            }}
            QFrame#InventoryCard, QFrame#ManagementCard {{
                background: {tokens['card_bg']};
                border-radius: 10px;
                border: 1px solid {tokens['card_border']};
            }}
            QTableWidget {{
                border: none;
                gridline-color: {tokens['card_border']};
                background-color: {tokens['table_row_bg']};
                alternate-background-color: {tokens['table_row_alt_bg']};
                color: {tokens['table_text']};
            }}
            QHeaderView::section {{
                background: {tokens['table_header_bg']};
                border: none;
                padding: 8px;
                font-weight: 600;
                color: {tokens['table_header_text']};
            }}
            QPushButton {{
                background-color: {tokens['card_bg']};
                border: 1px solid {tokens['button_outline_border']};
                border-radius: 6px;
                padding: 8px 12px;
                color: {tokens['button_outline_text']};
                font-weight: 600;
            }}
            QPushButton:hover {{
                border-color: {tokens['button_outline_hover_border']};
                color: {tokens['button_primary_hover']};
                background-color: {tokens['button_outline_hover_bg']};
            }}
            QPushButton#AccentButton {{
                background-color: {tokens['button_primary_bg']};
                color: {tokens['button_primary_text']};
                border: none;
            }}
            QPushButton#AccentButton:hover {{
                background-color: {tokens['button_primary_hover']};
            }}
            QTabBar::tab {{
                padding: 8px 16px;
                margin-right: 4px;
            }}
        """)
    def import_excel(self):
        file_path, _ = QFileDialog.getOpenFileName(self, "Import Excel File", "", "Excel Files (*.xlsx *.xls)")
        if file_path:
            try:
                df = pd.read_excel(file_path)
                # Check headers presence
                expected_headers = ["Parent", "Category", "Stock No", "Name", "Available Stocks", "[Z95] - Exibition Warehouse", "Total"]
                if not all(header in df.columns for header in expected_headers):
                    raise ValueError(f"Excel file missing required headers. Expected headers: {expected_headers}")
                updated_count = 0
                ignored_count = 0
                for index, row in df.iterrows():
                    barcode = str(row['Stock No']).strip()
                    z95_stock = row['[Z95] - Exibition Warehouse']  # Extract stock from the 6th column
                    if pd.isna(barcode) or pd.isna(z95_stock):
                        continue
                    try:
                        z95_stock_int = int(z95_stock)  # Convert to integer
                    except Exception:
                        continue
                    if barcode in self.products:
                        # Check if the stock needs to be updated
                        for variant in self.products[barcode]:
                            if variant['stock'] != z95_stock_int:  # Only update if the stock is different
                                variant['stock'] = z95_stock_int
                                updated_count += 1  # Increment updated count only if stock changes
                    else:
                        ignored_count += 1  # Count ignored products
                save_products_to_database(self)  # Persist updated products to MySQL
                self.populate_table()  # Refresh the table
                show_info("Import Successful", f"Stocks updated for {updated_count} products.\nIgnored {ignored_count} products not in current inventory.", self)
            except Exception as e:
                show_error("Import Error", f"Failed to import Excel file: {e}", self)
    def sync_inventory_from_api(self):
        if not ensure_api_settings_loaded(self):
            return
        payload = fetch_inventory_payload(self)
        if payload is None:
            return
        if payload.get("code") not in (200, 201):
            message = payload.get("message") or payload.get("error") or json.dumps(payload)
            show_error("Inventory Sync Failed", f"Inventory endpoint responded with code {payload.get('code')}:\n{message}", self)
            return
        items = ((payload.get("data") or {}).get("items") or [])
        if not items:
            show_info("Inventory Sync", "API response did not include any inventory items.", self)
            return
        preview_rows = []
        diff_found = False
        unmatched_remote = 0
        for entry in items:
            sku = str(entry.get("sku") or "").strip()
            if not sku:
                continue
            try:
                api_stock = int(entry.get("stock"))
            except (TypeError, ValueError):
                continue
            local_stock = None
            if sku in self.products:
                # Sum all variants that share the SKU
                variant_stocks = [variant.get("stock") for variant in self.products.get(sku, [])]
                local_stock = variant_stocks[0] if variant_stocks else 0
                for variant in self.products.get(sku, []):
                    # prefer matching by variant index "stock" field
                    current_stock = variant.get("stock")
                    break
            if local_stock is None:
                unmatched_remote += 1
                preview_rows.append((sku, "—", api_stock, "Not in local catalog", False))
                continue
            if local_stock != api_stock:
                diff_found = True
            preview_rows.append((sku, local_stock, api_stock, "", local_stock != api_stock))
        # Include local entries missing from remote payload
        local_only_rows = []
        for sku in sorted(self.products.keys()):
            if not any(row[0] == sku for row in preview_rows):
                variant = self.products[sku][0] if self.products[sku] else {}
                local_stock = variant.get("stock", 0)
                local_only_rows.append((sku, local_stock, "—", "Missing from API response", False))
        preview_rows.extend(local_only_rows)
        if not preview_rows:
            show_info("Inventory Sync", "No comparable inventory data was found in the API response.", self)
            return
        dialog = QDialog(self)
        dialog.setWindowTitle("Inventory Sync Preview")
        dialog.resize(720, 520)
        layout = QVBoxLayout(dialog)
        summary_label = QLabel(
            "Review the differences below. Items highlighted will be updated if you proceed."
        )
        layout.addWidget(summary_label)
        table = QTableWidget(dialog)
        table.setColumnCount(4)
        table.setHorizontalHeaderLabels(["Stock No.", "Local Stock", "API Stock", "Notes"])
        table.horizontalHeader().setSectionResizeMode(QHeaderView.ResizeMode.Stretch)
        table.setRowCount(len(preview_rows))
        for row_index, row_data in enumerate(preview_rows):
            sku, local_val, api_val, note, is_diff = row_data
            local_text = "—" if local_val == "—" else f"{local_val}"
            api_text = "—" if api_val == "—" else f"{api_val}"
            table.setItem(row_index, 0, QTableWidgetItem(sku))
            table.setItem(row_index, 1, QTableWidgetItem(local_text))
            table.setItem(row_index, 2, QTableWidgetItem(api_text))
            table.setItem(row_index, 3, QTableWidgetItem(note))
            if is_diff:
                for col in range(4):
                    item = table.item(row_index, col)
                    if item:
                        item.setBackground(QColor("#fff3cd"))
        table.verticalHeader().setVisible(False)
        table.setEditTriggers(QTableWidget.EditTrigger.NoEditTriggers)
        layout.addWidget(table)
        button_box = QDialogButtonBox(QDialogButtonBox.StandardButton.Cancel | QDialogButtonBox.StandardButton.Ok)
        button_box.button(QDialogButtonBox.StandardButton.Ok).setText("Sync Now")
        layout.addWidget(button_box)
        proceed = {"value": False}
        def accept():
            proceed["value"] = True
            dialog.accept()
        button_box.accepted.connect(accept)
        button_box.rejected.connect(dialog.reject)
        # Log preview action
        parent = self.parent()
        if parent and hasattr(parent, "log_user_action"):
            parent.log_user_action(
                "Previewed inventory sync",
                f"{len(preview_rows)} items compared; {unmatched_remote} not in local catalog",
            )
        dialog.exec()
        if not proceed["value"]:
            return
        updated_count = 0
        ignored_count = 0
        for entry in items:
            sku = str(entry.get("sku") or "").strip()
            if not sku:
                continue
            stock_value = entry.get("stock")
            try:
                stock_int = int(stock_value)
            except (TypeError, ValueError):
                continue
            if sku in self.products:
                for variant in self.products[sku]:
                    if variant.get("stock") != stock_int:
                        variant["stock"] = stock_int
                        if variant.get("original_stock", 0) < stock_int:
                            variant["original_stock"] = stock_int
                        updated_count += 1
            else:
                ignored_count += 1
        if updated_count == 0 and ignored_count == 0:
            show_info("Inventory Sync", "No local products were matched to the API response.", self)
            return
        save_products_to_database(self)
        rebuild_product_variant_lookup()
        parent = self.parent()
        if parent and hasattr(parent, "refresh_product_search_options"):
            parent.refresh_product_search_options()
        if parent and hasattr(parent, "clear_product_display"):
            parent.clear_product_display()
        self.populate_table()
        show_info(
            "Inventory Sync",
            f"Stocks updated for {updated_count} product variant(s).\nIgnored {ignored_count} item(s) not found in the local catalog.",
            self,
        )
        if api_settings.get("use_inventory_stub"):
            show_info(
                "Stub Data Used",
                "Inventory sync loaded stub data. Disable 'use_inventory_stub' in api_settings.json to call the live API.",
                self,
            )
    def export_summary(self):
        file_path, _ = QFileDialog.getSaveFileName(self, "Export Summary as Excel", "", "Excel Files (*.xlsx *.xls)")
        if not file_path:
            return
        try:
            rows = []
            for barcode, variants in self.products.items():
                for variant in variants:
                    starting_stock = variant.get('original_stock', variant.get('stock', 0))  # Use original stock
                    sold = sales_summary.get(barcode, {}).get('qty_sold', 0)
                    expected_stock = starting_stock - sold
                    code_value = variant.get("code") or ""
                    row_data = {
                        "Parent": "",
                        "Category": "",
                        "Stock No": barcode,
                        "Code": code_value,
                        "Name": variant['name'],
                        "[Z95] - Exibition Warehouse": starting_stock,
                        "Sold": sold,
                        "Expected Stocks": expected_stock,
                        "Available Stocks": variant['stock']
                    }
                    rows.append(row_data)
            columns = [
                "Parent",
                "Category",
                "Stock No",
                "Code",
                "Name",
                "[Z95] - Exibition Warehouse",
                "Sold",
                "Expected Stocks",
                "Available Stocks",
            ]
            df = pd.DataFrame(rows, columns=columns)
            df.to_excel(file_path, index=False)
            show_info("Export Successful", "Inventory summary has been exported successfully.", self)
        except Exception as e:
            show_error("Export Error", f"Failed to export summary: {e}", self)


class AddProductDialog(QDialog):
    def __init__(self, next_product_id, suggested_stock_no="", parent=None):
        super().__init__(parent)
        self.setWindowTitle("Add Inventory Item")
        self._result = None
        layout = QVBoxLayout(self)
        layout.setContentsMargins(20, 20, 20, 20)
        layout.setSpacing(12)
        info = QLabel(f"Next Product ID will be {next_product_id}")
        info.setObjectName("InventorySubtitle")
        layout.addWidget(info)
        form = QFormLayout()
        form.setLabelAlignment(Qt.AlignmentFlag.AlignRight)
        self.stock_input = QLineEdit()
        self.stock_input.setPlaceholderText("Unique stock number / barcode")
        if suggested_stock_no:
            self.stock_input.setText(suggested_stock_no)
        form.addRow("Stock No.", self.stock_input)
        self.code_input = QLineEdit()
        self.code_input.setPlaceholderText("Shorthand code (optional, e.g., A21)")
        form.addRow("Code", self.code_input)
        self.name_input = QLineEdit()
        self.name_input.setPlaceholderText("Product name")
        form.addRow("Name", self.name_input)
        self.price_input = QDoubleSpinBox()
        self.price_input.setDecimals(2)
        self.price_input.setMinimum(0.0)
        self.price_input.setMaximum(9_999_999.99)
        self.price_input.setPrefix("P")
        form.addRow("Price", self.price_input)
        self.quantity_spin = QSpinBox()
        self.quantity_spin.setRange(0, 1_000_000)
        form.addRow("Stock Qty", self.quantity_spin)
        layout.addLayout(form)
        button_box = QDialogButtonBox(
            QDialogButtonBox.StandardButton.Save | QDialogButtonBox.StandardButton.Cancel
        )
        save_btn = button_box.button(QDialogButtonBox.StandardButton.Save)
        save_btn.setText("Add Product")
        button_box.accepted.connect(self._handle_accept)
        button_box.rejected.connect(self.reject)
        layout.addWidget(button_box)

    def _handle_accept(self):
        stock_no = self.stock_input.text().strip()
        code_value = normalize_product_code(self.code_input.text())
        name = self.name_input.text().strip()
        price = float(self.price_input.value())
        stock_qty = int(self.quantity_spin.value())
        if not stock_no:
            show_error("Missing Stock Number", "Stock number is required.", self)
            return
        if not name:
            show_error("Missing Product Name", "Product name is required.", self)
            return
        self._result = {
            "stock_no": stock_no,
            "code": code_value,
            "name": name,
            "price": price,
            "stock": stock_qty,
        }
        self.accept()

    def get_values(self):
        return self._result


class PromoManagementDialog(QDialog):
    def __init__(self, products_ref, parent=None):
        super().__init__(parent)
        self.setWindowTitle("Promo Management")
        self.resize(900, 600)
        self.products = products_ref
        self.row_widgets = []
        main_layout = QVBoxLayout(self)
        info_label = QLabel("Create or update promos, assign them to products, and set unit usage in one place.")
        info_label.setWordWrap(True)
        main_layout.addWidget(info_label)
        form_layout = QGridLayout()
        main_layout.addLayout(form_layout)
        lbl_code = QLabel("Promo Code:")
        form_layout.addWidget(lbl_code, 0, 0)
        self.promo_code_combo = QComboBox()
        self.promo_code_combo.setEditable(True)
        self.promo_code_combo.lineEdit().setPlaceholderText("e.g., B3T1")
        existing_codes = sorted({code for code in product_promo_columns if code} | {code for code in promo_inventory_map if code})
        for code in existing_codes:
            self.promo_code_combo.addItem(code)
        form_layout.addWidget(self.promo_code_combo, 0, 1)
        self.btn_new_promo = QPushButton("New Promo")
        self.btn_new_promo.clicked.connect(self.clear_form)
        form_layout.addWidget(self.btn_new_promo, 0, 2)
        lbl_units = QLabel("Units Per Sale:")
        form_layout.addWidget(lbl_units, 1, 0)
        self.units_spin = QSpinBox()
        self.units_spin.setRange(1, 10000)
        form_layout.addWidget(self.units_spin, 1, 1)
        search_layout = QHBoxLayout()
        search_layout.addWidget(QLabel("Search Products:"))
        self.search_edit = QLineEdit()
        self.search_edit.setPlaceholderText("Type stock number or product name to filter…")
        search_layout.addWidget(self.search_edit, stretch=1)
        main_layout.addLayout(search_layout)
        self.table = QTableWidget()
        self.table.setColumnCount(5)
        self.table.setHorizontalHeaderLabels(["Include", "Stock No.", "Product Name", "Base Price", "Promo Price"])
        self.table.verticalHeader().setVisible(False)
        self.table.setAlternatingRowColors(True)
        self.table.setSelectionMode(QTableWidget.SelectionMode.NoSelection)
        main_layout.addWidget(self.table)
        self.product_rows = []
        for barcode in sorted(self.products.keys()):
            variants = self.products[barcode]
            for index, variant in enumerate(variants):
                self.product_rows.append((barcode, index, variant))
        self.table.setRowCount(len(self.product_rows))
        header = self.table.horizontalHeader()
        header.setSectionResizeMode(0, QHeaderView.ResizeMode.Fixed)
        header.setSectionResizeMode(1, QHeaderView.ResizeMode.ResizeToContents)
        header.setSectionResizeMode(2, QHeaderView.ResizeMode.Stretch)
        header.setSectionResizeMode(3, QHeaderView.ResizeMode.ResizeToContents)
        header.setSectionResizeMode(4, QHeaderView.ResizeMode.ResizeToContents)
        self.table.setColumnWidth(0, 80)
        for row, (barcode, index, variant) in enumerate(self.product_rows):
            checkbox = QCheckBox()
            checkbox.setToolTip("Toggle to include this product in the promo.")
            checkbox.setStyleSheet("margin-left: 25px; margin-right: 25px;")
            self.table.setCellWidget(row, 0, checkbox)
            stock_item = QTableWidgetItem(barcode)
            stock_item.setFlags(Qt.ItemFlag.ItemIsSelectable | Qt.ItemFlag.ItemIsEnabled)
            self.table.setItem(row, 1, stock_item)
            name = variant.get('name', '')
            if len(self.products.get(barcode, [])) > 1:
                name = f"{name} (Variant {index + 1})"
            name_item = QTableWidgetItem(name)
            name_item.setFlags(Qt.ItemFlag.ItemIsSelectable | Qt.ItemFlag.ItemIsEnabled)
            self.table.setItem(row, 2, name_item)
            base_price = float(variant.get('price', 0))
            base_item = QTableWidgetItem(f"{base_price:.2f}")
            base_item.setTextAlignment(Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignVCenter)
            base_item.setFlags(Qt.ItemFlag.ItemIsSelectable | Qt.ItemFlag.ItemIsEnabled)
            self.table.setItem(row, 3, base_item)
            price_spin = QDoubleSpinBox()
            price_spin.setDecimals(2)
            price_spin.setRange(0.0, 9999999.99)
            price_spin.setSingleStep(1.0)
            price_spin.setValue(base_price)
            price_spin.setEnabled(False)
            price_spin.setProperty("promo_custom", False)
            self.table.setCellWidget(row, 4, price_spin)
            checkbox.toggled.connect(partial(self.handle_checkbox_toggled, price_spin, base_price))
            price_spin.valueChanged.connect(partial(self.mark_price_custom, price_spin))
            self.row_widgets.append((barcode, index, checkbox, price_spin, base_price))
        button_box = QDialogButtonBox(QDialogButtonBox.StandardButton.Save | QDialogButtonBox.StandardButton.Cancel)
        button_box.accepted.connect(self.handle_save)
        button_box.rejected.connect(self.reject)
        main_layout.addWidget(button_box)
        self.promo_code_combo.currentTextChanged.connect(self.load_promo_data)
        self.units_spin.valueChanged.connect(self.handle_units_changed)
        self.search_edit.textChanged.connect(self.apply_filter)
        self.load_promo_data(self.promo_code_combo.currentText())
        self.apply_filter(self.search_edit.text())
    def clear_form(self):
        self.promo_code_combo.blockSignals(True)
        self.promo_code_combo.setCurrentIndex(-1)
        self.promo_code_combo.setEditText("")
        self.promo_code_combo.blockSignals(False)
        self.units_spin.blockSignals(True)
        self.units_spin.setValue(1)
        self.units_spin.blockSignals(False)
        self.load_promo_data("")
        self.promo_code_combo.lineEdit().setFocus()
    def compute_default_promo_price(self, base_price):
        units = max(1, self.units_spin.value())
        if units <= 1:
            return round(base_price, 2)
        return round(base_price * max(1, units - 1), 2)
    def handle_checkbox_toggled(self, price_spin, base_price, checked):
        price_spin.setEnabled(checked)
        if checked:
            auto_price = self.compute_default_promo_price(base_price)
            price_spin.blockSignals(True)
            price_spin.setValue(auto_price)
            price_spin.blockSignals(False)
            price_spin.setProperty("promo_custom", False)
        else:
            price_spin.blockSignals(True)
            price_spin.setValue(base_price)
            price_spin.blockSignals(False)
            price_spin.setProperty("promo_custom", False)
    def handle_units_changed(self, _value):
        for _, _, checkbox, price_spin, base_price in self.row_widgets:
            if checkbox.isChecked() and not price_spin.property("promo_custom"):
                auto_price = self.compute_default_promo_price(base_price)
                price_spin.blockSignals(True)
                price_spin.setValue(auto_price)
                price_spin.blockSignals(False)
    def mark_price_custom(self, price_spin, _value):
        if price_spin.isEnabled() and price_spin.hasFocus():
            price_spin.setProperty("promo_custom", True)
    def apply_filter(self, text):
        terms = [term for term in (text or "").lower().split() if term]
        for row, (barcode, index, variant) in enumerate(self.product_rows):
            variant_name = variant.get("name", "")
            variant_label = variant_name
            if len(self.products.get(barcode, [])) > 1:
                variant_label = f"{variant_name} (variant {index + 1})"
            haystack = f"{barcode} {variant_name} {variant_label}".lower()
            matches = all(term in haystack for term in terms)
            self.table.setRowHidden(row, not matches)
    def load_promo_data(self, promo_code):
        promo_code = (promo_code or "").strip()
        units_value = promo_inventory_map.get(promo_code, 1)
        try:
            units_value = int(units_value)
        except (ValueError, TypeError):
            units_value = 1
        target_units = max(1, units_value)
        self.units_spin.blockSignals(True)
        self.units_spin.setValue(target_units)
        self.units_spin.blockSignals(False)
        for barcode, index, checkbox, price_spin, base_price in self.row_widgets:
            variant = self.products.get(barcode, [])[index]
            existing_price = None
            promos = variant.get('promos') or {}
            if promo_code:
                existing_price = promos.get(promo_code)
            price_spin.blockSignals(True)
            price_spin.setValue(float(base_price))
            price_spin.blockSignals(False)
            price_spin.setProperty("promo_custom", False)
            checkbox.blockSignals(True)
            checkbox.setChecked(False)
            checkbox.blockSignals(False)
            price_spin.setEnabled(False)
            if existing_price not in (None, "") and promo_code:
                try:
                    price_val = float(existing_price)
                except (TypeError, ValueError):
                    price_val = self.compute_default_promo_price(base_price)
                price_spin.blockSignals(True)
                price_spin.setValue(price_val)
                price_spin.blockSignals(False)
                checkbox.blockSignals(True)
                checkbox.setChecked(True)
                checkbox.blockSignals(False)
                price_spin.setEnabled(True)
                auto_price = self.compute_default_promo_price(base_price)
                if abs(price_val - auto_price) >= 0.01:
                    price_spin.setProperty("promo_custom", True)
    def handle_save(self):
        promo_code = self.promo_code_combo.currentText().strip()
        if not promo_code:
            show_error("Validation Error", "Please enter a promo code before saving.", self)
            return
        if not re.fullmatch(r"[A-Za-z0-9_\\-]+", promo_code):
            show_error("Validation Error", "Promo code can only contain letters, numbers, underscores, and hyphens.", self)
            return
        promo_code = promo_code.upper()
        self.promo_code_combo.setEditText(promo_code)
        units_per_sale = self.units_spin.value()
        selected_entries = {}
        for barcode, index, checkbox, price_spin, _ in self.row_widgets:
            if checkbox.isChecked():
                price = float(price_spin.value())
                if price <= 0:
                    show_error("Validation Error", f"Promo price must be greater than zero for product '{barcode}'.", self)
                    return
                selected_entries[(barcode, index)] = round(price, 2)
        if not selected_entries:
            show_error("Validation Error", "Select at least one product to apply the promo.", self)
            return
        global product_promo_columns, promo_inventory_map
        if promo_code not in product_promo_columns:
            product_promo_columns.append(promo_code)
        promo_inventory_map[promo_code] = units_per_sale
        for barcode, variants in self.products.items():
            for idx, variant in enumerate(variants):
                promos = variant.setdefault('promos', {})
                key = (barcode, idx)
                if key in selected_entries:
                    promos[promo_code] = selected_entries[key]
                else:
                    promos.pop(promo_code, None)
        save_products_to_database(self)
        save_promo_inventory(self)
        rebuild_product_variant_lookup()
        if promo_code not in {self.promo_code_combo.itemText(i) for i in range(self.promo_code_combo.count())}:
            self.promo_code_combo.addItem(promo_code)
        show_info("Promo Saved", f"Promo '{promo_code}' has been saved successfully.", self)
        self.accept()
class BundlePromoDialog(QDialog):
    def __init__(self, products_ref, parent=None):
        super().__init__(parent)
        self.setWindowTitle("Bundle Promotions")
        self.resize(950, 620)
        self.products = products_ref
        self.row_widgets = []
        self.bundle_image_filename = ""
        self.bundle_image_source_path = None
        main_layout = QVBoxLayout(self)
        info_label = QLabel(
            "Create bundles that sell multiple products at a single promo price. "
            "Adjust quantities per item and set the bundle price; stock updates will deduct from each component."
        )
        info_label.setWordWrap(True)
        main_layout.addWidget(info_label)
        header_layout = QGridLayout()
        main_layout.addLayout(header_layout)
        header_layout.addWidget(QLabel("Bundle Code:"), 0, 0)
        self.bundle_code_combo = QComboBox()
        self.bundle_code_combo.setEditable(True)
        self.bundle_code_combo.lineEdit().setPlaceholderText("e.g., WKND_SET")
        for code in sorted(bundle_promos.keys()):
            self.bundle_code_combo.addItem(code)
        header_layout.addWidget(self.bundle_code_combo, 0, 1)
        self.btn_new_bundle = QPushButton("New Bundle")
        self.btn_new_bundle.clicked.connect(self.clear_form)
        header_layout.addWidget(self.btn_new_bundle, 0, 2)
        self.btn_delete_bundle = QPushButton("Delete Bundle")
        self.btn_delete_bundle.clicked.connect(self.delete_bundle)
        header_layout.addWidget(self.btn_delete_bundle, 0, 3)
        header_layout.addWidget(QLabel("Bundle Name:"), 1, 0)
        self.bundle_name_edit = QLineEdit()
        self.bundle_name_edit.setPlaceholderText("Display name shown in POS (optional)")
        header_layout.addWidget(self.bundle_name_edit, 1, 1, 1, 3)
        header_layout.addWidget(QLabel("Bundle Price:"), 2, 0)
        self.bundle_price_spin = QDoubleSpinBox()
        self.bundle_price_spin.setDecimals(2)
        self.bundle_price_spin.setRange(0.0, 9999999.99)
        self.bundle_price_spin.setSingleStep(1.0)
        self.bundle_price_spin.setProperty("custom_edit", False)
        self.bundle_price_spin.valueChanged.connect(self.mark_bundle_price_custom)
        header_layout.addWidget(self.bundle_price_spin, 2, 1)
        self.bundle_base_total_label = QLabel("Base total: P0.00")
        header_layout.addWidget(self.bundle_base_total_label, 2, 2, 1, 2)
        image_row = QHBoxLayout()
        image_row.setSpacing(12)
        self.bundle_image_label = QLabel("No Image")
        self.bundle_image_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.bundle_image_label.setFixedSize(160, 120)
        self.bundle_image_label.setStyleSheet("border: 1px dashed #94a3b8; background-color: #f8fafc;")
        image_row.addWidget(self.bundle_image_label)
        controls_col = QVBoxLayout()
        self.bundle_image_file_label = QLabel("No image selected")
        controls_col.addWidget(self.bundle_image_file_label)
        self.btn_select_bundle_image = QPushButton("Choose Image")
        self.btn_select_bundle_image.clicked.connect(self.choose_bundle_image)
        controls_col.addWidget(self.btn_select_bundle_image)
        image_row.addLayout(controls_col)
        header_layout.addLayout(image_row, 3, 0, 1, 4)
        search_layout = QHBoxLayout()
        search_layout.addWidget(QLabel("Search Products:"))
        self.search_edit = QLineEdit()
        self.search_edit.setPlaceholderText("Type stock number or name to filter bundle components…")
        search_layout.addWidget(self.search_edit, stretch=1)
        main_layout.addLayout(search_layout)
        self.table = QTableWidget()
        self.table.setColumnCount(5)
        self.table.setHorizontalHeaderLabels(["Qty", "Stock No.", "Product Name", "Base Price", "Total"])
        self.table.setAlternatingRowColors(True)
        self.table.setSelectionMode(QTableWidget.SelectionMode.NoSelection)
        main_layout.addWidget(self.table)
        self.product_rows = []
        for barcode in sorted(self.products.keys()):
            variants = self.products[barcode]
            for index, variant in enumerate(variants):
                self.product_rows.append((barcode, index, variant))
        self.table.setRowCount(len(self.product_rows))
        header = self.table.horizontalHeader()
        header.setSectionResizeMode(0, QHeaderView.ResizeMode.ResizeToContents)
        header.setSectionResizeMode(1, QHeaderView.ResizeMode.ResizeToContents)
        header.setSectionResizeMode(2, QHeaderView.ResizeMode.Stretch)
        header.setSectionResizeMode(3, QHeaderView.ResizeMode.ResizeToContents)
        header.setSectionResizeMode(4, QHeaderView.ResizeMode.ResizeToContents)
        for row, (barcode, index, variant) in enumerate(self.product_rows):
            qty_spin = QSpinBox()
            qty_spin.setRange(0, 999)
            qty_spin.valueChanged.connect(partial(self.handle_quantity_changed, row))
            self.table.setCellWidget(row, 0, qty_spin)
            stock_item = QTableWidgetItem(barcode)
            stock_item.setFlags(Qt.ItemFlag.ItemIsSelectable | Qt.ItemFlag.ItemIsEnabled)
            self.table.setItem(row, 1, stock_item)
            name = variant.get('name', '')
            if len(self.products.get(barcode, [])) > 1:
                name = f"{name} (Variant {index + 1})"
            name_item = QTableWidgetItem(name)
            name_item.setFlags(Qt.ItemFlag.ItemIsSelectable | Qt.ItemFlag.ItemIsEnabled)
            self.table.setItem(row, 2, name_item)
            base_price = float(variant.get('price', 0))
            base_item = QTableWidgetItem(f"{base_price:.2f}")
            base_item.setTextAlignment(Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignVCenter)
            base_item.setFlags(Qt.ItemFlag.ItemIsSelectable | Qt.ItemFlag.ItemIsEnabled)
            self.table.setItem(row, 3, base_item)
            total_item = QTableWidgetItem("0.00")
            total_item.setTextAlignment(Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignVCenter)
            total_item.setFlags(Qt.ItemFlag.ItemIsSelectable | Qt.ItemFlag.ItemIsEnabled)
            self.table.setItem(row, 4, total_item)
            self.row_widgets.append({
                "row": row,
                "barcode": barcode,
                "variant_index": index,
                "qty_spin": qty_spin,
                "base_price": base_price
            })
        button_box = QDialogButtonBox(
            QDialogButtonBox.StandardButton.Save | QDialogButtonBox.StandardButton.Cancel
        )
        button_box.accepted.connect(self.handle_save)
        button_box.rejected.connect(self.reject)
        main_layout.addWidget(button_box)
        self.bundle_code_combo.currentTextChanged.connect(self.load_bundle_data)
        self.search_edit.textChanged.connect(self.apply_filter)
        self.load_bundle_data(self.bundle_code_combo.currentText())
        self.apply_filter(self.search_edit.text())
        self.apply_theme_styles()
    def clear_form(self):
        self.bundle_code_combo.blockSignals(True)
        self.bundle_code_combo.setCurrentIndex(-1)
        self.bundle_code_combo.setEditText("")
        self.bundle_code_combo.blockSignals(False)
        self.bundle_name_edit.clear()
        self.bundle_price_spin.blockSignals(True)
        self.bundle_price_spin.setValue(0.0)
        self.bundle_price_spin.blockSignals(False)
        self.bundle_price_spin.setProperty("custom_edit", False)
        self.bundle_image_filename = ""
        self.bundle_image_source_path = None
        self.update_bundle_image_preview()
        for row_info in self.row_widgets:
            row_info["qty_spin"].blockSignals(True)
            row_info["qty_spin"].setValue(0)
            row_info["qty_spin"].blockSignals(False)
            self.table.item(row_info["row"], 4).setText("0.00")
            self.set_row_highlight(row_info["row"], False)
        self.update_base_total()
        self.bundle_code_combo.lineEdit().setFocus()
    def handle_quantity_changed(self, row_index, value):
        row_info = self.row_widgets[row_index]
        total_value = value * row_info["base_price"]
        self.table.item(row_index, 4).setText(f"{total_value:.2f}")
        self.set_row_highlight(row_index, value > 0)
        base_total = self.update_base_total()
        if not self.bundle_price_spin.property("custom_edit"):
            self.bundle_price_spin.blockSignals(True)
            self.bundle_price_spin.setValue(base_total)
            self.bundle_price_spin.blockSignals(False)
    def set_row_highlight(self, row, enabled):
        color = QColor("#FFF0C2") if enabled else QColor(Qt.GlobalColor.white)
        for col in range(1, 5):
            item = self.table.item(row, col)
            if item:
                item.setBackground(color)
    def update_base_total(self):
        total = 0.0
        for row_info in self.row_widgets:
            qty = row_info["qty_spin"].value()
            if qty > 0:
                total += qty * row_info["base_price"]
        self.bundle_base_total_label.setText(f"Base total: P{total:,.2f}")
        return round(total, 2)
    def mark_bundle_price_custom(self, _value):
        if self.bundle_price_spin.hasFocus():
            self.bundle_price_spin.setProperty("custom_edit", True)
    def apply_filter(self, text):
        terms = [term for term in (text or "").lower().split() if term]
        for row, (barcode, index, variant) in enumerate(self.product_rows):
            variant_name = variant.get("name", "")
            variant_label = variant_name
            if len(self.products.get(barcode, [])) > 1:
                variant_label = f"{variant_name} (variant {index + 1})"
            haystack = f"{barcode} {variant_name} {variant_label}".lower()
            matches = all(term in haystack for term in terms)
            self.table.setRowHidden(row, not matches)
    def update_bundle_image_preview(self, source_path=None, filename=None):
        path = None
        if source_path and os.path.exists(source_path):
            path = source_path
        elif filename:
            candidate = os.path.join(PRODUCT_IMAGE_FOLDER, filename)
            if os.path.exists(candidate):
                path = candidate
        if path:
            pixmap = QPixmap(path).scaled(
                self.bundle_image_label.size(), Qt.AspectRatioMode.KeepAspectRatio, Qt.TransformationMode.SmoothTransformation
            )
            self.bundle_image_label.setPixmap(pixmap)
            self.bundle_image_label.setText("")
            self.bundle_image_file_label.setText(os.path.basename(path))
        else:
            self.bundle_image_label.clear()
            self.bundle_image_label.setText("No Image")
            self.bundle_image_file_label.setText("No image selected")
    def choose_bundle_image(self):
        file_path, _ = QFileDialog.getOpenFileName(self, "Select Bundle Image", "", "Images (*.png *.jpg *.jpeg *.bmp)")
        if not file_path:
            return
        self.bundle_image_source_path = file_path
        self.update_bundle_image_preview(source_path=file_path)
    def load_bundle_data(self, bundle_code):
        bundle_code = (bundle_code or "").strip()
        bundle = bundle_promos.get(bundle_code, {})
        self.bundle_name_edit.setText(bundle.get("name", ""))
        self.bundle_price_spin.blockSignals(True)
        self.bundle_price_spin.setValue(float(bundle.get("price", 0)))
        self.bundle_price_spin.blockSignals(False)
        self.bundle_price_spin.setProperty("custom_edit", False)
        self.bundle_image_filename = bundle.get("image_filename", "")
        self.bundle_image_source_path = None
        self.update_bundle_image_preview(filename=self.bundle_image_filename)
        component_map = {}
        for component in bundle.get("components", []):
            key = (component.get("barcode"), component.get("variant_index", 0))
            component_map[key] = component.get("quantity", 0)
        for row_info in self.row_widgets:
            key = (row_info["barcode"], row_info["variant_index"])
            quantity = component_map.get(key, 0)
            row_info["qty_spin"].blockSignals(True)
            row_info["qty_spin"].setValue(quantity)
            row_info["qty_spin"].blockSignals(False)
            self.table.item(row_info["row"], 4).setText(f"{quantity * row_info['base_price']:.2f}")
            self.set_row_highlight(row_info["row"], quantity > 0)
        base_total = self.update_base_total()
        if abs(self.bundle_price_spin.value() - base_total) < 0.01:
            self.bundle_price_spin.setProperty("custom_edit", False)
    def delete_bundle(self):
        global bundle_promos
        bundle_code = self.bundle_code_combo.currentText().strip()
        if not bundle_code:
            show_warning("Delete Bundle", "Select a bundle code to delete.", self)
            return
        if bundle_code not in bundle_promos:
            show_warning("Delete Bundle", f"Bundle '{bundle_code}' does not exist.", self)
            return
        confirm = QMessageBox.question(
            self,
            "Delete Bundle",
            f"Are you sure you want to delete bundle '{bundle_code}'?",
            QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
            QMessageBox.StandardButton.No
        )
        if confirm != QMessageBox.StandardButton.Yes:
            return
        bundle_promos.pop(bundle_code, None)
        save_bundle_promos(self)
        rebuild_product_variant_lookup()
        idx = self.bundle_code_combo.findText(bundle_code)
        if idx != -1:
            self.bundle_code_combo.removeItem(idx)
        show_info("Bundle Deleted", f"Bundle '{bundle_code}' has been removed.", self)
        self.clear_form()
    def handle_save(self):
        global bundle_promos
        bundle_code = self.bundle_code_combo.currentText().strip()
        if not bundle_code:
            show_error("Validation Error", "Enter a bundle code before saving.", self)
            return
        if not re.fullmatch(r"[A-Za-z0-9_\\-]+", bundle_code):
            show_error(
                "Validation Error",
                "Bundle code can only contain letters, numbers, underscores, and hyphens.",
                self
            )
            return
        bundle_code = bundle_code.upper()
        self.bundle_code_combo.setEditText(bundle_code)
        selected_components = []
        for row_info in self.row_widgets:
            quantity = row_info["qty_spin"].value()
            if quantity <= 0:
                continue
            selected_components.append({
                "barcode": row_info["barcode"],
                "variant_index": row_info["variant_index"],
                "quantity": quantity
            })
        if not selected_components:
            show_error("Validation Error", "Select at least one product for the bundle.", self)
            return
        bundle_price = float(self.bundle_price_spin.value())
        if bundle_price <= 0:
            show_error("Validation Error", "Bundle price must be greater than zero.", self)
            return
        bundle_name = self.bundle_name_edit.text().strip() or f"Bundle {bundle_code}"
        sku = bundle_code
        image_filename = self.bundle_image_filename or ""
        if self.bundle_image_source_path:
            new_filename = copy_image_to_library(self.bundle_image_source_path, f"bundle_{bundle_code}", self)
            if new_filename:
                image_filename = new_filename
                self.bundle_image_source_path = None
        self.bundle_image_filename = image_filename
        bundle_promos[bundle_code] = {
            "code": bundle_code,
            "name": bundle_name,
            "price": round(bundle_price, 2),
            "components": selected_components,
            "sku": sku,
            "image_filename": image_filename,
        }
        save_bundle_promos(self)
        rebuild_product_variant_lookup()
        if self.bundle_code_combo.findText(bundle_code) == -1:
            self.bundle_code_combo.addItem(bundle_code)
        show_info("Bundle Saved", f"Bundle '{bundle_code}' saved successfully.", self)
        self.accept()
    def apply_theme_styles(self):
        tokens = get_theme_tokens()
        self.setStyleSheet(f"""
            QDialog {{
                background-color: {tokens['background']};
                color: {tokens['text']};
            }}
            QLabel {{
                color: {tokens['text']};
            }}
            QLineEdit, QDoubleSpinBox {{
                padding: 6px 8px;
                border: 1px solid {tokens['input_border']};
                border-radius: 4px;
                background-color: {tokens['input_bg']};
                color: {tokens['input_text']};
            }}
            QLineEdit:focus, QDoubleSpinBox:focus {{
                border: 1px solid {tokens['button_primary_bg']};
            }}
            QTableWidget {{
                border: 1px solid {tokens['card_border']};
                background-color: {tokens['table_row_bg']};
                color: {tokens['table_text']};
            }}
            QHeaderView::section {{
                background: {tokens['table_header_bg']};
                color: {tokens['table_header_text']};
                border: none;
                padding: 6px;
            }}
            QPushButton {{
                background-color: {tokens['card_bg']};
                border: 1px solid {tokens['button_outline_border']};
                border-radius: 4px;
                padding: 6px 10px;
                color: {tokens['button_outline_text']};
            }}
            QPushButton:hover {{
                border-color: {tokens['button_outline_hover_border']};
                background-color: {tokens['button_outline_hover_bg']};
            }}
        """)
class BasketPromoDialog(QDialog):
    def __init__(self, products_ref, parent=None):
        super().__init__(parent)
        self.setWindowTitle("Basket Rewards Management")
        self.resize(760, 620)
        self.products = products_ref
        self.current_code = None
        main_layout = QVBoxLayout(self)
        info_label = QLabel("Configure basket-size reward tiers that grant freebies once an order reaches a chosen subtotal.")
        info_label.setWordWrap(True)
        main_layout.addWidget(info_label)
        selector_layout = QHBoxLayout()
        main_layout.addLayout(selector_layout)
        selector_layout.addWidget(QLabel("Existing Tiers:"))
        self.tier_combo = QComboBox()
        selector_layout.addWidget(self.tier_combo, stretch=1)
        self.btn_new = QPushButton("New Tier")
        self.btn_new.clicked.connect(self.clear_form)
        selector_layout.addWidget(self.btn_new)
        self.btn_delete = QPushButton("Delete Tier")
        self.btn_delete.clicked.connect(self.delete_tier)
        selector_layout.addWidget(self.btn_delete)
        form_layout = QGridLayout()
        main_layout.addLayout(form_layout)
        form_layout.addWidget(QLabel("Tier Code:"), 0, 0)
        self.code_edit = QLineEdit()
        self.code_edit.setPlaceholderText("e.g., BASKET500")
        form_layout.addWidget(self.code_edit, 0, 1)
        form_layout.addWidget(QLabel("Tier Name:"), 1, 0)
        self.name_edit = QLineEdit()
        self.name_edit.setPlaceholderText("Friendly description (optional)")
        form_layout.addWidget(self.name_edit, 1, 1)
        form_layout.addWidget(QLabel("Threshold Amount (â‚±):"), 2, 0)
        self.threshold_spin = QDoubleSpinBox()
        self.threshold_spin.setRange(0.0, 1_000_000_000.0)
        self.threshold_spin.setDecimals(2)
        self.threshold_spin.setSingleStep(50.0)
        form_layout.addWidget(self.threshold_spin, 2, 1)
        form_layout.addWidget(QLabel("Receipt Message:"), 3, 0)
        self.message_edit = QLineEdit()
        self.message_edit.setPlaceholderText("Optional thank-you note that appears on receipts")
        form_layout.addWidget(self.message_edit, 3, 1)
        freebies_label = QLabel("Reward Items:")
        freebies_label.setFont(QFont("Arial", 11, QFont.Weight.Bold))
        main_layout.addWidget(freebies_label)
        self.freebie_table = QTableWidget(0, 4, self)
        self.freebie_table.setHorizontalHeaderLabels(["Stock No.", "Variant", "Product Name", "Quantity"])
        self.freebie_table.verticalHeader().setVisible(False)
        self.freebie_table.setSelectionBehavior(QTableWidget.SelectionBehavior.SelectRows)
        self.freebie_table.setSelectionMode(QTableWidget.SelectionMode.SingleSelection)
        header = self.freebie_table.horizontalHeader()
        header.setSectionResizeMode(0, QHeaderView.ResizeMode.ResizeToContents)
        header.setSectionResizeMode(1, QHeaderView.ResizeMode.ResizeToContents)
        header.setSectionResizeMode(2, QHeaderView.ResizeMode.Stretch)
        header.setSectionResizeMode(3, QHeaderView.ResizeMode.ResizeToContents)
        main_layout.addWidget(self.freebie_table)
        add_layout = QHBoxLayout()
        main_layout.addLayout(add_layout)
        add_layout.addWidget(QLabel("Add Reward Item:"))
        variant_selector = QVBoxLayout()
        self.variant_search_edit = QLineEdit()
        self.variant_search_edit.setPlaceholderText("Search stock no. or product name…")
        variant_selector.addWidget(self.variant_search_edit)
        self.variant_combo = QComboBox()
        variant_selector.addWidget(self.variant_combo)
        add_layout.addLayout(variant_selector, stretch=1)
        add_layout.addWidget(QLabel("Qty:"))
        self.qty_spin = QSpinBox()
        self.qty_spin.setRange(1, 10000)
        add_layout.addWidget(self.qty_spin)
        self.btn_add_freebie = QPushButton("Add")
        self.btn_add_freebie.clicked.connect(self.add_freebie)
        add_layout.addWidget(self.btn_add_freebie)
        self.btn_remove_freebie = QPushButton("Remove Selected")
        self.btn_remove_freebie.clicked.connect(self.remove_selected_freebie)
        add_layout.addWidget(self.btn_remove_freebie)
        button_box = QDialogButtonBox(QDialogButtonBox.StandardButton.Save | QDialogButtonBox.StandardButton.Cancel)
        button_box.accepted.connect(self.handle_save)
        button_box.rejected.connect(self.reject)
        main_layout.addWidget(button_box)
        self.variant_options = []
        self.populate_variant_options()
        self.variant_search_edit.textChanged.connect(self.apply_variant_filter)
        self.populate_tier_combo()
        self.tier_combo.currentIndexChanged.connect(self.handle_tier_selected)
        if self.tier_combo.count() > 0:
            self.handle_tier_selected(self.tier_combo.currentIndex())
        else:
            self.clear_form()
    def populate_variant_options(self):
        self.variant_options = []
        for barcode in sorted(self.products.keys()):
            variants = self.products[barcode]
            for index, variant in enumerate(variants):
                name = variant.get("name", barcode)
                label = f"{name} ({barcode}"
                if len(variants) > 1:
                    label += f" / Variant {index + 1}"
                label += ")"
                option = {
                    "barcode": barcode,
                    "variant_index": index,
                    "name": name,
                    "label": label
                }
                self.variant_options.append(option)
        self.apply_variant_filter(self.variant_search_edit.text())
    def apply_variant_filter(self, text):
        terms = [term for term in (text or "").lower().split() if term]
        self.variant_combo.blockSignals(True)
        self.variant_combo.clear()
        for option in self.variant_options:
            haystack = f"{option['barcode']} {option['name']} {option['label']}".lower()
            matches = all(term in haystack for term in terms)
            if matches:
                self.variant_combo.addItem(option["label"], option)
        self.variant_combo.blockSignals(False)
        has_results = self.variant_combo.count() > 0
        if has_results:
            self.variant_combo.setCurrentIndex(0)
        self.variant_combo.setEnabled(has_results)
        self.btn_add_freebie.setEnabled(has_results)
    def populate_tier_combo(self):
        self.tier_combo.blockSignals(True)
        self.tier_combo.clear()
        for entry in basket_promos:
            code = entry.get("code")
            if not code:
                continue
            display = f"{code} - â‚±{entry.get('threshold', 0):,.2f}"
            self.tier_combo.addItem(display, code)
        self.tier_combo.blockSignals(False)
    def clear_form(self):
        self.current_code = None
        self.code_edit.clear()
        self.name_edit.clear()
        self.threshold_spin.setValue(0.0)
        self.message_edit.clear()
        self.freebie_table.setRowCount(0)
        self.tier_combo.setCurrentIndex(-1)
        self.code_edit.setFocus()
    def handle_tier_selected(self, index):
        if index < 0:
            self.clear_form()
            return
        code = self.tier_combo.itemData(index)
        entry = self.get_tier_by_code(code)
        if not entry:
            self.clear_form()
            return
        self.current_code = code
        self.code_edit.setText(entry.get("code", ""))
        self.name_edit.setText(entry.get("name", ""))
        threshold = entry.get("threshold", 0)
        try:
            threshold = float(threshold)
        except (TypeError, ValueError):
            threshold = 0
        self.threshold_spin.setValue(max(0.0, threshold))
        self.message_edit.setText(entry.get("message", ""))
        self.freebie_table.setRowCount(0)
        for freebie in entry.get("freebies", []):
            barcode = freebie.get("barcode") or freebie.get("Stock No.") or ""
            variant_index = int(freebie.get("variant_index", 0))
            quantity = int(freebie.get("quantity", 1))
            self.insert_freebie_row(barcode, variant_index, quantity)
    def get_tier_by_code(self, code):
        for entry in basket_promos:
            if entry.get("code") == code:
                return entry
        return None
    def insert_freebie_row(self, barcode, variant_index, quantity):
        qty = max(1, int(quantity))
        variants = self.products.get(barcode, [])
        name = barcode
        variant_label = "Default"
        if variants:
            if variant_index >= len(variants):
                variant_index = 0
            name = variants[variant_index].get("name", barcode)
            variant_label = f"Variant {variant_index + 1}" if len(variants) > 1 else "Default"
        row = self.freebie_table.rowCount()
        self.freebie_table.insertRow(row)
        stock_item = QTableWidgetItem(barcode)
        stock_item.setFlags(Qt.ItemFlag.ItemIsSelectable | Qt.ItemFlag.ItemIsEnabled)
        stock_item.setData(Qt.ItemDataRole.UserRole, (barcode, variant_index))
        self.freebie_table.setItem(row, 0, stock_item)
        variant_item = QTableWidgetItem(variant_label)
        variant_item.setFlags(Qt.ItemFlag.ItemIsSelectable | Qt.ItemFlag.ItemIsEnabled)
        self.freebie_table.setItem(row, 1, variant_item)
        name_item = QTableWidgetItem(name)
        name_item.setFlags(Qt.ItemFlag.ItemIsSelectable | Qt.ItemFlag.ItemIsEnabled)
        self.freebie_table.setItem(row, 2, name_item)
        qty_spin = QSpinBox()
        qty_spin.setRange(1, 10000)
        qty_spin.setValue(qty)
        self.freebie_table.setCellWidget(row, 3, qty_spin)
    def add_freebie(self):
        data = self.variant_combo.currentData()
        if not data:
            show_warning("Select Product", "Choose a product to add as a reward item.", self)
            return
        quantity = self.qty_spin.value()
        barcode = data["barcode"]
        variant_index = data["variant_index"]
        for row in range(self.freebie_table.rowCount()):
            item = self.freebie_table.item(row, 0)
            if not item:
                continue
            existing_barcode, existing_variant = item.data(Qt.ItemDataRole.UserRole) or (None, None)
            if existing_barcode == barcode and existing_variant == variant_index:
                spin = self.freebie_table.cellWidget(row, 3)
                if isinstance(spin, QSpinBox):
                    spin.setValue(spin.value() + quantity)
                return
        self.insert_freebie_row(barcode, variant_index, quantity)
    def remove_selected_freebie(self):
        row = self.freebie_table.currentRow()
        if row < 0:
            show_warning("Remove Item", "Select a reward item from the list to remove.", self)
            return
        self.freebie_table.removeRow(row)
    def collect_freebies(self):
        freebies = []
        for row in range(self.freebie_table.rowCount()):
            stock_item = self.freebie_table.item(row, 0)
            if not stock_item:
                continue
            barcode, variant_index = stock_item.data(Qt.ItemDataRole.UserRole) or (None, None)
            if not barcode:
                continue
            qty_widget = self.freebie_table.cellWidget(row, 3)
            quantity = qty_widget.value() if isinstance(qty_widget, QSpinBox) else 1
            freebies.append({
                "barcode": barcode,
                "variant_index": int(variant_index or 0),
                "quantity": max(1, int(quantity))
            })
        return freebies
    def handle_save(self):
        global basket_promos
        code = self.code_edit.text().strip()
        if not code:
            show_error("Validation Error", "Tier code is required.", self)
            return
        threshold = float(self.threshold_spin.value())
        if threshold <= 0:
            show_error("Validation Error", "Threshold must be greater than zero.", self)
            return
        freebies = self.collect_freebies()
        if not freebies:
            show_error("Validation Error", "Add at least one reward item for this tier.", self)
            return
        entry = {
            "code": code,
            "name": self.name_edit.text().strip(),
            "threshold": threshold,
            "message": self.message_edit.text().strip(),
            "freebies": freebies
        }
        replaced = False
        for idx, existing in enumerate(basket_promos):
            if existing.get("code") == code:
                basket_promos[idx] = entry
                replaced = True
                break
        if not replaced:
            basket_promos.append(entry)
        basket_promos.sort(key=lambda x: x.get("threshold", 0))
        save_basket_promos(self)
        show_info("Basket Rewards", f"Tier '{code}' saved successfully.", self)
        self.accept()
    def delete_tier(self):
        global basket_promos
        code = self.code_edit.text().strip()
        if not code:
            show_warning("Delete Tier", "Select a tier before attempting to delete.", self)
            return
        confirm = QMessageBox.question(
            self,
            "Delete Tier",
            f"Are you sure you want to delete the basket reward '{code}'?",
            QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
            QMessageBox.StandardButton.No
        )
        if confirm != QMessageBox.StandardButton.Yes:
            return
        new_promos = [entry for entry in basket_promos if entry.get("code") != code]
        if len(new_promos) == len(basket_promos):
            show_warning("Delete Tier", f"Tier '{code}' was not found.", self)
            return
        basket_promos = new_promos
        save_basket_promos(self)
        show_info("Basket Rewards", f"Tier '{code}' deleted.", self)
        self.populate_tier_combo()
        self.clear_form()
# ----------------- Main Window -----------------
class StickyNoteWidget(QFrame):
    """Simple draggable widget that displays the active practice order."""

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setObjectName("StickyNoteWidget")
        self.setFrameShape(QFrame.Shape.StyledPanel)
        self.setFrameShadow(QFrame.Shadow.Raised)
        self.setStyleSheet(
            """
            QFrame#StickyNoteWidget {
                background-color: #F6E27F;
                border: 1px solid #C9AE4B;
                border-radius: 12px;
            }
            QLabel {
                color: #3B2F1D;
            }
            """
        )
        self.setWindowFlags(
            Qt.WindowType.Tool
            | Qt.WindowType.FramelessWindowHint
            | Qt.WindowType.WindowStaysOnTopHint
        )
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground, False)
        self.setCursor(Qt.CursorShape.OpenHandCursor)
        self._drag_offset = None
        self._user_positioned = False
        layout = QVBoxLayout(self)
        layout.setContentsMargins(18, 18, 18, 18)
        layout.setSpacing(8)
        self.title_label = QLabel("Customer Order")
        title_font = QFont("Arial", 14, QFont.Weight.Bold)
        self.title_label.setFont(title_font)
        self.title_label.setWordWrap(True)
        layout.addWidget(self.title_label)
        self.body_label = QLabel("")
        body_font = QFont("Arial", 12)
        self.body_label.setFont(body_font)
        self.body_label.setWordWrap(True)
        layout.addWidget(self.body_label)
        self.resize(260, 180)
        self._time_fraction = None
        self._time_color = QColor("#3CB371")
        self._base_border_color = QColor("#C9AE4B")
        self._progress_margin = 10

    def set_note_content(self, customer_number, scenario):
        difficulty = scenario.get("difficulty", "easy").capitalize()
        self.title_label.setText(f"{difficulty} - Customer {customer_number}")
        items = scenario.get("items") or []
        payment = scenario.get("payment") or {}
        if not items:
            self.body_label.setText("No items listed.")
            return
        lines = ["Items:"]
        for entry in items:
            name = entry.get("name") or entry.get("stock_no") or "Item"
            stock = entry.get("stock_no") or ""
            qty = entry.get("qty", 1)
            code_value = normalize_product_code(entry.get("code"))
            parts = [f"- x{qty}"]
            if code_value:
                parts.append(f"[{code_value}]")
            parts.append(name)
            if stock:
                parts.append(f"({stock})")
            lines.append(" ".join(part for part in parts if part))
        method = payment.get("method", "").title()
        lines.append("")
        lines.append("Payment:")
        if method:
            lines.append(f"- Method: {method}")
        cash_amount = payment.get("cash_amount", 0.0)
        gcash_amount = payment.get("gcash_amount", 0.0)
        if cash_amount:
            lines.append(f"- Cash: P{cash_amount:,.0f}")
        if gcash_amount:
            lines.append(f"- GCash: P{gcash_amount:,.0f}")
        if not cash_amount and not gcash_amount:
            lines.append("- Amount provided at checkout")
        expected_change = payment.get("expected_change")
        if expected_change is not None:
            lines.append(f"- Expected change: P{expected_change:,.2f}")
        time_limit = scenario.get("time_limit_seconds")
        if time_limit:
            lines.append("")
            lines.append(f"Time limit: {int(time_limit)}s")
        self.body_label.setText("\n".join(lines))

    def set_time_progress(self, fraction, color):
        if fraction is None or fraction <= 0:
            self._time_fraction = None
            self.update()
            return
        clamped = max(0.0, min(1.0, float(fraction)))
        self._time_fraction = clamped
        if color is not None:
            self._time_color = color
        self.update()

    def paintEvent(self, event):
        super().paintEvent(event)
        if self._time_fraction is None or self._time_fraction <= 0:
            return
        left = float(self._progress_margin)
        right = float(self.width() - self._progress_margin)
        y = float(self._progress_margin)
        base_pen = QPen(self._base_border_color, 4)
        base_pen.setCapStyle(Qt.PenCapStyle.RoundCap)
        progress_pen = QPen(self._time_color, 4)
        progress_pen.setCapStyle(Qt.PenCapStyle.RoundCap)
        painter = QPainter(self)
        painter.setRenderHint(QPainter.RenderHint.Antialiasing)
        painter.setPen(base_pen)
        painter.drawLine(QPointF(left, y), QPointF(right, y))
        progress_width = (right - left) * self._time_fraction
        if progress_width > 0:
            end_point = QPointF(left + progress_width, y)
            painter.setPen(progress_pen)
            painter.drawLine(QPointF(left, y), end_point)
        painter.end()

    def mousePressEvent(self, event):
        if event.button() == Qt.MouseButton.LeftButton:
            self._drag_offset = event.globalPosition().toPoint() - self.frameGeometry().topLeft()
            self.setCursor(Qt.CursorShape.ClosedHandCursor)
            event.accept()
        super().mousePressEvent(event)

    def mouseMoveEvent(self, event):
        if self._drag_offset is not None and event.buttons() & Qt.MouseButton.LeftButton:
            new_pos = event.globalPosition().toPoint() - self._drag_offset
            self.move(new_pos)
            self._user_positioned = True
            event.accept()
        super().mouseMoveEvent(event)

    def mouseReleaseEvent(self, event):
        if event.button() == Qt.MouseButton.LeftButton:
            self._drag_offset = None
            self.setCursor(Qt.CursorShape.OpenHandCursor)
            event.accept()
        super().mouseReleaseEvent(event)

    def show_at_default(self, parent_window):
        if self._user_positioned:
            self.show()
            self.raise_()
            return
        if parent_window is None:
            self.show()
            self.raise_()
            return
        parent_geom = parent_window.frameGeometry()
        note_width = self.width()
        available_width = parent_geom.width()
        offset_x = max(20, available_width - note_width - 40)
        x = parent_geom.x() + offset_x
        y = parent_geom.y() + 100
        self.move(int(x), int(y))
        self.show()
        self.raise_()

    def reset_position_flag(self):
        self._user_positioned = False


class CustomerSimulationManager:
    """Helper to run a quick three-customer practice simulation inside the POS UI."""

    DIFFICULTY_SETTINGS = {
        "easy": {
            "line_min": 1,
            "line_max": 3,
            "qty_min": 1,
            "qty_max": 3,
            "allow_bundles": False,
            "allow_promos": False,
            "payment_modes": ["cash only", "gcash only"],
            "extra_cents": [0, 500, 1000, 2000],
            "time_limit_seconds": 90,
        },
        "medium": {
            "line_min": 2,
            "line_max": 4,
            "qty_min": 1,
            "qty_max": 5,
            "allow_bundles": True,
            "allow_promos": True,
            "payment_modes": ["cash only", "gcash only", "cash and gcash"],
            "extra_cents": [0, 500, 1000, 2000, 5000],
            "time_limit_seconds": 60,
        },
        "hard": {
            "line_min": 5,
            "line_max": 7,
            "qty_min": 1,
            "qty_max": 7,
            "allow_bundles": True,
            "allow_promos": True,
            "payment_modes": ["cash only", "gcash only", "cash and gcash"],
            "extra_cents": [500, 1000, 2000, 5000, 10000],
            "time_limit_seconds": 45,
        },
    }

    SPEED_THRESHOLDS = (20.0, 40.0)  # seconds for Excellent / Good speed feedback

    def __init__(self, main_window):
        self.main_window = main_window
        self.difficulty = "easy"
        self.note = StickyNoteWidget()
        self.timeout_timer = QTimer(main_window)
        self.timeout_timer.setSingleShot(True)
        self.timeout_timer.timeout.connect(self._handle_time_limit_expired)
        self.progress_timer = QTimer(main_window)
        self.progress_timer.setInterval(200)
        self.progress_timer.timeout.connect(self._update_time_progress_visual)
        self.customer_deadline = None
        self.customer_total_count = 0
        self.active_checkout_token = None
        if self.main_window is not None:
            try:
                self.main_window.destroyed.connect(self.note.close)
            except Exception:
                pass
        self.reset_state()

    def reset_state(self):
        self.is_active = False
        self.scenarios = []
        self.current_index = -1
        self.start_time = None
        self.customer_start_time = None
        self.results = []
        self.time_limit_seconds = None
        self.customer_deadline = None
        self.customer_total_count = 0
        self.active_checkout_token = None
        if hasattr(self, "timeout_timer") and self.timeout_timer:
            self.timeout_timer.stop()
        if hasattr(self, "progress_timer") and self.progress_timer:
            self.progress_timer.stop()
        if hasattr(self, "note") and self.note:
            self.note.hide()
            self.note.reset_position_flag()
            self.note.set_time_progress(None, None)
        self._update_button_state()

    def set_difficulty(self, difficulty):
        normalized = (difficulty or "").strip().lower()
        if normalized not in self.DIFFICULTY_SETTINGS:
            normalized = "easy"
        self.difficulty = normalized
        settings = self.DIFFICULTY_SETTINGS[self.difficulty]
        self.time_limit_seconds = settings.get("time_limit_seconds") or None

    def _prompt_difficulty(self):
        options = ["Easy", "Medium", "Hard"]
        current_label = self.difficulty.capitalize()
        try:
            selection, ok = QInputDialog.getItem(
                self.main_window,
                "Simulation Difficulty",
                "Choose practice difficulty:",
                options,
                current=options.index(current_label) if current_label in options else 0,
                editable=False,
            )
        except Exception:
            return current_label
        if not ok:
            return None
        return selection

    def _prompt_customer_count(self):
        try:
            value, ok = QInputDialog.getInt(
                self.main_window,
                "Number of Customers",
                "How many practice customers?",
                value=max(1, self.customer_total_count) if self.customer_total_count else 3,
                min=1,
                max=10,
            )
        except Exception:
            return None
        if not ok:
            return None
        return int(value)

    def _update_button_state(self):
        button = getattr(self.main_window, "btn_start_simulation", None)
        if button is not None:
            button.setEnabled(not self.is_active)

    def start_simulation(self):
        if self.is_active:
            QMessageBox.information(
                self.main_window,
                "Customer Simulation",
                "A simulation is already running. Complete the current practice customers first.",
            )
            return
        existing_sessions = getattr(self.main_window, "customer_sessions", [])
        has_active_carts = any(session.get("cart") for session in existing_sessions or [])
        if has_active_carts:
            confirm = QMessageBox.question(
                self.main_window,
                "Start Simulation",
                "Starting the simulation will clear the current customer queue. Continue?",
                QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
                QMessageBox.StandardButton.No,
            )
            if confirm != QMessageBox.StandardButton.Yes:
                return
        selection = self._prompt_difficulty()
        if selection is None:
            return
        self.set_difficulty(selection)
        customer_count = self._prompt_customer_count()
        if customer_count is None:
            return
        scenarios = self._build_scenarios(customer_count)
        if not scenarios:
            show_warning(
                "Customer Simulation",
                "No sellable products were found, so the practice run cannot start right now.",
                self.main_window,
            )
            return
        self.reset_state()
        self.scenarios = scenarios
        self.customer_total_count = len(scenarios)
        self.is_active = True
        self._update_button_state()
        self.start_time = time.perf_counter()
        self.main_window.initialize_customer_queue()
        self.main_window.log_user_action(
            "Simulation started",
            f"{len(scenarios)} practice customers ({self.difficulty.capitalize()})",
        )
        self._begin_customer(0, announce=True)

    def _collect_candidate_items(self, allow_bundles, allow_promos):
        items = []
        lookups = list(product_variant_lookup.values())
        seen_skus = set()
        for data in lookups:
            if not isinstance(data, dict):
                continue
            sku = data.get("sku") or data.get("base_barcode")
            if not sku or sku in seen_skus:
                continue
            bundle_components = data.get("bundle_components")
            if bundle_components and not allow_bundles:
                continue
            promo_code = data.get("promo_code")
            if promo_code and not allow_promos:
                continue
            price = data.get("price")
            if price is None:
                continue
            try:
                price_value = float(price)
            except (TypeError, ValueError):
                continue
            if price_value <= 0:
                continue
            seen_skus.add(sku)
            promo_multiplier = promo_quantity_multiplier(promo_code)
            items.append(
                {
                    "sku": sku,
                    "stock_no": sku,
                    "variant_index": data.get("variant_index"),
                    "name": data.get("name") or sku,
                    "price": price_value,
                    "inventory_usage": data.get("inventory_usage", 1) or 1,
                    "bundle_components": deepcopy(bundle_components) if bundle_components else None,
                    "bundle_code": data.get("bundle_code"),
                    "is_bundle": bool(bundle_components),
                    "promo_code": promo_code,
                    "promo_multiplier": promo_multiplier,
                    "code": data.get("code"),
                }
            )
        return items

    def _build_scenarios(self, count):
        settings = self.DIFFICULTY_SETTINGS.get(self.difficulty, self.DIFFICULTY_SETTINGS["easy"])
        allow_bundles = settings["allow_bundles"]
        allow_promos = settings["allow_promos"]
        candidates = self._collect_candidate_items(allow_bundles, allow_promos)
        if not candidates and allow_bundles:
            candidates = self._collect_candidate_items(False, allow_promos)
        if not candidates:
            return []
        scenarios = []
        for _ in range(count):
            line_min = settings["line_min"]
            line_max = settings["line_max"]
            max_available = max(1, len(candidates))
            upper_bound = min(line_max, max_available) if len(candidates) >= line_min else line_min
            line_count = random.randint(line_min, max(upper_bound, line_min))
            if len(candidates) >= line_count:
                picked = random.sample(candidates, line_count)
            else:
                picked = [random.choice(candidates) for _ in range(line_count)]
            aggregated = {}
            for choice in picked:
                key = (
                    choice["stock_no"],
                    choice.get("variant_index"),
                    choice.get("bundle_code"),
                    choice.get("promo_code"),
                )
                entry = aggregated.setdefault(
                    key,
                    {
                        "stock_no": choice["stock_no"],
                        "variant_index": choice.get("variant_index"),
                        "name": choice["name"],
                        "qty": 0,
                        "price": choice["price"],
                        "inventory_usage": choice.get("inventory_usage", 1),
                        "bundle_code": choice.get("bundle_code"),
                        "bundle_components": deepcopy(choice.get("bundle_components")) if choice.get("bundle_components") else None,
                        "is_bundle": choice.get("is_bundle", False),
                        "promo_code": choice.get("promo_code"),
                        "promo_multiplier": choice.get("promo_multiplier", 1),
                        "code": choice.get("code"),
                    },
                )
                base_qty = random.randint(settings["qty_min"], settings["qty_max"])
                multiplier = entry.get("promo_multiplier", 1) or 1
                entry["qty"] += base_qty * multiplier
            scenario_items = list(aggregated.values())
            total_due = sum(item["price"] * item["qty"] for item in scenario_items)
            payment = self._generate_payment(total_due, settings)
            scenarios.append(
                {
                    "items": scenario_items,
                    "payment": payment,
                    "total": total_due,
                    "difficulty": self.difficulty,
                    "time_limit_seconds": settings.get("time_limit_seconds"),
                }
            )
        return scenarios

    def _generate_payment(self, total_due, settings):
        def to_cents(amount):
            return int(round(float(amount) * 100))

        def to_whole_amount(cents):
            return float(int(cents // 100)) if cents >= 0 else 0.0

        def to_change_amount(cents):
            return round(cents / 100.0, 2)

        raw_total_cents = max(0, to_cents(total_due))
        total_cents = raw_total_cents
        if total_cents % 100:
            total_cents = ((total_cents + 99) // 100) * 100
        extra_options = settings.get("extra_cents") or [0]
        extra_cents = random.choice(extra_options)
        total_paid_cents = max(total_cents, total_cents + extra_cents)
        if total_paid_cents % 100:
            total_paid_cents = ((total_paid_cents + 99) // 100) * 100
        method = random.choice(settings.get("payment_modes") or ["cash only"])
        cash_cents = 0
        gcash_cents = 0
        if method == "cash only":
            cash_cents = total_paid_cents
        elif method == "gcash only":
            gcash_cents = total_paid_cents
        else:
            if total_paid_cents < 200:
                method = "cash only"
                cash_cents = total_paid_cents
            elif total_paid_cents <= 0:
                method = "cash only"
                cash_cents = 0
            else:
                valid_cash_values = list(range(100, total_paid_cents, 100))
                if not valid_cash_values:
                    cash_cents = total_paid_cents
                    gcash_cents = 0
                    method = "cash only"
                else:
                    cash_cents = random.choice(valid_cash_values)
                    gcash_cents = total_paid_cents - cash_cents
                    if gcash_cents <= 0:
                        cash_cents = total_paid_cents
                        gcash_cents = 0
                        method = "cash only"
        expected_change_cents = max(0, cash_cents + gcash_cents - raw_total_cents)
        return {
            "method": method,
            "cash_amount": to_whole_amount(cash_cents),
            "gcash_amount": to_whole_amount(gcash_cents),
            "total_paid": to_whole_amount(cash_cents + gcash_cents),
            "expected_change": to_change_amount(expected_change_cents),
        }

    def _begin_customer(self, index, announce=False):
        if index < 0 or index >= len(self.scenarios):
            return
        self.current_index = index
        self.customer_start_time = time.perf_counter()
        self.active_checkout_token = time.perf_counter_ns()
        self._update_sticky_note(self.scenarios[index], index + 1, announce=announce)
        self._start_customer_timer()

    def get_active_checkout_token(self):
        return self.active_checkout_token

    def _update_sticky_note(self, scenario, number, announce=False):
        if not self.note:
            return
        self.note.set_note_content(number, scenario)
        self.note.show_at_default(self.main_window)
        if announce:
            QMessageBox.information(
                self.main_window,
                "Customer Simulation",
                "A movable sticky note has been added to the screen with the current customer's order "
                "and payment details. Drag it anywhere that's convenient while you process the cart.",
            )
    def _start_customer_timer(self):
        if not self.timeout_timer:
            return
        self.timeout_timer.stop()
        if self.progress_timer:
            self.progress_timer.stop()
        self.customer_deadline = None
        scenario = None
        if 0 <= self.current_index < len(self.scenarios):
            scenario = self.scenarios[self.current_index]
        seconds = None
        if scenario:
            seconds = scenario.get("time_limit_seconds")
        if not seconds or seconds <= 0:
            self.time_limit_seconds = None
            if self.note:
                self.note.set_time_progress(None, None)
            return
        self.time_limit_seconds = seconds
        self.customer_deadline = time.perf_counter() + seconds
        if self.note:
            self.note.set_time_progress(1.0, QColor("#3CB371"))
        self.timeout_timer.start(int(seconds * 1000))
        if self.progress_timer:
            self.progress_timer.start()
        self._update_time_progress_visual()

    def _update_time_progress_visual(self):
        if not self.note:
            return
        if not self.customer_deadline or not self.time_limit_seconds:
            self.note.set_time_progress(None, None)
            if self.progress_timer:
                self.progress_timer.stop()
            return
        remaining = self.customer_deadline - time.perf_counter()
        if remaining <= 0:
            self.note.set_time_progress(None, None)
            if self.progress_timer:
                self.progress_timer.stop()
            return
        fraction = max(0.0, min(1.0, remaining / self.time_limit_seconds))
        if fraction > 0.5:
            color = QColor("#3CB371")
        elif fraction > 0.25:
            color = QColor("#FFA500")
        else:
            color = QColor("#FF4C4C")
        self.note.set_time_progress(fraction, color)

    def handle_checkout_completion(
        self,
        cart_snapshot,
        total,
        total_paid,
        change,
        payment_method,
        receipt_text_content,
        cash_amount,
        gcash_amount,
        *,
        checkout_token=None,
    ):
        self.timeout_timer.stop()
        if self.progress_timer:
            self.progress_timer.stop()
        if not self.is_active or self.current_index < 0:
            return
        if self.current_index >= len(self.scenarios):
            return
        if checkout_token is not None:
            if self.active_checkout_token is None or checkout_token != self.active_checkout_token:
                return
        self._finalize_customer(
            cart_snapshot,
            total,
            total_paid,
            change,
            payment_method,
            receipt_text_content,
            cash_amount,
            gcash_amount,
            timed_out=False,
        )

    def _handle_time_limit_expired(self):
        if not self.is_active or self.current_index < 0:
            return
        if self.progress_timer:
            self.progress_timer.stop()
        if hasattr(self.main_window, "handle_simulation_timeout_abort"):
            message = (
                f"Customer {self.current_index + 1} lost patience and left before you finished."
                " Their order has been cleared so you can work on the next customer."
            )
            self.main_window.handle_simulation_timeout_abort(message)
        scenario = self.scenarios[self.current_index]
        cart_snapshot = [deepcopy(entry) for entry in getattr(self.main_window, "cart", [])]
        if hasattr(self.main_window, "cart"):
            self.main_window.cart.clear()
        if hasattr(self.main_window, "refresh_cart_display"):
            self.main_window.refresh_cart_display()
        if hasattr(self.main_window, "update_total"):
            self.main_window.update_total()
        self._finalize_customer(
            cart_snapshot,
            scenario.get("total", 0.0),
            total_paid=0.0,
            change=0.0,
            payment_method="timeout",
            receipt_text_content="",
            cash_amount=0.0,
            gcash_amount=0.0,
            timed_out=True,
        )

    def _finalize_customer(
        self,
        cart_snapshot,
        total,
        total_paid,
        change,
        payment_method,
        receipt_text_content,
        cash_amount,
        gcash_amount,
        timed_out,
    ):
        if self.timeout_timer:
            self.timeout_timer.stop()
        if self.progress_timer:
            self.progress_timer.stop()
        self.customer_deadline = None
        self.active_checkout_token = None
        if self.note:
            self.note.set_time_progress(None, None)
        scenario = self.scenarios[self.current_index]
        customer_number = self.current_index + 1
        elapsed = (time.perf_counter() - self.customer_start_time) if self.customer_start_time else 0.0
        if timed_out and self.time_limit_seconds:
            elapsed = self.time_limit_seconds
        evaluation = self._evaluate_accuracy(scenario, cart_snapshot)
        accuracy = evaluation["accuracy"]
        issues = evaluation["issue_lines"]
        payment_evaluation = self._evaluate_payment(
            scenario,
            total,
            total_paid,
            change,
            payment_method,
            cash_amount,
            gcash_amount,
            timed_out=timed_out,
        )
        issues.extend(payment_evaluation["issues"])
        accuracy_rating = self._accuracy_rating_label(accuracy)
        speed_rating = self._speed_rating_label(elapsed)
        receipt_provided = bool(str(receipt_text_content or "").strip())
        if not receipt_provided:
            issues.append("Receipt not detected. Be sure to print or hand a receipt to the customer.")
        feedback_lines = [
            f"Customer {customer_number} served!",
            f"Time: {elapsed:.1f}s ({speed_rating})",
            f"Accuracy: {accuracy * 100:.1f}% ({accuracy_rating})",
            f"Tendered: P{total_paid:,.0f} | Change: P{change:,.2f} | Method: {payment_method.title()}",
            "Receipt: Provided" if receipt_provided else "Receipt: Missing",
        ]
        if payment_evaluation["expected_summary"]:
            feedback_lines.append(payment_evaluation["expected_summary"])
        if issues:
            feedback_lines.append("")
            feedback_lines.append("Notes:")
            feedback_lines.extend(f" - {entry}" for entry in issues)
        else:
            feedback_lines.append("No issues detected - great work!")
        if not timed_out:
            QMessageBox.information(
                self.main_window,
                "Simulation Feedback",
                "\n".join(feedback_lines),
            )
        log_details = (
            f"Customer {customer_number}: {elapsed:.1f}s ({speed_rating}), "
            f"{accuracy * 100:.1f}% ({accuracy_rating}), receipt {'yes' if receipt_provided else 'no'}"
        )
        self.main_window.log_user_action("Simulation feedback", log_details)
        result_entry = {
            "scenario": scenario,
            "elapsed": elapsed,
            "accuracy": accuracy,
            "issues": issues,
            "missing": evaluation["missing"],
            "extras": evaluation["extras"],
            "speed_rating": speed_rating,
            "accuracy_rating": accuracy_rating,
            "receipt_provided": receipt_provided,
            "payment_result": payment_evaluation,
            "timed_out": timed_out,
        }
        self.results.append(result_entry)
        self.current_index += 1
        if self.current_index < len(self.scenarios):
            self._begin_customer(self.current_index, announce=False)
            return
        total_customers = len(self.results)
        total_time = (time.perf_counter() - self.start_time) if self.start_time else sum(
            entry["elapsed"] for entry in self.results
        )
        average_time = total_time / total_customers if total_customers else 0.0
        average_accuracy = (
            sum(entry["accuracy"] for entry in self.results) / total_customers if total_customers else 0.0
        )
        collected_issues = [issue for entry in self.results for issue in entry["issues"]]
        score_value, score_label = self._compute_overall_score(average_accuracy, average_time)
        if score_value >= 95:
            performance_banner = "Outstanding — you are good at this!"
        elif score_value >= 80:
            performance_banner = "Great hustle! Keep it up."
        elif score_value >= 65:
            performance_banner = "Not bad for a beginner."
        else:
            performance_banner = "Needs more practice — keep training!"
        summary_lines = [
            performance_banner,
            "",
            "Practice run complete!",
            f"Customers served: {total_customers}",
            f"Total time: {total_time:.1f}s (avg {average_time:.1f}s per customer)",
            f"Average accuracy: {average_accuracy * 100:.1f}%",
            f"Score: {score_value}/100 ({score_label})",
        ]
        if collected_issues:
            translated_feedback = self._translate_issue_feedback(collected_issues)
            if translated_feedback:
                summary_lines.append("")
                summary_lines.append("Things to review next time:")
                for entry in translated_feedback:
                    summary_lines.append(f"- {entry}")
        else:
            summary_lines.append("No discrepancies were detected - excellent job!")
        QMessageBox.information(
            self.main_window,
            "Simulation Summary",
            "\n".join(summary_lines),
        )
        if self.note:
            self.note.hide()
        self.main_window.log_user_action(
            "Simulation completed",
            f"{total_customers} customers | {total_time:.1f}s | {average_accuracy * 100:.1f}% accuracy",
        )
        self.reset_state()

    def _evaluate_accuracy(self, scenario, cart_snapshot):
        expected = Counter()
        expected_names = {}
        for item in scenario.get("items", []):
            key = (item["stock_no"], item["variant_index"])
            expected[key] += float(item.get("qty", 0) or 0)
            expected_names[key] = item.get("name") or item["stock_no"]
        actual = Counter()
        actual_names = {}
        for entry in cart_snapshot or []:
            if entry.get("is_freebie"):
                continue
            stock_no = entry.get("base_stock_no") or entry.get("Stock No.")
            if not stock_no:
                continue
            variant_index = int(entry.get("variant_index", 0) or 0)
            qty = self._as_float(entry.get("qty", 1), default=1.0)
            usage = self._as_float(entry.get("inventory_usage", 1), default=1.0)
            actual_qty = qty * usage
            key = (stock_no, variant_index)
            actual[key] += actual_qty
            if key not in actual_names:
                actual_names[key] = entry.get("name") or stock_no
        total_expected_units = sum(expected.values())
        correctly_matched = sum(min(expected[key], actual.get(key, 0.0)) for key in expected)
        accuracy = (correctly_matched / total_expected_units) if total_expected_units else 1.0
        missing = []
        extras = []
        for key, expected_qty in expected.items():
            actual_qty = actual.get(key, 0.0)
            if actual_qty + 1e-6 < expected_qty:
                missing.append((key, expected_qty - actual_qty))
        for key, actual_qty in actual.items():
            expected_qty = expected.get(key, 0.0)
            if actual_qty - 1e-6 > expected_qty:
                extras.append((key, actual_qty - expected_qty))
        issue_lines = []
        for key, qty in missing:
            label = expected_names.get(key) or actual_names.get(key) or key[0]
            issue_lines.append(f"Missing {self._format_quantity(qty)} x {label}")
        for key, qty in extras:
            label = actual_names.get(key) or expected_names.get(key) or key[0]
            issue_lines.append(f"Unexpected {self._format_quantity(qty)} x {label}")
        return {
            "accuracy": max(0.0, min(1.0, accuracy)),
            "missing": missing,
            "extras": extras,
            "issue_lines": issue_lines,
        }

    def _evaluate_payment(
        self,
        scenario,
        total,
        total_paid,
        change,
        payment_method,
        cash_amount,
        gcash_amount,
        timed_out=False,
    ):
        expected = scenario.get("payment") or {}
        expected_method = (expected.get("method") or "").lower()
        tolerance = 0.05
        issues = []
        expected_summary = ""
        def _format_amount(value):
            return f"P{value:,.0f}"
        actual_cash = round(cash_amount or 0.0, 2)
        actual_gcash = round(gcash_amount or 0.0, 2)
        actual_change = round(change or 0.0, 2)
        expected_cash = round(expected.get("cash_amount", 0.0), 2)
        expected_gcash = round(expected.get("gcash_amount", 0.0), 2)
        expected_change = round(expected.get("expected_change", 0.0), 2)
        expected_total_paid = round(expected.get("total_paid", expected_cash + expected_gcash), 2)
        if timed_out:
            issues.append("Checkout not completed before the time limit.")
            return {
                "issues": issues,
                "expected_summary": "",
                "expected": expected,
            }
        if expected_method and expected_method != payment_method.lower():
            issues.append(f"Payment method mismatch. Expected {expected_method.title()}, entered {payment_method.title()}.")
        if expected_method in ("cash only", "cash and gcash"):
            if abs(actual_cash - expected_cash) > tolerance:
                issues.append(
                    f"Cash tender entered {_format_amount(actual_cash)} but expected {_format_amount(expected_cash)}."
                )
        else:
            if actual_cash > tolerance:
                issues.append("Cash tender was provided but the customer planned to pay without cash.")
        if expected_method in ("gcash only", "cash and gcash"):
            if abs(actual_gcash - expected_gcash) > tolerance:
                issues.append(
                    f"GCash tender entered {_format_amount(actual_gcash)} but expected {_format_amount(expected_gcash)}."
                )
        else:
            if actual_gcash > tolerance:
                issues.append("GCash tender was provided but the customer planned to pay without GCash.")
        if abs((actual_cash + actual_gcash) - expected_total_paid) > tolerance:
            issues.append(
                f"Total tender {_format_amount(actual_cash + actual_gcash)} differs from expected {_format_amount(expected_total_paid)}."
            )
        if abs(actual_change - expected_change) > tolerance:
            issues.append(
                f"Change should be {_format_amount(expected_change)} but {_format_amount(actual_change)} was recorded."
            )
        if expected_method:
            parts = [f"Expected method: {expected_method.title()}"]
            if expected_cash:
                parts.append(f"Cash {_format_amount(expected_cash)}")
            if expected_gcash:
                parts.append(f"GCash {_format_amount(expected_gcash)}")
            parts.append(f"Change P{expected_change:,.2f}")
            expected_summary = " | ".join(parts)
        return {
            "issues": issues,
            "expected_summary": expected_summary,
            "expected": expected,
        }

    def _format_quantity(self, value):
        if abs(value - int(value)) < 1e-6:
            return str(int(round(value)))
        return f"{value:.2f}"

    def _as_float(self, value, default=0.0):
        try:
            return float(value)
        except (TypeError, ValueError):
            return default

    def _accuracy_rating_label(self, accuracy):
        if accuracy >= 0.99:
            return "Perfect"
        if accuracy >= 0.9:
            return "Great"
        if accuracy >= 0.75:
            return "Fair"
        return "Needs Attention"

    def _speed_rating_label(self, seconds_elapsed):
        if seconds_elapsed <= self.SPEED_THRESHOLDS[0]:
            return "Excellent"
        if seconds_elapsed <= self.SPEED_THRESHOLDS[1]:
            return "Good"
        return "Needs Improvement"

    def _compute_overall_score(self, average_accuracy, average_time):
        accuracy_component = max(0.0, min(1.0, average_accuracy or 0.0))
        reference_time = self.time_limit_seconds or self.SPEED_THRESHOLDS[-1]
        if reference_time is None or reference_time <= 0:
            reference_time = 60.0
        if average_time <= 0:
            speed_component = 1.0
        else:
            speed_component = max(0.0, min(1.0, reference_time / max(average_time, 1e-3)))
        score_value = round((accuracy_component * 0.7 + speed_component * 0.3) * 100)
        if score_value >= 95:
            label = "Outstanding"
        elif score_value >= 85:
            label = "Great"
        elif score_value >= 70:
            label = "Solid"
        elif score_value >= 55:
            label = "Needs Practice"
        else:
            label = "Critical"
        return score_value, label

    def _translate_issue_feedback(self, issues):
        if not issues:
            return ["No discrepancies were detected - excellent job!"]
        cleaned = [issue.strip() for issue in issues if issue and issue.strip()]
        lowered = [entry.lower() for entry in cleaned]
        messages = []
        if any(text.startswith("missing ") for text in lowered):
            messages.append("Accuracy drill: double-check the product codes you type before confirming the cart.")
        if any(text.startswith("unexpected ") for text in lowered):
            messages.append("Cart review: remove unintended items before you hit checkout.")
        if any("time limit" in text for text in lowered):
            messages.append("Speed focus: tighten your workflow so each customer finishes before the timer.")
        if any("receipt" in text for text in lowered):
            messages.append("Customer care: always hand or print the receipt to close the sale.")
        if any(text.startswith("payment") for text in lowered):
            messages.append("Payment accuracy: match the expected tender and change amounts more carefully.")
        if any("cash tender" in text for text in lowered):
            messages.append("Cash handling: enter the exact cash amount the customer provides.")
        if any("gcash tender" in text for text in lowered):
            messages.append("GCash handling: verify the GCash transfer matches the expected value before confirming.")
        if any("total tender" in text for text in lowered):
            messages.append("Tender balance: ensure the combined cash + GCash equals the required total.")
        if any("change should" in text for text in lowered):
            messages.append("Change accuracy: double-check your math before handing back change.")
        categorized_keywords = (
            "missing ",
            "unexpected ",
            "time limit",
            "receipt",
            "payment",
            "cash tender",
            "gcash tender",
            "total tender",
            "change should",
        )
        seen = set()
        for original, low in zip(cleaned, lowered):
            if low in seen:
                continue
            seen.add(low)
            if not any(keyword in low for keyword in categorized_keywords):
                messages.append(original)
        if not messages:
            messages.append("Keep practicing to smooth out the rough spots.")
        return messages


class POSMainWindow(QMainWindow):
    def __init__(self, username, parent=None):
        super().__init__(parent)
        self.current_user_name = username
        self.setWindowTitle(f"POS System - Logged in as: {username}")
        self.central_widget = QWidget()
        self.setCentralWidget(self.central_widget)
        self._status_bar = self.statusBar()
        # Initialize global variables that need to be widgets for updating
        self.label_product_image = None
        self.label_product_name_display = None
        self.label_product_price_display = None
        self.label_product_stock_display = None
        self.label_product_barcode_number = None
        self.default_pixmap = None
        self.cart = []
        self.customer_sessions = []
        self.customer_tabs = None
        self.btn_add_customer = None
        self.customer_tab_shortcuts = []
        self.customer_name_counter = 1
        self._active_payment_dialog = None
        self._active_receipt_dialog = None
        self.current_item_count = current_item_count
        self.current_discount = current_discount
        self.products = products  # Make sure this is accessibl
        self.sales_summary = sales_summary  # Make sure this is accessible
        self.current_theme_mode = current_theme_preference
        self.current_effective_theme = current_theme_effective
        self.theme_actions = {}
        self.theme_action_group = None
        self.current_display_barcode = None
        self.current_display_variant_index = None
        self.current_display_bundle_code = None
        self.scanner_worker = None
        self.activity_logs = load_activity_logs()
        self._api_catalog_cache = None
        ensure_sales_vault_started()
        self.simulation_manager = CustomerSimulationManager(self)
        self.init_ui()
        self.initialize_customer_queue()
        self.init_barcode_scanner()
        self.showMaximized()
    def log_user_action(self, action, details=None):
        """Record a user action with timestamp and optional details."""
        timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        entry = {
            "timestamp": timestamp,
            "user": self.current_user_name or "Unknown",
            "action": action,
        }
        if details:
            entry["details"] = details
        self.activity_logs.append(entry)
        append_activity_log_entry(entry)

    def _deduct_tender_totals_for_revenue(self, revenue_amount):
        """
        Reduce cash / gcash tendered totals proportionally to the provided revenue amount.
        Keeps values non-negative and persists the updated totals.
        """
        global total_cash_tendered, total_gcash_tendered
        global total_cash_tendered_vault, total_gcash_tendered_vault
        amount = float(revenue_amount or 0.0)
        if amount <= 0:
            return
        cash_available = max(0.0, float(total_cash_tendered))
        gcash_available = max(0.0, float(total_gcash_tendered))
        combined = cash_available + gcash_available
        if combined <= 0:
            return
        cash_ratio = cash_available / combined if combined else 0.0
        gcash_ratio = gcash_available / combined if combined else 0.0
        cash_deduction = min(cash_available, amount * cash_ratio)
        gcash_deduction = min(gcash_available, amount * gcash_ratio)
        remainder = amount - (cash_deduction + gcash_deduction)
        if remainder > 0:
            cash_remainder = cash_available - cash_deduction
            extra_cash = min(cash_remainder, remainder)
            cash_deduction += extra_cash
            remainder -= extra_cash
        if remainder > 0:
            gcash_remainder = gcash_available - gcash_deduction
            gcash_deduction += min(gcash_remainder, remainder)
        total_cash_tendered = max(0.0, cash_available - cash_deduction)
        total_gcash_tendered = max(0.0, gcash_available - gcash_deduction)
        total_cash_tendered_vault = max(0.0, float(total_cash_tendered_vault) - cash_deduction)
        total_gcash_tendered_vault = max(0.0, float(total_gcash_tendered_vault) - gcash_deduction)
        save_tendered_amounts()

    def get_api_catalog_skus(self, parent_widget=None, force_refresh=False):
        """
        Returns a cached set of SKUs that exist on the remote API inventory.
        Fetches fresh data when forced or when the cache is stale.
        """
        widget = parent_widget or self
        if not ensure_api_settings_loaded(widget):
            return None
        cache_entry = getattr(self, "_api_catalog_cache", None)
        if (
            not force_refresh
            and cache_entry
            and isinstance(cache_entry, dict)
            and cache_entry.get("fetched_at")
            and datetime.now() - cache_entry["fetched_at"] < timedelta(minutes=15)
        ):
            return cache_entry.get("skus", set())
        payload = fetch_inventory_payload(widget)
        if payload is None:
            return None
        if payload.get("code") not in (200, 201):
            message = payload.get("message") or payload.get("error") or json.dumps(payload)
            show_error(
                "Inventory Lookup Failed",
                f"Inventory endpoint responded with code {payload.get('code')}: \n{message}",
                widget,
            )
            return None
        items = ((payload.get("data") or {}).get("items") or [])
        sku_set = set()
        for entry in items:
            sku = str(entry.get("sku") or "").strip()
            if sku:
                sku_set.add(sku)
        self._api_catalog_cache = {
            "skus": sku_set,
            "fetched_at": datetime.now(),
        }
        return sku_set

    def _clear_tracked_dialog(self, attr_name, *args):
        setattr(self, attr_name, None)

    def _track_modal_dialog(self, dialog, attr_name):
        if dialog is None:
            return dialog
        setattr(self, attr_name, dialog)
        try:
            dialog.finished.connect(partial(self._clear_tracked_dialog, attr_name))
        except Exception:
            pass
        return dialog

    def _close_tracked_dialog(self, attr_name):
        dialog = getattr(self, attr_name, None)
        if dialog is None:
            return False
        try:
            dialog.reject()
        except Exception:
            try:
                dialog.close()
            except Exception:
                pass
        setattr(self, attr_name, None)
        return True

    def handle_simulation_timeout_abort(self, message):
        closed_any = False
        for attr in ("_active_payment_dialog", "_active_receipt_dialog"):
            closed_any = self._close_tracked_dialog(attr) or closed_any
        app = QApplication.instance()
        modal = app.activeModalWidget() if app else None
        if modal and modal is not self and modal.isVisible():
            try:
                modal.reject()
            except Exception:
                try:
                    modal.close()
                except Exception:
                    pass
            closed_any = True
        if message:
            show_warning("Simulation Timeout", message, self)
        if closed_any:
            self.log_user_action("Simulation timeout cleanup", message or "Closed blocking dialogs")
    def _apply_next_item_quantity(self, quantity, *, log_message=None, status_message=None):
        """Update the next item quantity tracked by the POS."""
        global current_item_count
        try:
            qty = int(quantity)
        except (TypeError, ValueError):
            qty = 1
        qty = max(1, qty)
        current_item_count = qty
        self.current_item_count = qty
        if status_message:
            bar = getattr(self, "_status_bar", None)
            if bar:
                bar.showMessage(status_message.format(qty=qty), 2500)
        if log_message:
            self.log_user_action(log_message, str(qty))
    def init_ui(self):
        # Create layout structure
        main_layout = QHBoxLayout()
        self.central_widget.setLayout(main_layout)
        # Left side: POS operations
        pos_layout = QVBoxLayout()
        # Adjusted stretch to match the image better (left side narrower)
        main_layout.addLayout(pos_layout, stretch=3)
        # Input Frame for Barcode and Search
        input_layout = QVBoxLayout()  # Changed to QVBoxLayout for vertical alignment
        pos_layout.addLayout(input_layout)
        # Product Search Label and ComboBox
        search_layout = QHBoxLayout()
        lbl_search = QLabel("Product Search:")
        lbl_search.setFont(QFont("Arial", 15, QFont.Weight.Bold))
        search_layout.addWidget(lbl_search)
        # Updated product search combobox setup using QCompleter with filtering model
        self.entry_product_search = QComboBox()
        self.entry_product_search.setEditable(True) # Make it editable for search
        # Removed setFixedWidth
        self.entry_product_search.setFont(QFont("Arial", 14))
        self.entry_product_search.lineEdit().setAlignment(Qt.AlignmentFlag.AlignLeft)
        self.setup_product_search_combobox()
        search_layout.addWidget(self.entry_product_search, stretch=1) # Allow it to expand
        input_layout.addLayout(search_layout)
        # Customer queue tabs and controls
        queue_layout = QHBoxLayout()
        queue_label = QLabel("Customer Queue:")
        queue_label.setFont(QFont("Arial", 14, QFont.Weight.Bold))
        queue_layout.addWidget(queue_label)
        self.customer_tabs = QTabWidget()
        self.customer_tabs.setTabsClosable(True)
        tab_bar = self.customer_tabs.tabBar()
        tab_bar.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        tab_bar.customContextMenuRequested.connect(self.show_customer_tab_context_menu)
        self.customer_tabs.tabCloseRequested.connect(self.close_customer_session)
        self.customer_tabs.currentChanged.connect(self.on_customer_tab_changed)
        queue_layout.addWidget(self.customer_tabs, stretch=1)
        self._install_customer_tab_shortcuts()
        self.btn_add_customer = QPushButton("Add Customer")
        self.btn_add_customer.setFont(QFont("Arial", 12, QFont.Weight.Bold))
        self.btn_add_customer.setStyleSheet("padding: 6px 12px;")
        self.btn_add_customer.clicked.connect(lambda: self.add_customer_session())
        queue_layout.addWidget(self.btn_add_customer)
        self.btn_start_simulation = QPushButton("Start Simulation")
        self.btn_start_simulation.setFont(QFont("Arial", 12, QFont.Weight.Bold))
        self.btn_start_simulation.setStyleSheet("padding: 6px 12px;")
        self.btn_start_simulation.setToolTip("Run a three-customer practice scenario with timing and accuracy feedback.")
        self.btn_start_simulation.clicked.connect(self.simulation_manager.start_simulation)
        queue_layout.addWidget(self.btn_start_simulation)
        pos_layout.addLayout(queue_layout)
        # Cart display list
        self.listbox = QListWidget()
        # Removed setFixedHeight for responsiveness
        self.listbox.setFont(QFont("Arial", 20))
        self.listbox.setFixedHeight(600)  # Set to any pixel height
        self.apply_listbox_style(self.current_effective_theme)
        pos_layout.addWidget(self.listbox)
        # Total label
        total_layout = QHBoxLayout() # New layout for total to handle alignment
        total_layout.addStretch(1) # Push total to the right
        self.label_total = QLabel("Total: P0.00")
        self.label_total.setFont(QFont("Arial", 20, QFont.Weight.Bold))
        self.label_total.setStyleSheet("color: #0f766e;")
        total_layout.addWidget(self.label_total)
        self.label_total_amount = QLabel("") # Separate label for the amount
        self.label_total_amount.setFont(QFont("Arial", 20, QFont.Weight.Bold))
        self.label_total_amount.setStyleSheet("color: #0f766e;")
        total_layout.addWidget(self.label_total_amount)
        pos_layout.addLayout(total_layout) # Add the new total_layout to pos_layout
        # Inside POSMainWindow.init_ui, after creating pos_layout (left vertical layout):
        # Add image label to bottom-left corner
        self.bottom_left_image_label = QLabel()
        self.bottom_left_image_label.setAlignment(Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignBottom)
        # Load the image from a PNG file in the current directory or resource folder
        image_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "sunnyware.png")  # Change to your actual file name if needed
        print(f"Looking for image at: {image_path}")  # Debugging line
        if os.path.exists(image_path):
            pixmap = QPixmap(image_path)
            # Scale pixmap to fit in fixed label size preserving aspect ratio
            pixmap = pixmap.scaled(300, 200, Qt.AspectRatioMode.KeepAspectRatio, Qt.TransformationMode.SmoothTransformation)
            self.bottom_left_image_label.setPixmap(pixmap)
        else:
            # If image does not exist, optionally set a placeholder
            self.bottom_left_image_label.setText("Image not found")
            self.bottom_left_image_label.setStyleSheet("color: gray; font-style: italic;")
        self.bottom_left_image_label.setFixedSize(300, 200)
        self.bottom_left_image_label.setContentsMargins(0, 0, 0, 0)
        # Add a vertical spacer to push the image label to the bottom in pos_layout
        from PyQt6.QtWidgets import QSpacerItem, QSizePolicy
        vertical_spacer = QSpacerItem(20, 40, QSizePolicy.Policy.Minimum, QSizePolicy.Policy.Expanding)
        pos_layout.addItem(vertical_spacer)          # push next widget to bottom
        pos_layout.addWidget(self.bottom_left_image_label, alignment=Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignBottom)
        # This will anchor the bottom_left_image_label at the bottom-left corner of the left pos_layout.
        # Right side: Product info and image
        product_display_frame = QVBoxLayout()
        # Adjusted stretch to match the image better (right side wider)
        main_layout.addLayout(product_display_frame)
        # Group for Product Info (Image and Details)
        info_group = QGroupBox()
        info_group.setMinimumWidth(660)
        info_group.setMaximumWidth(720)
        info_group.setFixedHeight(520)
        info_group.setStyleSheet("QGroupBox { border: 1px solid #CCC; border-radius: 8px; background-color: white; }") # Added styling
        info_layout = QVBoxLayout()
        info_group.setLayout(info_layout) # Set layout for the group box
        self.info_group = info_group
        # Product Image Section
        lbl_image_title = QLabel("PRODUCT INFORMATION")
        lbl_image_title.setAlignment(Qt.AlignmentFlag.AlignCenter)
        lbl_image_title.setFont(QFont("Arial", 20, QFont.Weight.Bold))
        info_layout.addWidget(lbl_image_title, alignment=Qt.AlignmentFlag.AlignCenter) # Added directly to info_layout
        self.default_pixmap = QPixmap(640, 200)
        self.default_pixmap.fill(QColor("#D9D9D9"))  # Light grey placeholder sized for the preview frame
        self.label_product_image = QLabel()
        self.label_product_image.setPixmap(self.default_pixmap)
        self.label_product_image.setFixedSize(640, 200)
        self.label_product_image.setMinimumSize(640, 200)  # Minimum size for the image area
        self.label_product_image.setStyleSheet("border: 1px solid black; background-color: white;")
        info_layout.addWidget(self.label_product_image, alignment=Qt.AlignmentFlag.AlignCenter) # Added directly to info_layout
        self.btn_change_image = QPushButton("Change Product Image")
        self.btn_change_image.clicked.connect(self.change_current_product_image)
        self.btn_change_image.setEnabled(False)
        info_layout.addWidget(self.btn_change_image, alignment=Qt.AlignmentFlag.AlignCenter)
        self.update_change_image_button_state()
        # Product Details Section
        self.label_product_name_display = QLabel("PRODUCT NAME: ")
        self.label_product_name_display.setFont(QFont("Arial", 15))
        self.label_product_name_display.setWordWrap(False)  # Ensure word wrap disabled to favor one line
        info_layout.addWidget(self.label_product_name_display, alignment=Qt.AlignmentFlag.AlignLeft)
        self.label_product_price_display = QLabel("PRICE: ")
        self.label_product_price_display.setFont(QFont("Arial", 15))
        self.label_product_price_display.setStyleSheet("color: #0f766e;")
        info_layout.addWidget(self.label_product_price_display, alignment=Qt.AlignmentFlag.AlignLeft)
        self.label_product_stock_display = QLabel("STOCK: ")
        self.label_product_stock_display.setFont(QFont("Arial", 15))
        info_layout.addWidget(self.label_product_stock_display, alignment=Qt.AlignmentFlag.AlignLeft)
        self.label_product_barcode_number = QLabel("CODE/STOCK: ")
        self.label_product_barcode_number.setFont(QFont("Arial", 15))
        info_layout.addWidget(self.label_product_barcode_number, alignment=Qt.AlignmentFlag.AlignLeft)
        # Set the layout for the info group and add it to the main product display frame
        product_display_frame.addWidget(info_group)
        # Create a grid layout for buttons
        buttons_grid_layout = QGridLayout()
        self.action_buttons = {}
        button_specs = [
            ("DISCOUNT", self.set_discount),
            ("SET QUANTITY", self.set_item_count),
            ("INVENTORY", self.inventory_management),
            ("SALES SUMMARY", self.summary_view),
            ("VOID", self.void_selected_item),
            ("CHECKOUT", self.checkout),
        ]
        fixed_button_height = 90
        self.set_quantity_button = None
        for index, (text, slot) in enumerate(button_specs):
            btn = QPushButton(text)
            btn.setMinimumSize(160, fixed_button_height)
            btn.setFixedHeight(fixed_button_height)
            btn.setCursor(Qt.CursorShape.PointingHandCursor)
            btn.setObjectName(f"ActionButton_{text.replace(' ', '_')}")
            btn.clicked.connect(slot)
            if text == "SET QUANTITY":
                btn.setToolTip("Set quantity for the next item (Ctrl+Q)")
                self.set_quantity_button = btn
            row = index // 2
            col = index % 2
            buttons_grid_layout.addWidget(btn, row, col)
            self.action_buttons[text] = btn
        self.update_action_button_styles(self.current_effective_theme)
        self.quantity_shortcut_action = QAction("Set Quantity", self)
        self.quantity_shortcut_action.setShortcut(QKeySequence("Ctrl+Q"))
        self.quantity_shortcut_action.setShortcutContext(Qt.ShortcutContext.ApplicationShortcut)
        self.quantity_shortcut_action.triggered.connect(self.set_item_count)
        self.addAction(self.quantity_shortcut_action)
        self.product_search_shortcut_action = QAction("Focus Product Search", self)
        self.product_search_shortcut_action.setShortcut(QKeySequence("Ctrl+S"))
        self.product_search_shortcut_action.setShortcutContext(Qt.ShortcutContext.ApplicationShortcut)
        self.product_search_shortcut_action.triggered.connect(self.focus_product_search_box)
        self.addAction(self.product_search_shortcut_action)
        # If desired, add empty stretch or spacer to fill the last grid cell (row=2, col=1)
        # Set the layout for the info group and add it to the main layout
        # Add the grid layout directly to the product_display_frame, below the info_group
        product_display_frame.addLayout(buttons_grid_layout)
        product_display_frame.addStretch(1) # Add a stretch to push info_group to the top of its frame
        # Menu bar with Archive menu
        menubar = self.menuBar()
        self.setup_theme_menu(menubar)
        archive_menu = menubar.addMenu("Archive")
        view_archive_action = QAction("View Archived Receipts", self)
        view_archive_action.triggered.connect(self.show_archive_labels)
        archive_menu.addAction(view_archive_action)
        sales_archive_action = QAction("Sales Summary Archive", self)
        sales_archive_action.triggered.connect(self.show_sales_summary_archive)
        archive_menu.addAction(sales_archive_action)
        logs_menu = menubar.addMenu("Logs / History")
        view_logs_action = QAction("View Activity Logs", self)
        view_logs_action.triggered.connect(self.show_activity_logs)
        logs_menu.addAction(view_logs_action)
        # Setup signals to handle selection from completer
        self.setup_product_search_signals()
        # Add this in POSMainWindow.__init__ or __init_ui__ after creating self.listbox:    
        self.listbox.setSelectionMode(QListWidget.SelectionMode.SingleSelection)  # Only single item selection allowed
        self.listbox.currentRowChanged.connect(self.display_selected_cart_item)
        self.listbox.itemDoubleClicked.connect(self.prompt_cart_item_quantity_update)
        self.apply_theme_styles(self.current_effective_theme)
    def init_barcode_scanner(self):
        if self.scanner_worker:
            try:
                self.scanner_worker.stop()
            except Exception:
                pass
            self.scanner_worker = None
        if serial is None or list_ports is None:
            self.scanner_worker = None
            return
        self.scanner_worker = BarcodeScannerWorker(parent=self)
        self.scanner_worker.barcode_scanned.connect(self.on_scanner_barcode)
        self.scanner_worker.status_changed.connect(self.on_scanner_status_changed)
        self.scanner_worker.start()
    def on_scanner_status_changed(self, status):
        # Status updates are logged for debugging but not shown in the UI.
        if status:
            print(f"[Scanner] {status}")
    def on_scanner_barcode(self, barcode_value):
        barcode_value = (barcode_value or "").strip()
        if not barcode_value:
            return
        self.process_scanned_code(barcode_value)
    def _install_customer_tab_shortcuts(self):
        if self.customer_tab_shortcuts:
            return
        for idx in range(1, 10):
            sequence = QKeySequence(f"Ctrl+{idx}")
            shortcut = QShortcut(sequence, self)
            shortcut.activated.connect(partial(self._activate_customer_tab_by_shortcut, idx - 1))
            self.customer_tab_shortcuts.append(shortcut)

    def _activate_customer_tab_by_shortcut(self, index):
        if self.customer_tabs is None:
            return
        if 0 <= index < self.customer_tabs.count():
            self.customer_tabs.setCurrentIndex(index)

    def show_customer_tab_context_menu(self, position):
        if self.customer_tabs is None:
            return
        tab_bar = self.customer_tabs.tabBar()
        index = tab_bar.tabAt(position)
        if index < 0 or index >= len(self.customer_sessions):
            return
        menu = QMenu(self)
        rename_action = menu.addAction("Rename Customer")
        selected_action = menu.exec(tab_bar.mapToGlobal(position))
        if selected_action == rename_action:
            self.prompt_rename_customer_session(index)

    def prompt_rename_customer_session(self, index):
        if index < 0 or index >= len(self.customer_sessions):
            return
        current_name = self.customer_sessions[index].get("name") or f"Customer {index + 1}"
        try:
            new_name, ok = QInputDialog.getText(
                self,
                "Rename Customer",
                "Customer name:",
                text=current_name,
            )
        except Exception:
            return
        if not ok:
            return
        new_name = new_name.strip()
        if not new_name:
            return
        self.customer_sessions[index]["name"] = new_name
        self.update_customer_tab_labels()

    def _generate_next_customer_name(self):
        name = f"Customer {self.customer_name_counter}"
        self.customer_name_counter += 1
        return name

    def initialize_customer_queue(self):
        if self.customer_tabs is None:
            return
        self.customer_name_counter = 1
        self.customer_tabs.blockSignals(True)
        while self.customer_tabs.count():
            self.customer_tabs.removeTab(0)
        self.customer_tabs.blockSignals(False)
        self.customer_sessions = []
        self.add_customer_session(set_active=True)
    def add_customer_session(self, set_active=True):
        if self.customer_tabs is None:
            return
        # Ensure internal list stays aligned with tab order
        session_name = self._generate_next_customer_name()
        session = {"cart": [], "name": session_name}
        tab_placeholder = QWidget()
        index = self.customer_tabs.addTab(tab_placeholder, "")
        if index >= len(self.customer_sessions):
            self.customer_sessions.append(session)
        else:
            self.customer_sessions.insert(index, session)
        self.update_customer_tab_labels()
        if set_active:
            self.customer_tabs.setCurrentIndex(index)
        else:
            # Update view in case we inserted without activating
            self.on_customer_tab_changed(self.customer_tabs.currentIndex())
        return index
    def close_customer_session(self, index):
        if index < 0 or index >= len(self.customer_sessions):
            return
        session = self.customer_sessions[index]
        if session["cart"]:
            response = QMessageBox.question(
                self,
                "Remove Customer",
                "This customer still has items in the cart. Remove them from the queue?",
                QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
                QMessageBox.StandardButton.No,
            )
            if response != QMessageBox.StandardButton.Yes:
                return
        self.customer_sessions.pop(index)
        self.customer_tabs.blockSignals(True)
        self.customer_tabs.removeTab(index)
        self.customer_tabs.blockSignals(False)
        if not self.customer_sessions:
            self.customer_name_counter = 1
            self.add_customer_session(set_active=True)
        else:
            next_index = min(index, len(self.customer_sessions) - 1)
            self.customer_tabs.setCurrentIndex(next_index)
        self.update_customer_tab_labels()
        # Refresh active customer cart display after closing a tab
        active_index = self.customer_tabs.currentIndex() if self.customer_tabs else -1
        if active_index != -1:
            self.on_customer_tab_changed(active_index)
    def update_customer_tab_labels(self):
        if self.customer_tabs is None:
            return
        for idx in range(self.customer_tabs.count()):
            session_name = ""
            if 0 <= idx < len(self.customer_sessions):
                session_name = self.customer_sessions[idx].get("name", "")
            if not session_name:
                session_name = f"Customer {idx + 1}"
            self.customer_tabs.setTabText(idx, session_name)
    def on_customer_tab_changed(self, index):
        if index < 0 or index >= len(self.customer_sessions):
            self.cart = []
            self.listbox.blockSignals(True)
            self.listbox.clear()
            self.listbox.blockSignals(False)
            self.update_total()
            self.clear_product_display()
            return
        self.cart = self.customer_sessions[index]["cart"]
        self.refresh_cart_display()
    def refresh_cart_display(self):
        if not hasattr(self, "listbox") or self.listbox is None:
            return
        self.listbox.blockSignals(True)
        self.listbox.clear()
        for item in self.cart:
            self.listbox.addItem(self.format_cart_item_label(item))
        self.listbox.blockSignals(False)
        self.update_total()
        self.clear_product_display()
    def format_cart_item_label(self, item):
        sku = item.get("Stock No.", "")
        identifier = render_product_identifier(item.get("code"), sku) or sku
        name_text = sanitize_product_name(item.get("name"))
        qty = item.get("qty", 1)
        inventory_usage = item.get("inventory_usage", 1) or 1
        display_qty = qty * inventory_usage
        if abs(display_qty - int(display_qty)) < 1e-6:
            display_qty = int(display_qty)
        line_total = item.get("price", 0) * qty
        suffix = " (Bundle)" if item.get("bundle_components") else ""
        if suffix and not name_text:
            name_segment = suffix.strip()
        else:
            name_segment = f"{name_text}{suffix}".strip()
        descriptor_parts = [part for part in (identifier, name_segment) if part]
        descriptor = " ".join(descriptor_parts).strip() or (identifier or name_segment or "Item")
        total_display = "FREE" if item.get("is_freebie") else f"P{line_total:.2f}"
        price_segment = f"- {total_display}" if total_display else ""
        return f"{descriptor} x{display_qty} {price_segment}".strip()
    def handle_session_after_checkout(self):
        if self.customer_tabs is None or not self.customer_sessions:
            return
        current_index = self.customer_tabs.currentIndex()
        if current_index < 0:
            return
        # Current cart already cleared before invoking this method
        if len(self.customer_sessions) > 1:
            self.customer_sessions.pop(current_index)
            self.customer_tabs.blockSignals(True)
            self.customer_tabs.removeTab(current_index)
            self.customer_tabs.blockSignals(False)
            if self.customer_sessions:
                next_index = min(current_index, len(self.customer_sessions) - 1)
                self.customer_tabs.setCurrentIndex(next_index)
        else:
            # Keep a single empty session ready for the next customer
            self.customer_sessions[0]["cart"] = self.cart
            self.refresh_cart_display()
        self.update_customer_tab_labels()
        # Ensure cart display refreshes for the newly active customer tab
        active_index = self.customer_tabs.currentIndex() if self.customer_tabs else -1
        if active_index != -1:
            self.on_customer_tab_changed(active_index)
    def display_selected_cart_item(self, current_row):
        """
        When the user selects an item in the cart listbox, display its product info.
        """
        if current_row < 0 or current_row >= len(self.cart):
            self.clear_product_display()
            return
        item = self.cart[current_row]
        sku = item.get('Stock No.')
        base_barcode = item.get('base_stock_no', sku)
        variant_index = item.get('variant_index', 0)
        if item.get("bundle_components"):
            component_summary = ", ".join(
                f"{comp.get('quantity', 1)}x {comp.get('name', comp.get('barcode', ''))}"
                for comp in item.get("bundle_components", [])
            ) or "No components"
            self.label_product_name_display.setText(f"Bundle: {item['name']}")
            self.label_product_price_display.setText(f"Price: P{item['price']:.2f}")
            self.label_product_stock_display.setText("Bundle Item")
            self.label_product_barcode_number.setText(f"Includes: {component_summary}")
            self.display_product_image(item.get("image_filename"), sku)
            self.set_display_context(None, None, item.get('bundle_code'))
            return
        variants = products.get(base_barcode, [])
        variant = variants[variant_index] if variant_index < len(variants) else (variants[0] if variants else None)
        if variant:
            self.label_product_name_display.setText(f"Name: {item['name']}")
            self.label_product_price_display.setText(f"Price: P{item['price']:.2f}")
            self.label_product_stock_display.setText(f"Stock: {variant['stock']}")
            identifier = render_product_identifier(item.get("code"), sku)
            display_identifier = identifier or (sku or "")
            self.label_product_barcode_number.setText(f"Code/Stock: {display_identifier}")
            self.display_product_image(variant.get('image_filename'), sku)
            self.set_display_context(base_barcode, variant_index, item.get('bundle_code'))
        else:
            self.clear_product_display()

    def prompt_cart_item_quantity_update(self, list_item):
        """
        Prompt for a new quantity when a cart row is double-clicked.
        """
        if list_item is None or not hasattr(self, "listbox"):
            return
        row = self.listbox.row(list_item)
        if row < 0 or row >= len(self.cart):
            return
        cart_entry = self.cart[row]
        if cart_entry.get("is_freebie"):
            show_warning("Quantity Locked", "Freebie quantities cannot be changed.", self)
            return
        current_qty = cart_entry.get("qty", 1)
        try:
            current_qty = max(1, int(current_qty))
        except (TypeError, ValueError):
            current_qty = 1
        product_name = cart_entry.get("name") or cart_entry.get("Stock No.") or "Item"
        prompt_text = f"Enter new quantity for '{product_name}':"
        new_qty, ok = QInputDialog.getInt(
            self,
            "Update Item Quantity",
            prompt_text,
            current_qty,
            min=1,
            max=10000,
        )
        if not ok or new_qty == current_qty:
            return
        cart_entry["qty"] = new_qty
        self.listbox.blockSignals(True)
        list_item.setText(self.format_cart_item_label(cart_entry))
        self.listbox.blockSignals(False)
        self.listbox.setCurrentRow(row)
        self.update_total()
        self.display_selected_cart_item(row)
        self.log_user_action("Updated cart item quantity", f"{product_name} x{new_qty}")

    def void_selected_item(self):
        """Remove the selected item from the cart without requiring a password."""
        selected_row = self.listbox.currentRow()
        if selected_row < 0:
            show_warning("Void Item", "Please select an item from the cart to void.", self)
            return
        if selected_row >= len(self.cart):
            show_error("Void Item", "Unable to locate the selected cart item.", self)
            return
        voided_item = self.cart.pop(selected_row)
        self.listbox.takeItem(selected_row)
        self.update_total()
        self.clear_product_display()
        if voided_item:
            details = f"{voided_item.get('name', 'Unknown Item')} x{voided_item.get('qty', 1)}"
            self.log_user_action("Voided cart item", details)
        # Update total
        self.update_total()
        show_info("Item Voided", f"'{voided_item['name']}' has been removed from the cart.", self)
    def _build_product_search_display(self, sku, data):
        identifier = render_product_identifier(data.get("code"), sku)
        if identifier:
            return f"{identifier} {data['name']} ({sku})"
        return f"{data['name']} ({sku})"

    def setup_product_search_combobox(self):
        # Initial setup for the combobox to be editable with styling and completer
        self.entry_product_search.setEditable(True)
        self.entry_product_search.setFixedWidth(1200)
        self.entry_product_search.setFont(QFont("Segoe UI", 20))
        self.entry_product_search.lineEdit().setAlignment(Qt.AlignmentFlag.AlignLeft)
        self.apply_combobox_style(self.current_effective_theme)
        # Store full product list as display strings: "Product Name (barcode)"
        self._product_search_list = [
            self._build_product_search_display(sku, data) for sku, data in product_variant_lookup.items()
        ]
        self.entry_product_search.clear()
        self.entry_product_search.addItems(self._product_search_list)
        # Setup completer with case-insensitive contains matching
        self._completer_model = QStringListModel(self._product_search_list)
        self._completer = QCompleter(self._completer_model, self.entry_product_search)
        self._completer.setCaseSensitivity(Qt.CaseSensitivity.CaseInsensitive)
        self._completer.setFilterMode(Qt.MatchFlag.MatchContains)
        self._completer.setCompletionMode(QCompleter.CompletionMode.PopupCompletion)
        self.entry_product_search.setCompleter(self._completer)
        # Connect to update completer model on typing for dynamic filtering
        self.entry_product_search.lineEdit().textEdited.connect(self.filter_product_search_list)
        # Ensure search box starts blank instead of displaying the first product
        self.entry_product_search.setCurrentIndex(-1)
        self.entry_product_search.clearEditText()
    def filter_product_search_list(self, text):
        # Filter underlying model of completer based on typed text to update dropdown options.
        text_lower = text.lower().strip()
        if not text_lower:
            # Show no completions when empty to avoid list show
            self._completer_model.setStringList([])
            return
        matches = []

        def evaluate_match(field_text, base_priority):
            if not field_text:
                return None
            idx = field_text.find(text_lower)
            if idx == -1:
                return None
            # Prefix matches have higher priority than contains matches
            prefix_bucket = 0 if idx == 0 else 3
            return (base_priority + prefix_bucket, idx, len(field_text))

        for sku, data in product_variant_lookup.items():
            data = data or {}
            display_text = self._build_product_search_display(sku, data)
            name_value = (data.get('name') or "").lower()
            code_value = (data.get('code') or "").lower()
            sku_value = str(sku or "").lower()
            ranking_candidates = [
                evaluate_match(name_value, 0),
                evaluate_match(code_value, 1),
                evaluate_match(sku_value, 2),
            ]
            ranking_candidates = [candidate for candidate in ranking_candidates if candidate is not None]
            if not ranking_candidates:
                continue
            best_rank = min(ranking_candidates)
            matches.append((best_rank, display_text))
        matches.sort(key=lambda entry: (entry[0][0], entry[0][1], entry[0][2], entry[1].lower()))
        filtered = [entry[1] for entry in matches]
        self._completer_model.setStringList(filtered)
    def setup_product_search_signals(self):
        self._search_selection_in_progress = False
        self._completer.activated.connect(self.on_product_search_selected)
        line_edit = self.entry_product_search.lineEdit()
        line_edit.returnPressed.connect(self.on_product_search_return_pressed)
        dropdown_view = self.entry_product_search.view()
        dropdown_view.clicked.connect(self.on_product_search_dropdown_index_triggered)
        dropdown_view.activated.connect(self.on_product_search_dropdown_index_triggered)

    def on_product_search_return_pressed(self):
        if getattr(self, "_search_selection_in_progress", False):
            return
        text = self.entry_product_search.currentText().strip()
        if not text:
            return
        self.on_product_search_selected(text)

    def on_product_search_dropdown_index_triggered(self, model_index):
        if getattr(self, "_search_selection_in_progress", False):
            return
        if not model_index or not model_index.isValid():
            return
        display_text = model_index.data(Qt.ItemDataRole.DisplayRole)
        if not display_text:
            return
        self.on_product_search_selected(str(display_text))
    def refresh_product_search_options(self):
        if not hasattr(self, "_completer_model"):
            return
        self._product_search_list = [
            self._build_product_search_display(sku, data) for sku, data in product_variant_lookup.items()
        ]
        current_text = self.entry_product_search.currentText()
        self.entry_product_search.blockSignals(True)
        self.entry_product_search.clear()
        self.entry_product_search.addItems(self._product_search_list)
        self.entry_product_search.setCurrentText(current_text)
        self.entry_product_search.blockSignals(False)
        self._completer_model.setStringList(self._product_search_list)
        self.apply_combobox_style(self.current_effective_theme)
    def setup_theme_menu(self, menubar):
        """Create theme selection actions under a View menu."""
        view_menu = menubar.addMenu("View")
        self.theme_actions = {}
        self.theme_action_group = QActionGroup(self)
        self.theme_action_group.setExclusive(True)
        options = [
            ("light", "Light Mode"),
            ("dark", "Dark Mode"),
            ("system", "Follow System Theme"),
        ]
        for mode, label in options:
            action = QAction(label, self)
            action.setCheckable(True)
            action.triggered.connect(lambda checked, m=mode: self.set_theme_mode(m))
            self.theme_action_group.addAction(action)
            view_menu.addAction(action)
            self.theme_actions[mode] = action
        self.sync_theme_actions()
    def sync_theme_actions(self):
        """Ensure the checked menu action reflects the current theme preference."""
        for mode, action in self.theme_actions.items():
            action.blockSignals(True)
            action.setChecked(mode == self.current_theme_mode)
            action.blockSignals(False)
    def set_theme_mode(self, mode):
        """Apply the requested theme, persist it, and update UI styling."""
        app = QApplication.instance()
        if app is None:
            return
        applied = apply_theme(app, mode)
        save_ui_preferences(mode)
        self.current_theme_mode = mode
        self.current_effective_theme = applied
        self.apply_theme_styles(applied)
        self.sync_theme_actions()
    def apply_theme_styles(self, effective_theme):
        """Refresh widget-level styling to match the current theme."""
        self.apply_combobox_style(effective_theme)
        self.apply_listbox_style(effective_theme)
        self.update_action_button_styles(effective_theme)
        accent_color = "#0f766e" if effective_theme == "light" else "#7dd3fc"
        if getattr(self, "label_total", None) is not None:
            self.label_total.setStyleSheet(f"color: {accent_color};")
        if getattr(self, "label_total_amount", None) is not None:
            self.label_total_amount.setStyleSheet(f"color: {accent_color};")
        if getattr(self, "label_product_price_display", None) is not None:
            self.label_product_price_display.setStyleSheet(f"color: {accent_color};")
        if hasattr(self, "info_group") and self.info_group is not None:
            if effective_theme == "dark":
                self.info_group.setStyleSheet(
                    "QGroupBox { border: 1px solid #334155; border-radius: 8px; background-color: #111827; }"
                )
            else:
                self.info_group.setStyleSheet(
                    "QGroupBox { border: 1px solid #d1d5db; border-radius: 8px; background-color: #ffffff; }"
                )
        if self.label_product_image is not None:
            if effective_theme == "dark":
                self.label_product_image.setStyleSheet("border: 1px solid #334155; background-color: #0f172a;")
            else:
                self.label_product_image.setStyleSheet("border: 1px solid black; background-color: white;")
    def apply_combobox_style(self, theme):
        """Apply theme-aware styling to the product search dropdown."""
        if not hasattr(self, "entry_product_search") or self.entry_product_search is None:
            return
        if theme == "dark":
            stylesheet = """
                QComboBox {
                    background-color: #1f2937;
                    border: 1px solid #374151;
                    padding: 6px 12px;
                    font-family: 'Segoe UI', Tahoma, Geneva, Verdana, sans-serif;
                    font-size: 20px;
                    color: #f3f4f6;
                }
                QComboBox QAbstractItemView {
                    border: 1px solid #374151;
                    selection-background-color: #2563eb;
                    background-color: #111827;
                    color: #f3f4f6;
                    font-size: 20px;
                }
            """
        else:
            stylesheet = """
                QComboBox {
                    background-color: #ffffff;
                    border: 1px solid #d1d5db;
                    padding: 6px 12px;
                    font-family: 'Segoe UI', Tahoma, Geneva, Verdana, sans-serif;
                    font-size: 20px;
                    color: #374151;
                }
                QComboBox QAbstractItemView {
                    border: 1px solid #d1d5db;
                    selection-background-color: #2563eb;
                    color: #111827;
                    background-color: #ffffff;
                    font-size: 20px;
                }
            """
        self.entry_product_search.setStyleSheet(stylesheet)
    def apply_listbox_style(self, theme):
        """Apply theme-aware styling to the cart list widget."""
        if not hasattr(self, "listbox") or self.listbox is None:
            return
        if theme == "dark":
            self.listbox.setStyleSheet("""
                QListWidget {
                    background-color: #0f172a;
                    border: 1px solid #334155;
                    color: #f8fafc;
                    selection-background-color: #2563eb;
                    selection-color: #f8fafc;
                }
            """)
        else:
            self.listbox.setStyleSheet("""
                QListWidget {
                    background-color: #ffffff;
                    border: 1px solid #d1d5db;
                    color: #111827;
                    selection-background-color: #2563eb;
                    selection-color: #ffffff;
                }
            """)
    def update_action_button_styles(self, theme):
        """Apply pastel styling to the primary action buttons."""
        if not hasattr(self, "action_buttons") or not self.action_buttons:
            return
        tokens = get_theme_tokens(theme)
        pastel_palette = {
            "DISCOUNT": {
                "base": "#fde2e4",
                "hover": "#fbc5d3",
                "pressed": "#f7a8c2",
                "border": "#f09ab5",
                "disabled": "#fbe4e8",
            },
            "SET QUANTITY": {
                "base": "#d5f5e3",
                "hover": "#bff0d4",
                "pressed": "#a8eac4",
                "border": "#92dcb0",
                "disabled": "#e3f7ed",
            },
            "INVENTORY": {
                "base": "#e2f0ff",
                "hover": "#cfe5ff",
                "pressed": "#bdd9ff",
                "border": "#a7c9f5",
                "disabled": "#e8f3ff",
            },
            "SALES SUMMARY": {
                "base": "#ede4ff",
                "hover": "#dcd0ff",
                "pressed": "#ccbaff",
                "border": "#bca4f3",
                "disabled": "#f1eaff",
            },
            "VOID": {
                "base": "#fef3e2",
                "hover": "#fddfba",
                "pressed": "#fcc992",
                "border": "#f5b87c",
                "disabled": "#feeed4",
            },
            "CHECKOUT": {
                "base": "#daf5ff",
                "hover": "#c1ecff",
                "pressed": "#a8e2ff",
                "border": "#8fd6f5",
                "disabled": "#e5f8ff",
            },
        }
        text_color = "#1f2937"
        disabled_text = tokens["muted"]
        for label, button in self.action_buttons.items():
            swatch = pastel_palette.get(label, pastel_palette.get("INVENTORY"))
            button.setStyleSheet(f"""
                QPushButton {{
                    background-color: {swatch['base']};
                    color: {text_color};
                    border-radius: 12px;
                    padding: 14px 18px;
                    font-size: 22px;
                    font-weight: 600;
                    border: 1px solid {swatch['border']};
                }}
                QPushButton:hover {{
                    background-color: {swatch['hover']};
                }}
                QPushButton:pressed {{
                    background-color: {swatch['pressed']};
                }}
                QPushButton:disabled {{
                    background-color: {swatch['disabled']};
                    color: {disabled_text};
                    border: 1px solid {swatch['border']};
                }}
            """)
    def remove_existing_freebies_from_cart(self):
        """Remove any previously added freebies from the cart and UI list."""
        if not self.cart:
            return
        indices_to_remove = [idx for idx, item in enumerate(self.cart) if item.get("is_freebie")]
        if not indices_to_remove:
            return
        removed_details = []
        for offset, idx in enumerate(indices_to_remove):
            adjusted_index = idx - offset
            removed_item = self.cart.pop(adjusted_index)
            if removed_item:
                removed_details.append(f"{removed_item.get('name', 'Freebie')} x{removed_item.get('qty', 1)}")
            if 0 <= adjusted_index < self.listbox.count():
                self.listbox.takeItem(adjusted_index)
        self.update_total()
        if removed_details:
            self.log_user_action("Removed freebies from cart", "; ".join(removed_details))
    def evaluate_basket_freebies(self, subtotal):
        """Return the list of basket promos the subtotal qualifies for."""
        qualified = []
        if not basket_promos:
            return qualified
        for promo in basket_promos:
            threshold = promo.get("threshold", 0)
            if subtotal >= threshold:
                freebies = promo.get("freebies") or []
                valid_items = []
                for entry in freebies:
                    barcode = entry.get("barcode") or entry.get("Stock No.") or entry.get("sku")
                    if not barcode:
                        continue
                    try:
                        qty = int(entry.get("quantity", 1))
                    except (TypeError, ValueError):
                        qty = 1
                    if qty <= 0:
                        continue
                    try:
                        variant_index = int(entry.get("variant_index", 0))
                    except (TypeError, ValueError):
                        variant_index = 0
                    valid_items.append({
                        "barcode": str(barcode).strip(),
                        "variant_index": max(0, variant_index),
                        "quantity": qty
                    })
                if valid_items:
                    qualified.append({
                        "promo": promo,
                        "items": valid_items
                    })
        return qualified
    def add_freebie_item(self, barcode, variant_index, quantity, promo_code):
        """Append a freebie item to the cart and return the created cart entry."""
        variants = products.get(barcode, [])
        if not variants:
            print(f"Warning: basket promo references unknown product '{barcode}'.")
            return None
        if variant_index >= len(variants):
            print(f"Warning: basket promo uses invalid variant index for '{barcode}'. Using first variant.")
            variant_index = 0
        variant = variants[variant_index]
        available_stock = variant.get("stock", 0)
        if quantity > available_stock:
            print(f"Warning: insufficient stock for freebie '{variant['name']}' ({barcode}). Requested {quantity}, available {available_stock}.")
            return None
        item = {
            "name": variant['name'],
            "price": 0.0,
            "qty": quantity,
            "Stock No.": barcode,
            "code": variant.get("code"),
            "base_stock_no": barcode,
            "variant_index": variant_index,
            "inventory_usage": 1,
            "promo_code": promo_code,
            "original_unit_price": 0.0,
            "is_freebie": True
        }
        self.cart.append(item)
        promo_label = promo_code or "FREEBIE"
        details = f"{item['name']} x{quantity} ({promo_label})"
        self.log_user_action("Added freebie to cart", details)
        self.listbox.addItem(self.format_cart_item_label(item))
        return item
    def apply_basket_freebies_to_cart(self, subtotal):
        """Award qualifying freebies based on the order subtotal."""
        self.remove_existing_freebies_from_cart()
        self.applied_freebies = []
        self.applied_freebie_messages = []
        qualified = self.evaluate_basket_freebies(subtotal)
        if not qualified:
            return
        for entry in qualified:
            promo = entry["promo"]
            promo_code = promo.get("code") or "BASKET_PROMO"
            promo_message = promo.get("message")
            for freebie in entry["items"]:
                added = self.add_freebie_item(
                    freebie["barcode"],
                    freebie["variant_index"],
                    freebie["quantity"],
                    promo_code
                )
                if added:
                    self.applied_freebies.append({
                        "name": added["name"],
                        "qty": added["qty"],
                        "promo": promo_code
                    })
            if promo_message:
                self.applied_freebie_messages.append(promo_message)
        if self.applied_freebies:
            self.update_total()
            rendered = []
            for freebie in self.applied_freebies:
                promo_label = freebie.get("promo")
                suffix = f" ({promo_label})" if promo_label else ""
                rendered.append(f"{freebie.get('name', 'Freebie')} x{freebie.get('qty', 1)}{suffix}")
            summary = ", ".join(rendered)
            self.log_user_action("Awarded basket freebies", summary)
    def on_product_search_selected(self, selected_text):
        if not selected_text:
            return
        if getattr(self, "_search_selection_in_progress", False):
            return
        self._search_selection_in_progress = True
        # Parse barcode from selected_text, update product info display and barcode entry
        try:
            start_idx = selected_text.rfind('(')
            end_idx = selected_text.rfind(')')
            if start_idx != -1 and end_idx != -1:
                sku = selected_text[start_idx + 1:end_idx]
                if not self.add_item_to_cart_by_sku(sku, show_not_found=False):
                    show_warning("Product Not Found", f"Product with SKU '{sku}' not found in database.", self)
                    self.clear_product_display()
                else:
                    self.clear_product_search_entry()
            else:
                show_warning("Format Error", "Invalid product selection format.", self)
                self.clear_product_display()
        finally:
            QTimer.singleShot(0, lambda: setattr(self, "_search_selection_in_progress", False))
    def clear_product_display(self):
        self.label_product_name_display.setText("PRODUCT NAME: ")
        self.label_product_price_display.setText("PRICE: ")
        self.label_product_stock_display.setText("STOCK: ")
        self.label_product_barcode_number.setText("CODE/STOCK: ")
        self.label_product_image.setPixmap(self.default_pixmap)
        self.set_display_context()

    def focus_product_search_box(self):
        """Give focus to the product search field when the shortcut is pressed."""
        if hasattr(self, "entry_product_search") and self.entry_product_search is not None:
            self.entry_product_search.setFocus()
            line_edit = self.entry_product_search.lineEdit()
            if line_edit:
                line_edit.selectAll()

    def display_product_image(self, image_filename, stock_no=None):
        if stock_no is None:
            stock_no = getattr(self, "current_display_barcode", None)
        resolved_filename = resolve_product_image_filename(stock_no, image_filename)
        if resolved_filename:
            image_path = os.path.join(PRODUCT_IMAGE_FOLDER, resolved_filename)
            if os.path.exists(image_path):
                try:
                    pil_image = Image.open(image_path)
                    label_size = self.label_product_image.size()
                    target_size = (max(1, label_size.width()), max(1, label_size.height()))
                    pil_image = pil_image.convert("RGBA")
                    fitted = ImageOps.contain(pil_image, target_size, Image.Resampling.LANCZOS)
                    canvas = Image.new("RGBA", target_size, (255, 255, 255, 0))
                    offset = (
                        (target_size[0] - fitted.width) // 2,
                        (target_size[1] - fitted.height) // 2,
                    )
                    canvas.paste(fitted, offset, fitted if fitted.mode == "RGBA" else None)
                    qt_image = ImageQt.ImageQt(canvas)
                    pixmap = QPixmap.fromImage(qt_image)
                    self.label_product_image.setPixmap(pixmap)
                    return
                except Exception as e:
                    print(f"Error loading product image {image_path}: {e}")
            else:
                print(f"Product image file not found: {image_path}")
        self.label_product_image.setPixmap(self.default_pixmap)
    def set_display_context(self, barcode=None, variant_index=None, bundle_code=None):
        self.current_display_barcode = barcode
        self.current_display_variant_index = variant_index
        self.current_display_bundle_code = bundle_code
        self.update_change_image_button_state()
    def update_change_image_button_state(self):
        if not hasattr(self, "btn_change_image") or self.btn_change_image is None:
            return
        allow_product_change = bool(self.current_display_barcode is not None)
        self.btn_change_image.setEnabled(allow_product_change)
        if allow_product_change:
            self.btn_change_image.setToolTip("Select a new image for this product.")
        else:
            self.btn_change_image.setToolTip("Scan or select a product to change its image.")
    def change_current_product_image(self):
        if not self.current_display_barcode:
            show_info("Select Product", "Scan or select a product first to update its image.", self)
            return
        variants = products.get(self.current_display_barcode)
        if not variants:
            show_error("Update Image", "Current product could not be found in memory.", self)
            return
        variant_index = self.current_display_variant_index or 0
        if variant_index >= len(variants):
            variant_index = 0
        variant = variants[variant_index]
        file_path, _ = QFileDialog.getOpenFileName(
            self, "Select Product Image", "", "Images (*.png *.jpg *.jpeg *.bmp)"
        )
        if not file_path:
            return
        new_filename = copy_image_to_library(file_path, self.current_display_barcode, self)
        if not new_filename:
            return
        variant["image_filename"] = new_filename
        save_products_to_database(self)
        rebuild_product_variant_lookup()
        self.display_product_image(new_filename, self.current_display_barcode)
        self.set_display_context(self.current_display_barcode, variant_index, None)
        show_info("Image Updated", "Product image has been updated.", self)
    def add_item_to_cart_by_sku(self, sku, show_not_found=True, apply_promo_multiplier=False):
        global current_item_count, current_discount
        lookup = product_variant_lookup.get(sku)
        if lookup is None:
            if show_not_found:
                show_warning("Not Found", f"Barcode '{sku}' not found in product database.", self)
                self.display_product_image(None, sku)
            return False
        qty = current_item_count
        promo_multiplier = promo_quantity_multiplier(lookup.get("promo_code"))
        if apply_promo_multiplier and promo_multiplier > 1:
            qty *= promo_multiplier
        price = lookup['price']
        if current_discount > 0:
            price = price * (1 - current_discount / 100)
        price = round(price, 2)
        bundle_components = lookup.get('bundle_components')
        if bundle_components:
            components_copy = deepcopy(bundle_components)
            insufficient = []
            bundle_stock_cap = None
            for component in components_copy:
                barcode = component.get("barcode")
                variant_index = component.get("variant_index", 0)
                component_qty = component.get("quantity", 1)
                variants = products.get(barcode, [])
                if not variants:
                    insufficient.append((component.get("name", barcode), component_qty * qty, 0))
                    continue
                if variant_index >= len(variants):
                    variant_index = 0
                variant = variants[variant_index]
                available = variant.get("stock", 0)
                required = component_qty * qty
                component["name"] = variant.get("name", barcode)
                component["variant_index"] = variant_index
                component["base_price"] = float(variant.get("price", 0))
                if available < required:
                    insufficient.append((component["name"], required, available))
                else:
                    if component_qty > 0:
                        component_cap = available // component_qty
                        bundle_stock_cap = component_cap if bundle_stock_cap is None else min(bundle_stock_cap, component_cap)
            if insufficient:
                details = "\n".join(
                    f"- {name}: need {need}, available {avail}"
                    for name, need, avail in insufficient
                )
                show_error(
                    "Insufficient Stock",
                    f"Not enough stock for bundle '{lookup['name']}' components:\n{details}",
                    self
                )
                self.log_user_action("Add bundle to cart blocked", f"Insufficient stock for '{lookup['name']}' components")
                return False
            item = {
                "name": lookup['name'],
                "price": price,
                "qty": qty,
                "Stock No.": lookup['sku'],
                "code": lookup.get('code'),
                "base_stock_no": None,
                "variant_index": None,
                "inventory_usage": None,
                "promo_code": lookup.get('bundle_code'),
                "bundle_code": lookup.get('bundle_code'),
                "bundle_components": components_copy,
                "original_unit_price": lookup['price'],
                "image_filename": lookup.get('image_filename'),
            }
            self.cart.append(item)
            details = f"{item['name']} bundle x{qty} (SKU {lookup['sku']})"
            if components_copy:
                component_details = ", ".join(
                    f"{comp.get('quantity', 0)}x {comp.get('name', comp.get('barcode', ''))}"
                    for comp in components_copy
                )
                if component_details:
                    details = f"{details} [{component_details}]"
            self.log_user_action("Added bundle to cart", details)
            self.listbox.addItem(self.format_cart_item_label(item))
            component_summary = ", ".join(
                f"{component['quantity']}x {component['name']}"
                for component in components_copy
            )
            self.label_product_name_display.setText(f"BUNDLE: {item['name']}")
            self.label_product_price_display.setText(f"Price: P{lookup['price']:.2f}")
            stock_caption = "Unlimited" if bundle_stock_cap is None else str(bundle_stock_cap)
            self.label_product_stock_display.setText(f"Bundle Stock: {stock_caption}")
            self.label_product_barcode_number.setText(f"Includes: {component_summary}")
            self.display_product_image(lookup.get("image_filename"), lookup.get("sku"))
            self.set_display_context(None, None, item.get("bundle_code"))
            self.clear_product_search_entry()
            current_item_count = 1
            self.current_item_count = 1
            current_discount = 0.0
            self.update_total()
            return True
        base_barcode = lookup['base_barcode']
        variant_index = lookup.get('variant_index', 0)
        variants = products.get(base_barcode, [])
        if not variants:
            if show_not_found:
                show_warning("Not Found", f"Base product '{base_barcode}' not found in product database.", self)
                self.display_product_image(None, lookup.get('sku'))
            return False
        variant = variants[variant_index] if variant_index < len(variants) else variants[0]
        item = {
            "name": lookup['name'],
            "price": price,
            "qty": qty,
            "Stock No.": lookup['sku'],
            "code": lookup.get('code'),
            "base_stock_no": base_barcode,
            "variant_index": variant_index,
            "inventory_usage": lookup.get('inventory_usage', 1),
            "promo_code": lookup.get('promo_code'),
            "original_unit_price": lookup['price'],
            "image_filename": variant.get('image_filename'),
        }
        self.cart.append(item)
        details = f"{item['name']} x{qty} (SKU {lookup['sku']})"
        promo_suffix = item.get("promo_code")
        if promo_suffix:
            details = f"{details} [Promo {promo_suffix}]"
        self.log_user_action("Added item to cart", details)
        self.listbox.addItem(self.format_cart_item_label(item))
        self.label_product_name_display.setText(f"Name: {item['name']}")
        self.label_product_price_display.setText(f"Price: P{lookup['price']:.2f}")
        self.label_product_stock_display.setText(f"Stock: {variant['stock']}")
        identifier = render_product_identifier(lookup.get('code'), lookup['sku'])
        display_identifier = identifier or lookup['sku']
        self.label_product_barcode_number.setText(f"Code/Stock: {display_identifier}")
        self.display_product_image(variant.get('image_filename'), lookup.get('sku'))
        self.set_display_context(base_barcode, variant_index, None)
        self.clear_product_search_entry()
        current_item_count = 1
        self.current_item_count = 1
        current_discount = 0.0
        self.update_total()
        return True
    def clear_product_search_entry(self):
        """Reset the product search box so the next lookup starts empty."""
        if not hasattr(self, "entry_product_search") or self.entry_product_search is None:
            return
        def _finalize_clear():
            try:
                self.entry_product_search.blockSignals(True)
                self.entry_product_search.setCurrentIndex(-1)
                self.entry_product_search.clearEditText()
                self.entry_product_search.setEditText("")
                self.entry_product_search.setCurrentText("")
                line_edit = self.entry_product_search.lineEdit()
                if line_edit:
                    line_edit.blockSignals(True)
                    line_edit.clear()
                    line_edit.setText("")
                    line_edit.blockSignals(False)
                    line_edit.setFocus(Qt.FocusReason.OtherFocusReason)
                if hasattr(self, "_completer_model"):
                    self._completer_model.setStringList(self._product_search_list)
            finally:
                self.entry_product_search.blockSignals(False)
            self.entry_product_search.hidePopup()
        _finalize_clear()
        QTimer.singleShot(0, _finalize_clear)
    def process_scanned_code(self, barcode_input):
        global current_item_count, current_discount
        barcode_input = (barcode_input or "").strip()
        if not barcode_input:
            return
        self.clear_product_search_entry()
        # Clear previous product info display
        self.clear_product_display()
        added = self.add_item_to_cart_by_sku(barcode_input)
        if not added:
            self.display_product_image(None, barcode_input)
    def keyPressEvent(self, event):
        if event is not None:
            modifiers = event.modifiers()
            if modifiers & (Qt.KeyboardModifier.ShiftModifier | Qt.KeyboardModifier.AltModifier):
                key = event.key()
                shortcut_map = {
                    Qt.Key.Key_1: 1,
                    Qt.Key.Key_2: 2,
                    Qt.Key.Key_3: 3,
                    Qt.Key.Key_4: 4,
                    Qt.Key.Key_5: 5,
                    Qt.Key.Key_6: 6,
                    Qt.Key.Key_7: 7,
                    Qt.Key.Key_8: 8,
                    Qt.Key.Key_9: 9,
                    Qt.Key.Key_Exclam: 1,
                    Qt.Key.Key_At: 2,
                    Qt.Key.Key_NumberSign: 3,
                    Qt.Key.Key_Dollar: 4,
                    Qt.Key.Key_Percent: 5,
                    Qt.Key.Key_AsciiCircum: 6,
                    Qt.Key.Key_Ampersand: 7,
                    Qt.Key.Key_Asterisk: 8,
                    Qt.Key.Key_ParenLeft: 9,
                }
                qty = shortcut_map.get(key)
                if qty:
                    self._apply_next_item_quantity(
                        qty,
                        status_message="Next item quantity set to {qty}",
                    )
                    event.accept()
                    return
        super().keyPressEvent(event)
    def update_total(self):
        total = 0
        for item in self.cart:
            qty = item.get('qty', 1)
            price = item['price']
            total += price * qty
        self.label_total.setText(f"Total: P{total:,.2f}")
    def select_payment_method_dialog(self):
        dialog = QDialog(self)
        dialog.setWindowTitle("Select Payment Method")
        dialog.setFixedSize(300, 200)
        v_layout = QVBoxLayout()
        dialog.setLayout(v_layout)
        self._track_modal_dialog(dialog, "_active_payment_dialog")
        lbl = QLabel("Select Payment Method:")
        lbl.setFont(QFont("Arial", 12, QFont.Weight.Bold))
        v_layout.addWidget(lbl, alignment=Qt.AlignmentFlag.AlignCenter)
        selected_method = {"method": None}
        def set_method(method):
            selected_method["method"] = method
            dialog.accept()
        btn_cash = QPushButton("Cash Only")
        btn_cash.setStyleSheet("background-color: #FFEB3B; color: black;")
        btn_cash.clicked.connect(lambda: set_method("cash only"))
        v_layout.addWidget(btn_cash)
        btn_gcash = QPushButton("GCash Only")
        btn_gcash.setStyleSheet("background-color: #1A8FE1; color: white;")
        btn_gcash.clicked.connect(lambda: set_method("gcash only"))
        v_layout.addWidget(btn_gcash)
        btn_both = QPushButton("Cash and GCash")
        btn_both.setStyleSheet("background-color: #4CAF50; color: white;")
        btn_both.clicked.connect(lambda: set_method("cash and gcash"))
        v_layout.addWidget(btn_both)
        dialog.exec()
        return selected_method["method"]

    def _build_transaction_reference(self, transaction_uuid):
        """
        Build a deterministic reference label for the current transaction using the POS prefix settings.
        """
        prefix = (api_settings or {}).get("order_reference_prefix") if api_settings else None
        return generate_reference_code(prefix or TRANSACTION_REFERENCE_PREFIX, seed=transaction_uuid)

    def generate_local_reference_label(self):
        """Return a human-friendly reference used when tagging local-only exports."""
        return generate_reference_code(LOCAL_EXPORT_REFERENCE_PREFIX)

    def _record_transaction_tracking(
        self,
        *,
        transaction_uuid,
        reference_label,
        sales_key,
        payment_method,
        ledger_lines,
        total_amount,
        cash_amount,
        gcash_amount,
    ):
        """
        Store metadata about the completed transaction so export/post/void flows can correlate line items.
        """
        if not transaction_uuid or not ledger_lines:
            return
        entry = {
            "transaction_uuid": transaction_uuid,
            "reference_label": reference_label,
            "sales_key": sales_key,
            "payment_method": payment_method,
            "total_amount": float(total_amount),
            "cash_amount": float(cash_amount or 0.0),
            "gcash_amount": float(gcash_amount or 0.0),
            "line_items": deepcopy(ledger_lines),
            "day_code": datetime.now().strftime("%Y%m%d"),
            "created_at": datetime.now().strftime(REFERENCE_TIMESTAMP_FORMAT),
        }
        register_transaction_ledger_entry(entry)

    def checkout(self):
        global current_sales_number, current_transaction_number, receipts_archive
        global total_cash_tendered, total_gcash_tendered
        global sales_summary_vault, total_cash_tendered_vault, total_gcash_tendered_vault
        simulation_mode = bool(getattr(self, "simulation_manager", None) and self.simulation_manager.is_active)
        simulation_checkout_token = None
        if simulation_mode and getattr(self, "simulation_manager", None):
            simulation_checkout_token = self.simulation_manager.get_active_checkout_token()
        if not self.cart:
            show_info("Info", "Cart is empty. Please add items before checking out.", self)
            self.log_user_action("Checkout cancelled", "Cart empty")
            return
        transaction_uuid = generate_transaction_uuid()
        transaction_reference = self._build_transaction_reference(transaction_uuid)
        ledger_line_entries = []
        ledger_sequence = 1
        api_catalog_skus = set()
        cache_entry = getattr(self, "_api_catalog_cache", None)
        if cache_entry and isinstance(cache_entry, dict):
            cached_skus = cache_entry.get("skus")
            if isinstance(cached_skus, (set, list, tuple)):
                api_catalog_skus = set(cached_skus)
        self.remove_existing_freebies_from_cart()
        self.applied_freebies = []
        self.applied_freebie_messages = []
        # Ensure sufficient stock is still available for all items (including bundles) before processing payment.
        for item in self.cart:
            qty = item.get('qty', 1)
            if item.get('bundle_components'):
                insufficient = []
                for component in item['bundle_components']:
                    barcode = component.get("barcode")
                    variant_index = component.get("variant_index", 0)
                    component_qty = component.get("quantity", 1)
                    required = qty * component_qty
                    variants = products.get(barcode, [])
                    if not variants:
                        insufficient.append((component.get("name", barcode), required, 0))
                        continue
                    if variant_index >= len(variants):
                        variant_index = 0
                    available = variants[variant_index].get("stock", 0)
                    if available < required:
                        name = variants[variant_index].get("name", barcode)
                        insufficient.append((name, required, available))
                if insufficient:
                    details = "\n".join(
                        f"- {name}: need {need}, available {avail}"
                        for name, need, avail in insufficient
                    )
                    show_error(
                        "Insufficient Stock",
                        f"Unable to complete checkout. Bundle '{item['name']}' lacks stock:\n{details}",
                        self
                    )
                    self.log_user_action("Checkout blocked", f"Bundle '{item['name']}' insufficient stock")
                    return
            else:
                base_barcode = item.get('base_stock_no') or item.get('Stock No.')
                variant_index = item.get('variant_index', 0)
                inventory_usage = item.get('inventory_usage', 1)
                required = qty * inventory_usage
                variants = products.get(base_barcode, [])
                if not variants:
                    show_error(
                        "Inventory Error",
                        f"Product '{base_barcode}' is missing from inventory. Please remove it from the cart.",
                        self
                    )
                    self.log_user_action("Checkout blocked", f"Inventory record missing for '{base_barcode}'")
                    return
                if variant_index >= len(variants):
                    variant_index = 0
                available = variants[variant_index].get("stock", 0)
                if available < required:
                    name = variants[variant_index].get("name", base_barcode)
                    show_error(
                        "Insufficient Stock",
                        f"Product '{name}' only has {available} pcs left, but {required} pcs are needed.",
                        self
                    )
                    self.log_user_action("Checkout blocked", f"Insufficient stock for '{name}' (need {required}, have {available})")
                    return
        # ... (Existing code for stock availability, total calculation, payment, etc.) ...
        total = 0
        for item in self.cart:
            qty = item.get('qty', 1)
            price = item['price']
            total += price * qty
        subtotal_for_promos = total
        payment_method = self.select_payment_method_dialog()
        if payment_method is None:
            self.log_user_action("Checkout cancelled", "Payment method dialog closed")
            return
        self.log_user_action("Selected payment method", payment_method.title())
        cash_amount = 0.0
        gcash_amount = 0.0
        total_paid = 0.0
        if payment_method == "cash only":
            cash_amount_input, ok = QInputDialog.getDouble(self, "Cash Payment", f"Total due: P{total:,.2f}\nEnter cash amount:", min=total)
            if not ok:
                self.log_user_action("Checkout cancelled", "Cash payment entry cancelled")
                return
            cash_amount = cash_amount_input
            total_paid = cash_amount
            if total_paid < total:
                show_error("Payment Error", "Insufficient cash payment. Please pay the full amount.", self)
                self.log_user_action("Checkout blocked", f"Insufficient cash tendered: P{total_paid:,.2f} of P{total:,.2f}")
                return
        elif payment_method == "gcash only":
            gcash_amount_input, ok = QInputDialog.getDouble(self, "GCash Payment", f"Total due: P{total:,.2f}\nEnter GCash amount:", min=total)
            if not ok:
                self.log_user_action("Checkout cancelled", "GCash payment entry cancelled")
                return
            gcash_amount = gcash_amount_input
            total_paid = gcash_amount
            if total_paid < total:
                show_error("Payment Error", "Insufficient GCash payment. Please pay the full amount.", self)
                self.log_user_action("Checkout blocked", f"Insufficient GCash tendered: P{total_paid:,.2f} of P{total:,.2f}")
                return
        elif payment_method == "cash and gcash":
            cash_amount_input, ok = QInputDialog.getDouble(self, "Cash Payment", f"Total due: P{total:,.2f}\nEnter cash amount (0 for no cash):", min=0)
            if not ok:
                self.log_user_action("Checkout cancelled", "Cash portion entry cancelled")
                return
            cash_amount = cash_amount_input
            gcash_amount_input, ok = QInputDialog.getDouble(self, "GCash Payment", f"Total due: P{total:,.2f}\nEnter GCash amount (0 for no GCash):", min=0)
            if not ok:
                self.log_user_action("Checkout cancelled", "GCash portion entry cancelled")
                return
            gcash_amount = gcash_amount_input
            total_paid = cash_amount + gcash_amount
            if total_paid < total:
                show_error("Payment Error", f"Insufficient combined payment. Total paid: P{total_paid:,.2f}\nRemaining due: P{total - total_paid:,.2f}", self)
                self.log_user_action("Checkout blocked", f"Combined tender short by P{total - total_paid:,.2f}")
                return
        change = total_paid - total
        if not simulation_mode:
            self.apply_basket_freebies_to_cart(subtotal_for_promos)
        # Find the highest existing sales number and transaction number in receipts_archive
        if not simulation_mode:
            highest_sales_number = 0
            highest_transaction_number = 0
            for key in receipts_archive.keys():
                sales_match = re.search(r"SALES#: (\d+)", key)  # Extract the sales number using regex
                trans_match = re.search(r"TRANS#: (\d+)", key)  # Extract the transaction number using regex
                if sales_match:
                    try:
                        sales_number = int(sales_match.group(1))
                        highest_sales_number = max(highest_sales_number, sales_number)
                    except ValueError:
                        pass  # Ignore keys that don't have a valid sales number
                if trans_match:
                    try:
                        transaction_number = int(trans_match.group(1))
                        highest_transaction_number = max(highest_transaction_number, transaction_number)
                    except ValueError:
                        pass  # Ignore keys that don't have a valid transaction number
            db_sales_highest, db_transaction_highest = fetch_highest_sales_identifiers(self)
            highest_sales_number = max(highest_sales_number, db_sales_highest)
            highest_transaction_number = max(highest_transaction_number, db_transaction_highest)
            next_sales_number = highest_sales_number + 1
            next_transaction_number = highest_transaction_number + 1
            current_date = datetime.now().strftime("%Y-%m-%d")
            current_time = datetime.now().strftime("%H:%M:%S")
            sales_trans_label = f"SALES#: {next_sales_number:06d}   TRANS#: {next_transaction_number:06d}"
            sales_trans_line = f"{sales_trans_label}"
        else:
            current_date = datetime.now().strftime("%Y-%m-%d")
            current_time = datetime.now().strftime("%H:%M:%S")
            customer_number = (
                (self.simulation_manager.current_index + 1) if self.simulation_manager.current_index >= 0 else 1
            )
            sales_trans_label = f"SIM CUSTOMER {customer_number:02d} {current_time}"
            sales_trans_line = sales_trans_label
        # Generate receipt text content based on printable layout
        layout_info = compute_receipt_layout()
        width = int(layout_info["total_width"])
        price_col_width = int(layout_info["price_width"])
        left_col_width = int(layout_info["left_width"])
        receipt_text_content = ""
        def wrap_left(text, target_width=None):
            cleaned = (text or "").replace("\n", " ")
            width_limit = target_width if target_width is not None else left_col_width
            if width_limit <= 0:
                return [cleaned]
            if not cleaned:
                return [" " * width_limit]
            segments = [
                cleaned[i:i + width_limit]
                for i in range(0, len(cleaned), width_limit)
            ]
            return [segment.ljust(width_limit) for segment in segments]
        def format_right(text):
            if price_col_width <= 0:
                return ""
            right_text = (text or "").strip()
            if len(right_text) > price_col_width:
                right_text = right_text[-price_col_width:]
            return right_text.rjust(price_col_width)
        def append_columns(left_text, right_text=None):
            nonlocal receipt_text_content
            if left_col_width > 0:
                wrap_width = left_col_width if right_text is not None else max(left_col_width, width)
                left_lines = wrap_left(left_text, wrap_width)
            else:
                cleaned = (left_text or "").replace("\n", " ")
                if not cleaned:
                    left_lines = [""]
                else:
                    step = max(width, 1)
                    left_lines = [
                        cleaned[i:i + step] for i in range(0, len(cleaned), step)
                    ] or [""]
            if right_text is not None:
                if left_col_width > 0:
                    right_formatted = format_right(right_text)
                    receipt_text_content += f"{left_lines[0]}{right_formatted}\n"
                    for extra in left_lines[1:]:
                        receipt_text_content += f"{extra}\n"
                else:
                    right_formatted = format_right(right_text)
                    receipt_text_content += f"{right_formatted.rjust(width)}\n"
                    for segment in left_lines:
                        if segment:
                            receipt_text_content += f"{segment[:width]}\n"
            else:
                for segment in left_lines:
                    receipt_text_content += f"{segment[:width]}\n"
        booth_header_text = "Booth #: A003"
        receipt_text_content += f"{booth_header_text:^{width}}\n"
        receipt_text_content += f"{'SUNNYWARE PHILIPPINES':^{width}}\n"
        receipt_text_content += f"{'Metro Manila, Philippines':^{width}}\n"
        receipt_text_content += f"{'---SALES ORDER SLIP---':^{width}}\n"
        receipt_text_content += f"{sales_trans_line:^{width}}\n"
        if not simulation_mode:
            receipt_text_content += f"{('REF: ' + transaction_reference):^{width}}\n"
        receipt_text_content += "\n"
        for item in self.cart:
            raw_name = sanitize_product_name(item.get('name'))
            fallback_label = item.get('Stock No.') or item.get('base_stock_no') or ""
            name = raw_name or str(fallback_label).strip() or "Item"
            qty = item.get('qty', 1)
            price = item['price']
            line_total_val = price * qty
            line_total = f"P{line_total_val:,.2f}"
            unit_price = f"P{price:,.2f}"
            promo_suffix = item.get('promo_code')
            identifier = render_product_identifier(item.get("code"), item.get("Stock No."))
            label_prefix = f"{identifier} " if identifier else ""
            full_name = f"{label_prefix}{name}".strip().replace("\n", " ") or (identifier or name)
            append_columns(full_name)
            if promo_suffix:
                label = promo_suffix if qty == 1 else f"{qty} x {promo_suffix}"
                append_columns(f"{label} @ {unit_price}", line_total)
            else:
                append_columns(f"{qty} @ {unit_price}", line_total)
            if item.get('bundle_components'):
                for component in item['bundle_components']:
                    component_name = sanitize_product_name(component.get("name"), component.get("barcode"))
                    component_qty = component.get("quantity", 1)
                    append_columns(f"  - {component_qty} x {component_name}")
            receipt_text_content += "\n"
        receipt_text_content += "-" * width + "\n"
        append_columns("Total Amount Due:", f"P{total:,.2f}")
        if payment_method == "cash and gcash":
            append_columns("Cash:", f"P{cash_amount:,.2f}")
            append_columns("GCash:", f"P{gcash_amount:,.2f}")
            if not simulation_mode:
                total_gcash_tendered += gcash_amount
                total_cash_tendered += cash_amount
                total_cash_tendered_vault += cash_amount
                total_gcash_tendered_vault += gcash_amount
        elif payment_method == "cash only":
            append_columns("Cash:", f"P{cash_amount:,.2f}")
            if not simulation_mode:
                total_cash_tendered += cash_amount
                total_cash_tendered_vault += cash_amount
        elif payment_method == "gcash only":
            append_columns("GCash:", f"P{gcash_amount:,.2f}")
            if not simulation_mode:
                total_gcash_tendered += gcash_amount
                total_gcash_tendered_vault += gcash_amount
        append_columns("Change:", f"P{change:,.2f}")
        append_columns(f"Payment Method: {payment_method.title()}")
        receipt_text_content += "-" * width + "\n"
        timestamp_line = f"{current_date} {current_time}"
        receipt_text_content += f"{timestamp_line:^{width}}\n"
        receipt_text_content += f"{'Cashier: ' + self.current_user_name:^{width}}\n"
        receipt_text_content += f"{'SUNNYWARE PHILIPPINES':^{width}}\n"
        freebie_messages = [msg for msg in self.applied_freebie_messages if msg]
        closing_messages = freebie_messages if freebie_messages else ["THANK YOU SO MUCH!"]
        for message in closing_messages:
            wrapped_lines = textwrap.wrap(message, width) or [""]
            for line in wrapped_lines:
                receipt_text_content += f"{line:^{width}}\n"
        if not simulation_mode:
            receipts_archive[sales_trans_label] = receipt_text_content
        receipt_dialog = ReceiptDialog(receipt_text_content, self)
        self._track_modal_dialog(receipt_dialog, "_active_receipt_dialog")
        if simulation_mode:
            receipt_dialog.setWindowTitle("Simulation Receipt")
        receipt_dialog.exec()
        # Update stock & sales summary after transaction
        sale_items_records = []
        if not simulation_mode:
            for item in self.cart:
                is_freebie = bool(item.get("is_freebie"))
                if item.get('bundle_components'):
                    bundle_qty = item.get('qty', 1)
                    component_infos = []
                    total_base_value = 0.0
                    for component in item['bundle_components']:
                        barcode = component.get("barcode")
                        variant_index = component.get("variant_index", 0)
                        quantity_per_bundle = component.get("quantity", 1)
                        deduction_units = bundle_qty * quantity_per_bundle
                        variants = products.get(barcode, [])
                        if not variants:
                            print(f"Warning: bundle component '{barcode}' missing during inventory update.")
                            continue
                        if variant_index >= len(variants):
                            variant_index = 0
                        variant = variants[variant_index]
                        variant["stock"] -= deduction_units
                        base_price = float(variant.get("price", 0))
                        base_value = base_price * quantity_per_bundle
                        total_base_value += base_value
                        component_infos.append({
                            "barcode": barcode,
                            "product_id": variant.get("_product_id"),
                            "deduction_units": deduction_units,
                            "base_value": base_value
                        })
                    for info in component_infos:
                        barcode = info["barcode"]
                        product_id = info["product_id"]
                        quantity = info["deduction_units"]
                        if not is_freebie:
                            if barcode not in sales_summary:
                                sales_summary[barcode] = {"qty_sold": 0, "revenue": 0.0}
                            if barcode not in sales_summary_vault:
                                sales_summary_vault[barcode] = {"qty_sold": 0, "revenue": 0.0}
                            sales_summary[barcode]["qty_sold"] += quantity
                            sales_summary_vault[barcode]["qty_sold"] += quantity
                        if total_base_value > 0:
                            share = info["base_value"] / total_base_value
                        else:
                            share = 1 / len(component_infos) if component_infos else 0
                        component_total = 0.0 if is_freebie else item['price'] * bundle_qty * share
                        if not is_freebie:
                            sales_summary[barcode]["revenue"] += component_total
                            sales_summary_vault[barcode]["revenue"] += component_total
                        price_per_unit = (component_total / quantity) if quantity and component_total else 0.0
                        if product_id:
                            sale_items_records.append({
                                "product_id": product_id,
                                "quantity": int(quantity),
                                "price_per_unit": price_per_unit,
                                "total_price": component_total,
                                "is_freebie": is_freebie,
                            })
                        ledger_line_entries.append(
                            {
                                "line_id": f"{transaction_uuid[:8]}-{ledger_sequence:03d}",
                                "sku": barcode,
                                "name": component.get("name") or barcode,
                                "quantity": int(quantity),
                                "unit_price": price_per_unit,
                                "line_total": component_total,
                                "is_freebie": is_freebie,
                                "bundle_parent": item.get("name"),
                                "status": "pending",
                                "api_candidate": barcode in api_catalog_skus,
                            }
                        )
                        ledger_sequence += 1
                    continue
                sku = item.get('Stock No.')
                base_barcode = item.get('base_stock_no', sku)
                qty = item.get('qty', 1)
                inventory_usage = item.get('inventory_usage', 1)
                variant_index = item.get('variant_index', 0)
                deduction_units = qty * inventory_usage
                variants = products.get(base_barcode, [])
                if not variants:
                    print(f"Warning: Unable to update inventory. Base product '{base_barcode}' not found.")
                    continue
                if variant_index >= len(variants):
                    variant_index = 0
                variant = variants[variant_index]
                variant["stock"] -= deduction_units
                if isinstance(deduction_units, float) and deduction_units.is_integer():
                    deduction_units = int(deduction_units)
                product_id = variant.get("_product_id")
                line_total_amount = 0.0 if is_freebie else item['price'] * qty
                if not is_freebie:
                    if base_barcode not in sales_summary:
                        sales_summary[base_barcode] = {"qty_sold": 0, "revenue": 0.0}
                    if base_barcode not in sales_summary_vault:
                        sales_summary_vault[base_barcode] = {"qty_sold": 0, "revenue": 0.0}
                    sales_summary[base_barcode]["qty_sold"] += deduction_units
                    sales_summary[base_barcode]["revenue"] += line_total_amount
                    sales_summary_vault[base_barcode]["qty_sold"] += deduction_units
                    sales_summary_vault[base_barcode]["revenue"] += line_total_amount
                price_per_unit = (line_total_amount / deduction_units) if deduction_units and line_total_amount else 0.0
                if product_id:
                    sale_items_records.append({
                        "product_id": product_id,
                        "quantity": int(deduction_units),
                        "price_per_unit": price_per_unit,
                        "total_price": line_total_amount,
                        "is_freebie": is_freebie,
                    })
                ledger_line_entries.append(
                    {
                        "line_id": f"{transaction_uuid[:8]}-{ledger_sequence:03d}",
                        "sku": base_barcode,
                        "name": item.get("name") or base_barcode,
                        "quantity": int(deduction_units),
                        "unit_price": price_per_unit,
                        "line_total": line_total_amount,
                        "is_freebie": is_freebie,
                        "status": "pending",
                        "api_candidate": base_barcode in api_catalog_skus,
                    }
                )
                ledger_sequence += 1
            self.persist_checkout_to_database(
                next_sales_number,
                sales_trans_label,
                receipt_text_content,
                total,
                total_paid,
                change,
                payment_method,
                sale_items_records,
                transaction_uuid=transaction_uuid,
            )
            save_products_to_database(self)
            current_sales_number = next_sales_number
            current_transaction_number = next_transaction_number
            save_sales_summary()
            save_receipts_archive()
            save_sales_vault()
            save_inventory_summary()
            self._record_transaction_tracking(
                transaction_uuid=transaction_uuid,
                reference_label=transaction_reference,
                sales_key=sales_trans_label,
                payment_method=payment_method,
                ledger_lines=ledger_line_entries,
                total_amount=total,
                cash_amount=cash_amount,
                gcash_amount=gcash_amount,
            )
        cart_snapshot = [deepcopy(entry) for entry in self.cart]
        tender_segments = []
        if cash_amount > 0:
            tender_segments.append(f"Cash P{cash_amount:,.2f}")
        if gcash_amount > 0:
            tender_segments.append(f"GCash P{gcash_amount:,.2f}")
        tender_detail = ", ".join(tender_segments) if tender_segments else payment_method.title()
        item_descriptions = []
        for entry in self.cart:
            label = entry.get("name") or entry.get("Stock No.") or "Item"
            qty = entry.get("qty", 1)
            if entry.get("is_freebie"):
                label = f"{label} (FREE)"
            item_descriptions.append(f"{label} x{qty}")
        if len(item_descriptions) > 10:
            visible = item_descriptions[:10]
            remaining = len(item_descriptions) - 10
            visible.append(f"... +{remaining} more")
        else:
            visible = item_descriptions
        cart_summary = "; ".join(visible) if visible else "No items recorded"
        action_label = "Completed checkout (Simulation)" if simulation_mode else "Completed checkout"
        self.log_user_action(
            action_label,
            f"Ref {transaction_reference} | Total P{total:,.2f}, Paid P{total_paid:,.2f}, Change P{change:,.2f}, Tender: {tender_detail}. Items: {cart_summary}",
        )
        # Clear cart and UI
        self.cart.clear()
        self.listbox.clear()
        self.update_total()
        self.clear_product_display()
        self.handle_session_after_checkout()
        if getattr(self, "simulation_manager", None):
            self.simulation_manager.handle_checkout_completion(
                cart_snapshot,
                total,
                total_paid,
                change,
                payment_method,
                receipt_text_content,
                cash_amount,
                gcash_amount,
                checkout_token=simulation_checkout_token,
            )
    def persist_checkout_to_database(
        self,
        next_sales_number,
        sales_key,
        receipt_text,
        total_amount,
        amount_tendered,
        change_due,
        payment_method,
        sale_items_records,
        transaction_uuid=None,
    ):
        """
        Persist the completed sale, its line items, and receipt text to the MySQL database.
        """
        conn = get_db_connection(self)
        if not conn:
            return
        try:
            ensure_sales_reference_columns(conn)
            with conn.cursor(dictionary=True) as cursor:
                cursor.execute(
                    "SELECT user_id FROM users WHERE username = %s",
                    (self.current_user_name,),
                )
                user_row = cursor.fetchone()
            if not user_row:
                show_error(
                    "Database Error",
                    "Unable to record sale because the current cashier could not be found in the database.",
                    self,
                )
                return
            cashier_id = user_row["user_id"]
            with conn.cursor() as cursor:
                sales_no_value = f"{int(next_sales_number):06d}"
                cursor.execute(
                    """
                    INSERT INTO sales_transactions
                        (sales_no, transaction_uuid, transaction_time, cashier_id, total_amount, payment_method, amount_tendered, change_given)
                    VALUES
                        (%s, %s, NOW(), %s, %s, %s, %s, %s)
                    """,
                    (
                        sales_no_value,
                        transaction_uuid,
                        cashier_id,
                        float(total_amount),
                        payment_method,
                        float(amount_tendered),
                        float(change_due),
                    ),
                )
                transaction_id = cursor.lastrowid
                clean_items = [
                    (
                        transaction_id,
                        int(item["product_id"]),
                        int(item["quantity"]),
                        float(item["price_per_unit"]),
                        float(item["total_price"]),
                        bool(item["is_freebie"]),
                    )
                    for item in sale_items_records
                    if item.get("product_id") is not None
                ]
                if clean_items:
                    cursor.executemany(
                        """
                        INSERT INTO sales_items
                            (transaction_id, product_id, quantity, price_per_unit, total_price, is_freebie)
                        VALUES
                            (%s, %s, %s, %s, %s, %s)
                        """,
                        clean_items,
                    )
                cursor.execute(
                    """
                    INSERT INTO receipts (transaction_id, sales_key, receipt_text)
                    VALUES (%s, %s, %s)
                    ON DUPLICATE KEY UPDATE
                        receipt_text = VALUES(receipt_text),
                        transaction_id = VALUES(transaction_id)
                    """,
                    (transaction_id, sales_key, receipt_text),
                )
            conn.commit()
        except Error as exc:
            try:
                conn.rollback()
            except Exception:
                pass
            print(f"Error persisting checkout: {exc}")
            show_error("Database Error", f"Unable to save sale to the database:\n{exc}", self)
        finally:
            try:
                conn.close()
            except Exception:
                pass
    def set_discount(self):
        disc, ok = QInputDialog.getDouble(self, "Apply Discount", "Enter discount percentage (0-100):", min=0, max=100)
        if ok:
            global current_discount
            current_discount = disc
            show_info("Discount Set", f"Discount for next item set to {current_discount:.2f}%", self)
            self.log_user_action("Set next item discount", f"{current_discount:.2f}%")
    def set_item_count(self):
        count, ok = QInputDialog.getInt(self, "Set Item Quantity", "Enter item quantity (1 or more):", min=1)
        if ok:
            self._apply_next_item_quantity(
                count,
                log_message="Set next item quantity",
            )
    def inventory_management(self):
        dlg = InventoryManagementDialog(products, self)  # Pass the global products dictionary
        dlg.exec()
        # Refresh product search and product display after stock changes
        self.clear_product_display()
        rebuild_product_variant_lookup()
        self.refresh_product_search_options()
        save_inventory_summary()
        save_products_to_database(self)
        self.log_user_action("Accessed inventory management")
    def clear_sales_summary_with_reference(
        self,
        ref_no,
        parent_widget=None,
        show_feedback=True,
        target_skus=None,
        clear_reason="manual",
        auto_generated=False,
    ):
        """
        Tags unposted sales with ref_no, clears local summary totals (fully or partially), and persists the reset.
        Returns a dictionary with counts on success, or None on failure.
        """
        global sales_summary, total_cash_tendered, total_gcash_tendered
        widget = parent_widget or self
        ref_no = (ref_no or "").strip()
        if not ref_no:
            show_error("Missing Reference", "A valid SI / reference number is required.", widget)
            return None
        normalized_targets = None
        if target_skus:
            seen = []
            for value in target_skus:
                if value is None:
                    continue
                text = str(value).strip()
                if text and text not in seen:
                    seen.append(text)
            normalized_targets = seen or None
        prior_sku_count = len(sales_summary)
        removed_revenue = 0.0
        if normalized_targets is None:
            for entry in sales_summary.values():
                removed_revenue += float((entry or {}).get("revenue") or 0.0)
        else:
            for sku in normalized_targets:
                snapshot = sales_summary.get(sku) or {}
                removed_revenue += float(snapshot.get("revenue") or 0.0)
        success, counts = assign_reference_to_sales(ref_no, widget, stock_numbers=normalized_targets)
        if not success:
            return None
        transactions_tagged, items_tagged = counts
        tag_transaction_lines_with_reference(ref_no, normalized_targets, clear_reason)
        if normalized_targets is None:
            cleared_sku_count = prior_sku_count
            sales_summary.clear()
            total_cash_tendered = 0.0
            total_gcash_tendered = 0.0
            save_tendered_amounts()
        else:
            cleared_sku_count = len(normalized_targets)
            for sku in normalized_targets:
                sales_summary.pop(sku, None)
            self._deduct_tender_totals_for_revenue(removed_revenue)
        save_sales_summary()
        self.sales_summary = sales_summary
        action_label = "Cleared sales summary" if normalized_targets is None else "Partially cleared sales summary"
        if clear_reason and clear_reason != "manual":
            action_label = f"{action_label} ({clear_reason.replace('_', ' ').title()})"
        self.log_user_action(
            action_label,
            f"Reference {ref_no} | Transactions tagged: {transactions_tagged} | Items tagged: {items_tagged} | SKUs removed: {cleared_sku_count}",
        )
        if show_feedback:
            if normalized_targets is None:
                message_title = "Sales Summary Cleared"
                message_lines = [
                    "Sales summary cleared.",
                    f"Tagged {transactions_tagged} transaction(s) and {items_tagged} item(s) with reference '{ref_no}'.",
                ]
            else:
                message_title = "Sales Summary Updated"
                message_lines = [
                    "Tagged matching items with the provided reference.",
                    f"Removed {cleared_sku_count} SKU(s) from the dashboard. Remaining items stay pending for manual export.",
                ]
                if removed_revenue > 0:
                    message_lines.append(
                        f"Adjusted tender totals by P{removed_revenue:,.2f} to keep metrics accurate."
                    )
            if auto_generated:
                message_lines.append("Reference generated automatically for tagging.")
            show_info(message_title, "\n".join(message_lines), widget)
        return {"transactions": transactions_tagged, "items": items_tagged, "skus": cleared_sku_count}
    def post_sales_invoice(self, parent_widget=None):
        """
        Posts the current sales summary as an invoice via the configured API and clears the summary on success.
        """
        global sales_summary
        widget = parent_widget or self
        if not ensure_api_settings_loaded(widget):
            return False
        api_skus = self.get_api_catalog_skus(parent_widget=widget)
        if api_skus is None:
            return False
        if not sales_summary:
            show_info("Sales Invoice", "No sales data available to post.", widget)
            return False
        items = []
        posted_skus = []
        skipped_items = []
        include_unit_price = api_settings.get("include_unit_price")
        for sku, data in sales_summary.items():
            qty = int(data.get("qty_sold") or 0)
            if qty <= 0:
                continue
            sku_text = str(sku).strip()
            if not sku_text:
                continue
            revenue = float(data.get("revenue") or 0.0)
            unit_price = revenue / qty if qty and include_unit_price else None
            variant_name = sku
            variants = self.products.get(sku)
            if variants:
                variant_name = variants[0].get("name", sku)
            if sku_text not in api_skus:
                skipped_items.append(
                    {
                        "sku": sku_text,
                        "name": variant_name,
                        "quantity": qty,
                    }
                )
                continue
            items.append(
                {
                    "sku": sku_text,
                    "quantity": qty,
                    "unitPrice": round(unit_price, 2) if unit_price is not None else None,
                    "remarks": variant_name,
                }
            )
            posted_skus.append(sku_text)
        if not items:
            show_info(
                "Sales Invoice",
                "No qualifying sales items matched the API catalog. Use 'Export Local Items' to process the remaining entries.",
                widget,
            )
            return False
        today_str = datetime.now().strftime("%Y-%m-%d")
        prefix = api_settings.get("order_reference_prefix") or "POS"
        order_reference = f"{prefix}-{today_str}"
        notes_value = api_settings.get("default_notes")
        payload = {
            "customerId": api_settings["customer_id"],
            "reference": api_settings.get("default_reference"),
            "transactionDate": today_str,
            "warehouseId": api_settings["warehouse_id"],
            "orderReference": order_reference,
            "notes": notes_value if notes_value is not None else "",
            "items": items,
        }
        using_stub = api_settings.get("use_sales_stub")
        body = None
        if using_stub:
            body = load_sales_invoice_stub_response(parent=widget)
            if body is None:
                show_error("Sales Invoice Error", "Sales stub response could not be loaded.", widget)
                return False
        else:
            response = api_request("POST", "sales-invoices", parent=widget, json_payload=payload)
            if response is None:
                return False
            if response.status_code not in (200, 201):
                try:
                    error_body = response.json()
                except ValueError:
                    error_body = response.text
                show_error("Sales Invoice Error", f"API returned {response.status_code}:\n{error_body}", widget)
                return False
            try:
                body = response.json()
            except ValueError:
                body = {}
            if not isinstance(body, dict):
                body = {}
            if body.get("code") not in (200, 201):
                message = body.get("message") or body.get("error") or response.text
                show_error("Sales Invoice Error", f"API responded with code {body.get('code')}:\n{message}", widget)
                return False
        if not isinstance(body, dict):
            body = {}
        data = body.get("data") or {}
        if isinstance(data, dict):
            order_number = payload.get("orderReference")
            txn_date = payload.get("transactionDate")
            warehouse_id = payload.get("warehouseId")
            if order_number and not data.get("order_no"):
                data["order_no"] = order_number
            if txn_date and not data.get("txn_date"):
                data["txn_date"] = txn_date
            if warehouse_id and not data.get("warehouse_id"):
                data["warehouse_id"] = str(warehouse_id)
        ref_no = data.get("ref_no") or data.get("order_no") or data.get("id") or payload.get("orderReference")
        amount_due = data.get("amount_due")
        summary_stats = self.clear_sales_summary_with_reference(
            ref_no,
            parent_widget=widget,
            show_feedback=False,
            target_skus=posted_skus,
            clear_reason="api_post",
        )
        message_lines = ["Sales invoice created successfully."]
        if ref_no:
            message_lines.append(f"Reference: {ref_no}")
        if amount_due is not None:
            message_lines.append(f"Amount Due: {amount_due}")
        if summary_stats:
            message_lines.append(
                f"Tagged {summary_stats['transactions']} transaction(s) and {summary_stats['items']} item(s) before clearing the summary."
            )
            cleared_skus = summary_stats.get("skus")
            if cleared_skus is not None:
                message_lines.append(f"Removed {cleared_skus} SKU(s) from the dashboard.")
        else:
            message_lines.append("Sales summary was not cleared automatically. Please clear it manually.")
        if skipped_items:
            message_lines.append(
                f"Skipped {len(skipped_items)} local item(s) not found on the API. Export them via 'Export Local Items'."
            )
        show_info("Sales Invoice Posted", "\n".join(message_lines), widget)
        if using_stub:
            show_info(
                "Stub Data Used",
                "Sales invoice request used stub response. Disable 'use_sales_stub' in api_settings.json to call the live API.",
                widget,
            )
        self.log_user_action(
            "Posted sales invoice",
            f"Reference {ref_no or 'N/A'} | Items sent: {len(items)} | Skipped: {len(skipped_items)}",
        )
        return True
    def summary_view(self):
        dlg = SalesSummaryDialog(self)
        dlg.exec()
        self.log_user_action("Viewed sales summary")
    def show_activity_logs(self):
        password, ok = QInputDialog.getText(
            self,
            "Admin Authorization Required",
            "Enter admin password to open activity logs:",
            QLineEdit.EchoMode.Password,
        )
        if not ok:
            return
        if password != ADMIN_PASSWORD:
            show_error("Authorization Failed", "Invalid admin password.", self)
            return
        self.log_user_action("Viewed activity logs")
        logs = load_activity_logs()
        self.activity_logs = logs
        dialog = QDialog(self)
        dialog.setWindowTitle("Activity Logs")
        dialog.resize(940, 520)
        layout = QVBoxLayout(dialog)
        header_label = QLabel(f"Recorded events: {len(logs)}")
        header_label.setAlignment(Qt.AlignmentFlag.AlignLeft)
        layout.addWidget(header_label)
        table = QTableWidget(dialog)
        table.setColumnCount(4)
        table.setHorizontalHeaderLabels(["Timestamp", "User", "Action", "Details"])
        table.setRowCount(len(logs))
        table.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers)
        table.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        table.setSelectionMode(QAbstractItemView.SelectionMode.SingleSelection)
        header_view = table.horizontalHeader()
        header_view.setSectionResizeMode(0, QHeaderView.ResizeMode.ResizeToContents)
        header_view.setSectionResizeMode(1, QHeaderView.ResizeMode.ResizeToContents)
        header_view.setSectionResizeMode(2, QHeaderView.ResizeMode.ResizeToContents)
        header_view.setSectionResizeMode(3, QHeaderView.ResizeMode.Stretch)
        for row, entry in enumerate(logs):
            timestamp_item = QTableWidgetItem(str(entry.get("timestamp", "")))
            user_item = QTableWidgetItem(str(entry.get("user", "")))
            action_item = QTableWidgetItem(str(entry.get("action", "")))
            details_item = QTableWidgetItem(str(entry.get("details", "")))
            table.setItem(row, 0, timestamp_item)
            table.setItem(row, 1, user_item)
            table.setItem(row, 2, action_item)
            table.setItem(row, 3, details_item)
        table.verticalHeader().setVisible(False)
        layout.addWidget(table)
        close_box = QDialogButtonBox(QDialogButtonBox.StandardButton.Close)
        close_box.rejected.connect(dialog.reject)
        layout.addWidget(close_box)
        if logs:
            table.scrollToBottom()
        dialog.exec()
    def show_sales_summary_archive(self):
        dlg = SalesSummaryArchiveDialog(self)
        dlg.exec()
    def show_archive_labels(self):
        dlg = ArchiveDialog(self)
        dlg.exec()

    def void_archived_receipt(self, receipt_key, parent_widget=None):
        """
        Reverse an already-posted receipt by restoring stock, removing DB records, and updating metrics.
        """
        global receipts_archive, sales_summary, sales_summary_vault
        global total_cash_tendered, total_gcash_tendered
        global total_cash_tendered_vault, total_gcash_tendered_vault
        widget = parent_widget or self
        receipt_key = (receipt_key or "").strip()
        if not receipt_key:
            show_warning("Void Receipt", "Please select a receipt to void.", widget)
            return False
        receipt_text = receipts_archive.get(receipt_key)
        if not receipt_text:
            show_error("Void Receipt", "Receipt content was not found in the archive.", widget)
            return False
        conn = get_db_connection(self)
        if not conn:
            show_error("Database Error", "Unable to connect to the database to void the receipt.", widget)
            return False
        transaction_row = None
        sale_items = []
        transaction_id = None
        transaction_uuid = None
        try:
            with conn.cursor(dictionary=True) as cursor:
                cursor.execute(
                    """
                    SELECT r.transaction_id,
                           st.sales_no,
                           st.total_amount,
                           st.amount_tendered,
                           st.change_given,
                           st.payment_method,
                           st.transaction_uuid,
                           st.transaction_time
                      FROM receipts r
                      JOIN sales_transactions st ON r.transaction_id = st.transaction_id
                     WHERE r.sales_key = %s
                    """,
                    (receipt_key,),
                )
                transaction_row = cursor.fetchone()
                if not transaction_row:
                    show_error(
                        "Void Receipt",
                        "The receipt is missing its transaction record. Nothing was voided.",
                        widget,
                    )
                    return False
                transaction_id = transaction_row["transaction_id"]
                transaction_uuid = transaction_row.get("transaction_uuid")
                cursor.execute(
                    """
                    SELECT product_id, quantity, price_per_unit, total_price, is_freebie
                      FROM sales_items
                     WHERE transaction_id = %s
                    """,
                    (transaction_id,),
                )
                sale_items = cursor.fetchall() or []
            with conn.cursor() as cursor:
                cursor.execute("DELETE FROM sales_items WHERE transaction_id = %s", (transaction_id,))
                cursor.execute("DELETE FROM receipts WHERE sales_key = %s", (receipt_key,))
                cursor.execute("DELETE FROM sales_transactions WHERE transaction_id = %s", (transaction_id,))
            conn.commit()
        except Error as exc:
            try:
                conn.rollback()
            except Exception:
                pass
            show_error("Database Error", f"Failed to void the receipt:\n{exc}", widget)
            return False
        finally:
            try:
                conn.close()
            except Exception:
                pass
        # Restore inventory and local summaries
        restored_units = 0
        missing_products = []
        total_revenue_removed = 0.0
        for item in sale_items:
            product_id = item.get("product_id")
            qty = int(item.get("quantity") or 0)
            total_price = float(item.get("total_price") or 0.0)
            is_freebie = bool(item.get("is_freebie"))
            if qty <= 0:
                continue
            barcode, variant, _ = locate_variant_by_product_id(product_id)
            if not variant:
                missing_products.append(str(product_id))
                continue
            new_stock = float(variant.get("stock", 0)) + qty
            if isinstance(new_stock, float) and new_stock.is_integer():
                new_stock = int(new_stock)
            variant["stock"] = new_stock
            restored_units += qty
            if not is_freebie:
                summary_entry = sales_summary.setdefault(barcode, {"qty_sold": 0, "revenue": 0.0})
                summary_entry["qty_sold"] = max(0, int(summary_entry.get("qty_sold", 0)) - qty)
                summary_entry["revenue"] = max(0.0, float(summary_entry.get("revenue", 0.0)) - total_price)
                vault_entry = sales_summary_vault.setdefault(barcode, {"qty_sold": 0, "revenue": 0.0})
                vault_entry["qty_sold"] = max(0, int(vault_entry.get("qty_sold", 0)) - qty)
                vault_entry["revenue"] = max(0.0, float(vault_entry.get("revenue", 0.0)) - total_price)
                total_revenue_removed += total_price
            if barcode in inventory_summary:
                inv_entry = inventory_summary[barcode]
                inv_entry["stock"] = int(inv_entry.get("stock", 0)) + qty
                if not is_freebie:
                    inv_entry["qty_sold"] = max(0, int(inv_entry.get("qty_sold", 0)) - qty)
                    inv_entry["revenue"] = max(0.0, float(inv_entry.get("revenue", 0.0)) - total_price)
        # Update tender totals using receipt content
        payment_details = parse_receipt_payment_breakdown(receipt_text)
        cash_removed = float(payment_details.get("cash") or 0.0)
        gcash_removed = float(payment_details.get("gcash") or 0.0)
        payment_label = payment_details.get("payment_method") or transaction_row.get("payment_method", "")
        if payment_label:
            payment_label = payment_label.strip()
        if cash_removed == 0 and gcash_removed == 0:
            fallback_method = (transaction_row.get("payment_method") or "").strip().lower()
            tendered_total = float(transaction_row.get("amount_tendered") or 0.0)
            if fallback_method == "cash only":
                cash_removed = tendered_total
            elif fallback_method == "gcash only":
                gcash_removed = tendered_total
        if cash_removed > 0:
            total_cash_tendered = max(0.0, float(total_cash_tendered) - cash_removed)
            total_cash_tendered_vault = max(0.0, float(total_cash_tendered_vault) - cash_removed)
        if gcash_removed > 0:
            total_gcash_tendered = max(0.0, float(total_gcash_tendered) - gcash_removed)
            total_gcash_tendered_vault = max(0.0, float(total_gcash_tendered_vault) - gcash_removed)
        receipts_archive.pop(receipt_key, None)
        save_receipts_archive()
        if transaction_uuid:
            mark_transaction_voided(transaction_uuid)
        save_sales_vault()
        save_products_to_database(self)
        save_inventory_summary()
        save_tendered_amounts()
        summary_lines = [
            f"Receipt '{receipt_key}' voided.",
            f"Units restored: {restored_units}",
        ]
        if cash_removed > 0 or gcash_removed > 0:
            summary_lines.append(
                f"Tender reversed - Cash: P{cash_removed:,.2f}, GCash: P{gcash_removed:,.2f}"
            )
        if total_revenue_removed > 0:
            summary_lines.append(f"Sales removed: P{total_revenue_removed:,.2f}")
        if missing_products:
            summary_lines.append(
                f"Warning: {len(missing_products)} product(s) were missing locally and could not be restocked."
            )
        self.log_user_action(
            "Voided archived receipt",
            f"{receipt_key} | Units restored: {restored_units} | Cash -P{cash_removed:,.2f} | "
            f"GCash -P{gcash_removed:,.2f}",
        )
        show_info("Receipt Voided", "\n".join(summary_lines), widget)
        return True
class SalesSummaryDialog(QDialog):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setWindowTitle("Sales Summary")
        self.resize(1400, 680)
        self.metric_labels = {}
        main_layout = QVBoxLayout(self)
        main_layout.setContentsMargins(28, 24, 28, 24)
        main_layout.setSpacing(16)
        title = QLabel("Sales Performance Overview")
        title.setObjectName("SummaryTitle")
        main_layout.addWidget(title)
        subtitle = QLabel("Monitor sell-through, tender mix, and best sellers without leaving this dashboard.")
        subtitle.setObjectName("SummarySubtitle")
        subtitle.setWordWrap(True)
        main_layout.addWidget(subtitle)
        content_card = QFrame()
        content_card.setObjectName("SummaryCard")
        card_layout = QVBoxLayout(content_card)
        card_layout.setContentsMargins(20, 18, 20, 24)
        card_layout.setSpacing(20)
        content_row = QHBoxLayout()
        content_row.setSpacing(20)
        content_row.setContentsMargins(0, 0, 0, 0)
        card_layout.addLayout(content_row)
        table_container = QFrame()
        table_container.setObjectName("SummaryTableContainer")
        table_layout = QVBoxLayout(table_container)
        table_layout.setContentsMargins(0, 0, 0, 0)
        table_layout.setSpacing(0)
        self.table = QTableWidget()
        self.table.setColumnCount(6)
        self.table.setHorizontalHeaderLabels(
            ["Code", "STOCK #", "Product Name", "Qty Sold", "Unit Price", "Total Revenue"]
        )
        header = self.table.horizontalHeader()
        header.setDefaultAlignment(Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter)
        header.setHighlightSections(False)
        header.setSectionResizeMode(QHeaderView.ResizeMode.Interactive)
        header.setStretchLastSection(False)
        self.table.verticalHeader().setVisible(False)
        self.table.verticalHeader().setSectionResizeMode(QHeaderView.ResizeMode.Fixed)
        self.table.verticalHeader().setDefaultSectionSize(48)
        self.table.setSelectionBehavior(QTableWidget.SelectionBehavior.SelectRows)
        self.table.setAlternatingRowColors(True)
        self.table.setWordWrap(False)
        self.table.setSortingEnabled(True)
        self.table.setEditTriggers(QTableWidget.EditTrigger.NoEditTriggers)
        self.table.setShowGrid(False)
        QTimer.singleShot(0, self._set_summary_column_widths)
        table_layout.addWidget(self.table)
        content_row.addWidget(table_container, 3)
        side_panel = QFrame()
        side_panel.setObjectName("SummarySidePanel")
        side_layout = QVBoxLayout(side_panel)
        side_layout.setContentsMargins(12, 8, 12, 8)
        side_layout.setSpacing(16)
        metrics_grid = QGridLayout()
        metrics_grid.setHorizontalSpacing(12)
        metrics_grid.setVerticalSpacing(12)
        metrics_grid.setColumnStretch(0, 1)
        metrics_grid.setColumnStretch(1, 1)
        metric_order = [
            ("items", "Total Items Sold"),
            ("revenue", "Total Revenue"),
            ("cash", "Cash Tendered"),
            ("gcash", "GCash Tendered"),
            ("top", "Top Selling Product"),
        ]
        for idx, (key, label_text) in enumerate(metric_order):
            card = self._create_metric_card(key, label_text)
            metrics_grid.addWidget(card, idx // 2, idx % 2)
        side_layout.addLayout(metrics_grid)
        side_layout.addStretch()
        self.post_invoice_button = QPushButton("Post Sales Invoice")
        self.post_invoice_button.setObjectName("SummaryAction")
        self.post_invoice_button.setCursor(Qt.CursorShape.PointingHandCursor)
        self.post_invoice_button.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Fixed)
        self.export_excel_button = QPushButton("Export to Excel")
        self.export_excel_button.setObjectName("SummaryAction")
        self.export_excel_button.setCursor(Qt.CursorShape.PointingHandCursor)
        self.export_excel_button.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Fixed)
        self.export_pdf_button = QPushButton("Export to PDF")
        self.export_pdf_button.setObjectName("SummaryAction")
        self.export_pdf_button.setCursor(Qt.CursorShape.PointingHandCursor)
        self.export_pdf_button.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Fixed)
        self.export_local_button = QPushButton("Export Local Items")
        self.export_local_button.setObjectName("SummaryAction")
        self.export_local_button.setCursor(Qt.CursorShape.PointingHandCursor)
        self.export_local_button.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Fixed)
        self.clear_summary_button = QPushButton("Clear Summary")
        self.clear_summary_button.setObjectName("SummaryAction")
        self.clear_summary_button.setCursor(Qt.CursorShape.PointingHandCursor)
        self.clear_summary_button.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Fixed)
        side_layout.addWidget(self.post_invoice_button)
        side_layout.addWidget(self.export_excel_button)
        side_layout.addWidget(self.export_pdf_button)
        side_layout.addWidget(self.export_local_button)
        side_layout.addWidget(self.clear_summary_button)
        content_row.addWidget(side_panel, 1)
        main_layout.addWidget(content_card)
        self.post_invoice_button.clicked.connect(self.trigger_post_sales_invoice)
        self.export_excel_button.clicked.connect(self.export_to_excel)
        self.export_pdf_button.clicked.connect(self.export_to_pdf)
        self.export_local_button.clicked.connect(self.export_local_items_summary)
        self.clear_summary_button.clicked.connect(self.prompt_clear_summary)
        self.populate_sales_summary()
        self.update_metrics()
        self.apply_theme_styles()
    def trigger_post_sales_invoice(self):
        parent = self.parent()
        if not parent or not hasattr(parent, "post_sales_invoice"):
            show_error("Unavailable", "Posting sales invoices is not available right now.", self)
            return
        result = parent.post_sales_invoice(parent_widget=self)
        if result:
            self.populate_sales_summary()
            self.update_metrics()
    def prompt_clear_summary(self):
        parent = self.parent()
        if not parent or not hasattr(parent, "clear_sales_summary_with_reference"):
            show_error("Unavailable", "Clearing the sales summary is not available right now.", self)
            return
        ref_no, ok = QInputDialog.getText(
            self,
            "Clear Sales Summary",
            "Enter the SI / Reference Number to tag these transactions:",
        )
        if not ok:
            return
        ref_no = (ref_no or "").strip()
        if not ref_no:
            show_error("Missing Reference", "A valid SI / reference number is required.", self)
            return
        confirm = QMessageBox.question(
            self,
            "Confirm Clear",
            f"Tag all unposted sales with reference '{ref_no}' and clear the summary?",
            QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
            QMessageBox.StandardButton.No,
        )
        if confirm != QMessageBox.StandardButton.Yes:
            return
        if parent.clear_sales_summary_with_reference(ref_no, parent_widget=self):
            self.populate_sales_summary()
            self.update_metrics()
    def _prompt_clear_specific_skus(self, skus, reason_label):
        parent = self.parent()
        if not parent or not hasattr(parent, "clear_sales_summary_with_reference"):
            show_error("Unavailable", "Clearing the sales summary is not available right now.", self)
            return
        auto_ref = parent.generate_local_reference_label() if hasattr(parent, "generate_local_reference_label") else generate_reference_code(LOCAL_EXPORT_REFERENCE_PREFIX)
        confirm = QMessageBox.question(
            self,
            "Confirm Clear",
            f"Automatically tag {len(skus)} exported item(s) with reference '{auto_ref}' and remove them from the dashboard?",
            QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
            QMessageBox.StandardButton.No,
        )
        if confirm != QMessageBox.StandardButton.Yes:
            return
        if parent.clear_sales_summary_with_reference(
            auto_ref,
            parent_widget=self,
            target_skus=skus,
            clear_reason="local_export",
            auto_generated=True,
        ):
            if hasattr(parent, "log_user_action"):
                parent.log_user_action(
                    "Cleared exported items",
                    f"{reason_label} | Reference {auto_ref} | SKUs: {len(skus)}",
                )
            self.populate_sales_summary()
            self.update_metrics()
    def _create_metric_card(self, key, title):
        card = QFrame()
        card.setObjectName("MetricCard")
        card.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Minimum)
        layout = QVBoxLayout(card)
        layout.setContentsMargins(14, 12, 14, 12)
        layout.setSpacing(6)
        label_title = QLabel(title)
        label_title.setObjectName("MetricTitle")
        label_value = QLabel("--")
        label_value.setObjectName("MetricValue")
        label_value.setWordWrap(True)
        label_value.setAlignment(Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter)
        layout.addWidget(label_title)
        layout.addWidget(label_value)
        self.metric_labels[key] = label_value
        return card
    @staticmethod
    def _hex_to_rgb(value):
        value = value.lstrip("#")
        return tuple(int(value[i:i+2], 16) for i in (0, 2, 4))
    @staticmethod
    def _rgb_to_hex(rgb):
        r, g, b = (max(0, min(255, int(round(v)))) for v in rgb)
        return "#{:02x}{:02x}{:02x}".format(r, g, b)
    @classmethod
    def _mix_color(cls, color_a, color_b, ratio):
        ratio = max(0.0, min(1.0, ratio))
        ra, ga, ba = cls._hex_to_rgb(color_a)
        rb, gb, bb = cls._hex_to_rgb(color_b)
        return cls._rgb_to_hex((
            ra + (rb - ra) * ratio,
            ga + (gb - ga) * ratio,
            ba + (bb - ba) * ratio,
        ))
    def apply_theme_styles(self):
        effective = (getattr(self.parent(), "current_effective_theme", None) or current_theme_effective or "light").lower()
        tokens = get_theme_tokens(effective)
        if effective == "dark":
            table_bg = self._mix_color(tokens["card_bg"], "#000000", 0.18)
            side_panel_bg = self._mix_color(tokens["card_bg"], "#000000", 0.28)
            metric_bg = self._mix_color(tokens["card_bg"], "#000000", 0.12)
            metric_border = self._mix_color(metric_bg, "#000000", 0.4)
            metric_border_style = f"border: 1px solid {metric_border};"
            button_bg = self._mix_color(tokens["card_bg"], "#ffffff", 0.05)
            button_hover = self._mix_color(button_bg, "#ffffff", 0.12)
            button_pressed = self._mix_color(button_bg, "#000000", 0.25)
            button_text = tokens["title"]
            button_border = self._mix_color(button_bg, "#000000", 0.35)
            table_border = self._mix_color(tokens["card_bg"], "#ffffff", 0.2)
            header_bg = self._mix_color(tokens["card_bg"], "#ffffff", 0.18)
            header_text = tokens["title"]
            alt_row = self._mix_color(table_bg, "#ffffff", 0.08)
        else:
            table_bg = self._mix_color(tokens["card_bg"], "#000000", 0.05)
            side_panel_bg = self._mix_color(tokens["card_bg"], "#000000", 0.02)
            metric_bg = self._mix_color(tokens["card_bg"], "#ffffff", 0.7)
            metric_border = self._mix_color(metric_bg, "#000000", 0.12)
            metric_border_style = f"border: 1px solid {metric_border};"
            button_bg = "#f3f4f6"
            button_hover = "#e5e7eb"
            button_pressed = "#d1d5db"
            button_text = "#1f2937"
            button_border = "#d1d5db"
            table_border = self._mix_color(tokens["card_bg"], "#000000", 0.1)
            header_bg = self._mix_color(tokens["card_bg"], "#000000", 0.12)
            header_text = "#1f2937"
            alt_row = self._mix_color(table_bg, "#000000", 0.04)
        self.setStyleSheet(f"""
            QDialog {{
                background-color: {tokens['background']};
                color: {tokens['text']};
            }}
            QLabel#SummaryTitle {{
                font-size: 20px;
                font-weight: 600;
                color: {tokens['title']};
            }}
            QLabel#SummarySubtitle {{
                font-size: 12px;
                color: {tokens['subtitle']};
            }}
            QFrame#SummaryCard {{
                background: {tokens['card_bg']};
                border-radius: 12px;
                border: 1px solid {tokens['card_border']};
            }}
            QFrame#SummaryTableContainer {{
                background: {table_bg};
                border-radius: 12px;
                border: 1px solid {table_border};
            }}
            QFrame#SummarySidePanel {{
                background: {side_panel_bg};
                border-radius: 12px;
                border: 1px solid {table_border};
            }}
            QFrame#MetricCard {{
                background: {metric_bg};
                {metric_border_style}
                border-radius: 10px;
            }}
            QLabel#MetricTitle {{
                font-size: 12px;
                font-weight: 600;
                color: {tokens['muted']};
                letter-spacing: 0.05em;
            }}
            QLabel#MetricValue {{
                font-size: 18px;
                font-weight: 600;
                color: {tokens['title']};
            }}
            QPushButton#SummaryAction {{
                background-color: {button_bg};
                color: {button_text};
                border-radius: 12px;
                padding: 12px 18px;
                font-weight: 600;
                border: 1px solid {button_border};
                text-align: left;
                min-height: 44px;
            }}
            QPushButton#SummaryAction:hover {{
                background-color: {button_hover};
            }}
            QPushButton#SummaryAction:pressed {{
                background-color: {button_pressed};
            }}
            QTableWidget {{
                background-color: {table_bg};
                alternate-background-color: {alt_row};
                border: 1px solid {table_border};
                border-radius: 10px;
                gridline-color: {table_border};
                font-size: 13px;
            }}
            QTableWidget::item {{
                padding: 10px;
            }}
            QHeaderView::section {{
                background-color: {header_bg};
                color: {header_text};
                font-size: 13px;
                font-weight: 600;
                border: none;
                padding: 10px 12px;
            }}
        """)
        palette = QPalette(self.table.palette())
        palette.setColor(QPalette.ColorRole.Base, QColor(table_bg))
        palette.setColor(QPalette.ColorRole.AlternateBase, QColor(alt_row))
        palette.setColor(QPalette.ColorRole.Text, QColor(tokens["text"]))
        self.table.setPalette(palette)
        self.table.viewport().setAutoFillBackground(True)
    def _get_summary_context(self):
        parent = self.parent()
        products_map = getattr(parent, "products", {})
        dataset = getattr(parent, "sales_summary", sales_summary) or {}
        return products_map, dataset, total_cash_tendered, total_gcash_tendered
    def populate_sales_summary(self):
        products, dataset, *_ = self._get_summary_context()
        all_codes = sorted(set(products.keys()) | set(dataset.keys()))
        self.table.setRowCount(len(all_codes))
        for row, barcode in enumerate(all_codes):
            variants = products.get(barcode, [])
            variant = variants[0] if variants else {}
            product_name = sanitize_product_name(variant.get('name'), barcode) or barcode
            code_value = variant.get('code') or ""
            sales_data = dataset.get(barcode, {"qty_sold": 0, "revenue": 0.0})
            quantity_sold = sales_data.get('qty_sold', 0)
            total_revenue = sales_data.get('revenue', 0.0)
            price_per_item = total_revenue / quantity_sold if quantity_sold else 0.0
            self.table.setItem(row, 0, QTableWidgetItem(code_value))
            self.table.setItem(row, 1, QTableWidgetItem(barcode))
            self.table.setItem(row, 2, QTableWidgetItem(product_name))
            self.table.setItem(row, 3, QTableWidgetItem(f"{quantity_sold:,}"))
            self.table.setItem(row, 4, QTableWidgetItem(f"P{price_per_item:,.2f}"))
            self.table.setItem(row, 5, QTableWidgetItem(f"P{total_revenue:,.2f}"))
        QTimer.singleShot(0, self._set_summary_column_widths)
    def _set_summary_column_widths(self):
        if not self.table or self.table.columnCount() < 6:
            return
        viewport_width = self.table.viewport().width()
        if viewport_width <= 0:
            return
        padding = 28
        static_columns = {
            0: 120,  # Code
            1: 140,  # Stock No.
            3: 120,  # Qty Sold
            4: 140,  # Unit Price
            5: 160,  # Total Revenue
        }
        other_total = 0
        for index, minimum in static_columns.items():
            hint = self.table.sizeHintForColumn(index)
            width = max(hint + padding, minimum)
            self.table.setColumnWidth(index, width)
            other_total += width
        remaining = viewport_width - other_total
        product_hint = self.table.sizeHintForColumn(2) + padding
        product_min = 220
        product_width = max(product_min, min(product_hint, max(remaining, product_min)))
        self.table.setColumnWidth(2, product_width)
    def resizeEvent(self, event):
        super().resizeEvent(event)
        self._set_summary_column_widths()
    def update_metrics(self):
        products, dataset, cash_total, gcash_total = self._get_summary_context()
        total_quantity_sold = sum(data.get('qty_sold', 0) for data in dataset.values())
        total_revenue = sum(data.get('revenue', 0.0) for data in dataset.values())
        best_code = None
        best_qty = 0
        for barcode, data in dataset.items():
            qty = data.get('qty_sold', 0)
            if qty > best_qty:
                best_qty = qty
                best_code = barcode
        top_label = "No sales recorded yet"
        if best_code:
            if best_code in products and products[best_code]:
                product_name = sanitize_product_name(products[best_code][0].get('name'), best_code) or best_code
            else:
                product_name = best_code
            top_label = f"{product_name}\n{best_qty:,} sold"
        self.metric_labels["items"].setText(f"{total_quantity_sold:,}")
        self.metric_labels["revenue"].setText(f"P{total_revenue:,.2f}")
        self.metric_labels["cash"].setText(f"P{cash_total:,.2f}")
        self.metric_labels["gcash"].setText(f"P{gcash_total:,.2f}")
        self.metric_labels["top"].setText(top_label)
    def _assemble_sales_rows(self, products, dataset):
        all_codes = set(products.keys()) | set(dataset.keys())
        rows = []
        for barcode in sorted(all_codes):
            record = dataset.get(barcode) or {}
            qty_sold = record.get("qty_sold", 0)
            revenue = float(record.get("revenue", 0.0) or 0.0)
            if qty_sold <= 0 and abs(revenue) < 0.0001:
                continue
            variants = products.get(barcode, [])
            variant = variants[0] if variants else {}
            product_name = sanitize_product_name(variant.get("name"), barcode) or barcode
            price_per_item = revenue / qty_sold if qty_sold else 0.0
            rows.append({
                "Code": variant.get("code") or "",
                "STOCK #": barcode,
                "Product Name": product_name,
                "Qty Sold": qty_sold,
                "Unit Price": price_per_item,
                "Total Revenue": revenue,
            })
        return rows
    def _post_export_reset_prompt(self, label, file_path):
        parent = self.parent()
        if parent and hasattr(parent, "log_user_action"):
            parent.log_user_action(
                "Exported sales summary",
                f"{label} | File: {file_path}",
            )
        result = QMessageBox.question(
            self,
            "Reset Totals?",
            "Do you want to tag an SI/reference and clear the current session now?",
            QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
            QMessageBox.StandardButton.No,
        )
        if result == QMessageBox.StandardButton.Yes:
            self.prompt_clear_summary()
        else:
            # Refresh views so any new data is reflected.
            self.populate_sales_summary()
            self.update_metrics()
    def _apply_sales_sheet_formatting(
        self,
        worksheet,
        df,
        workbook,
        *,
        include_tenders=False,
        cash_total=0.0,
        gcash_total=0.0,
    ):
        """Apply consistent header styling and auto-fit the sales summary columns."""
        currency_format = workbook.add_format({"num_format": "Php #,##0.00"})
        qty_format = workbook.add_format({"num_format": "#,##0"})
        header_format = workbook.add_format(
            {
                "bold": True,
                "bg_color": "#e5e7eb",
                "font_color": "#111827",
                "align": "left",
                "valign": "vcenter",
                "bottom": 1,
            }
        )
        bold_format = workbook.add_format({"bold": True})
        column_formats = {
            "Qty Sold": qty_format,
            "Unit Price": currency_format,
            "Total Revenue": currency_format,
        }
        self._autofit_sales_columns(
            worksheet,
            df,
            column_formats,
            include_tenders=include_tenders,
            cash_total=cash_total,
            gcash_total=gcash_total,
        )
        for col_idx, column_name in enumerate(df.columns):
            worksheet.write(0, col_idx, column_name, header_format)
        worksheet.set_row(len(df) - 1, None, bold_format)
        return {
            "currency": currency_format,
            "qty": qty_format,
            "bold": bold_format,
        }

    def _write_sales_dataframe(
        self,
        file_path,
        df,
        sheet_name,
        *,
        include_tenders=False,
        cash_total=0.0,
        gcash_total=0.0,
    ):
        """
        Save a pandas DataFrame to Excel. Uses xlsxwriter formatting when available.
        Returns True if advanced formatting was applied.
        """
        if has_xlsxwriter_support():
            with pd.ExcelWriter(file_path, engine="xlsxwriter") as writer:
                df.to_excel(writer, sheet_name=sheet_name, index=False)
                workbook = writer.book
                worksheet = writer.sheets[sheet_name]
                formats = self._apply_sales_sheet_formatting(
                    worksheet,
                    df,
                    workbook,
                    include_tenders=include_tenders,
                    cash_total=cash_total,
                    gcash_total=gcash_total,
                )
                if include_tenders:
                    row_after = len(df) + 1
                    worksheet.write(row_after, 0, "Cash:", formats["bold"])
                    worksheet.write(row_after, 1, cash_total, formats["currency"])
                    worksheet.write(row_after + 1, 0, "GCash:", formats["bold"])
                    worksheet.write(row_after + 1, 1, gcash_total, formats["currency"])
            return True
        # Fallback without styling – relies on pandas default engine (typically openpyxl)
        try:
            df.to_excel(file_path, sheet_name=sheet_name, index=False)
        except ModuleNotFoundError as exc:
            raise ModuleNotFoundError(
                "Excel export requires an engine such as 'xlsxwriter'. "
                "Install it via 'pip install xlsxwriter' and try again."
            ) from exc
        return False
    def _autofit_sales_columns(
        self,
        worksheet,
        df,
        column_formats,
        *,
        include_tenders=False,
        cash_total=0.0,
        gcash_total=0.0,
    ):
        """Resize Excel columns so headers and values remain readable."""
        padding = 2
        max_width = 60
        tender_samples = {
            0: ["Cash:", "GCash:"] if include_tenders else [],
            1: (
                [f"Php {cash_total:,.2f}", f"Php {gcash_total:,.2f}"]
                if include_tenders
                else []
            ),
        }
        for col_idx, column_name in enumerate(df.columns):
            samples = [column_name]
            samples.extend(
                self._preview_value_for_column(column_name, value)
                for value in df[column_name]
            )
            samples.extend(tender_samples.get(col_idx, []))
            filtered = [s for s in samples if isinstance(s, str)]
            if not filtered:
                continue
            length = max(len(entry) for entry in filtered)
            width = min(max(length + padding, 10), max_width)
            worksheet.set_column(
                col_idx,
                col_idx,
                width,
                column_formats.get(column_name),
            )
    @staticmethod
    def _preview_value_for_column(column_name, value):
        """Return the display string used for auto-fit length calculations."""
        if value in ("", None) or pd.isna(value):
            return ""
        if column_name == "Qty Sold":
            try:
                return f"{int(float(value)):,}"
            except (TypeError, ValueError):
                return ""
        if column_name in {"Unit Price", "Total Revenue"}:
            try:
                return f"Php {float(value):,.2f}"
            except (TypeError, ValueError):
                return ""
        return str(value)
    @staticmethod
    def _compute_pdf_column_widths(table_data, total_width=460, min_widths=None):
        """Derive column widths proportionally to the content length."""
        if not table_data:
            return []
        column_count = len(table_data[0])
        min_widths = min_widths or [60] * column_count
        char_unit = 4.2
        max_lengths = [0] * column_count
        for row in table_data:
            for idx, cell in enumerate(row):
                text = str(cell)
                max_lengths[idx] = max(max_lengths[idx], len(text))
        widths = []
        for idx, length in enumerate(max_lengths):
            width = max(min_widths[idx], length * char_unit)
            widths.append(width)
        total = sum(widths)
        if total <= 0:
            return min_widths
        scale = min(1.0, total_width / total)
        return [width * scale for width in widths]
    def export_to_excel(self):
        products, dataset, cash_total, gcash_total = self._get_summary_context()
        rows = self._assemble_sales_rows(products, dataset)
        if not rows:
            QMessageBox.information(self, "No Data", "No sales data to export.")
            return
        file_path, _ = QFileDialog.getSaveFileName(self, "Export Sales Summary to Excel", "", "Excel Files (*.xlsx *.xls)")
        if not file_path:
            return
        if not (file_path.lower().endswith(".xlsx") or file_path.lower().endswith(".xls")):
            file_path += ".xlsx"
        try:
            df = pd.DataFrame(
                rows,
                columns=["Code", "STOCK #", "Product Name", "Qty Sold", "Unit Price", "Total Revenue"],
            )
            total_qty = df["Qty Sold"].sum()
            total_revenue = df["Total Revenue"].sum()
            totals_df = pd.DataFrame([{
                "Code": "",
                "STOCK #": "",
                "Product Name": "Totals",
                "Qty Sold": total_qty,
                "Unit Price": "",
                "Total Revenue": total_revenue,
            }])
            df_with_totals = pd.concat([df, totals_df], ignore_index=True)
            formatted = self._write_sales_dataframe(
                file_path,
                df_with_totals,
                "Sales Summary",
                include_tenders=True,
                cash_total=cash_total,
                gcash_total=gcash_total,
            )
            QMessageBox.information(self, "Export Successful", f"Sales summary has been exported to:\n{file_path}")
            if not formatted:
                show_warning(
                    "Install xlsxwriter for styling",
                    "Excel export succeeded without styling because 'xlsxwriter' is not installed.\n"
                    "Run 'pip install xlsxwriter' to enable formatted reports.",
                    self,
                )
            self._post_export_reset_prompt("Excel", file_path)
        except Exception as e:
            QMessageBox.critical(self, "Export Error", f"Failed to export sales summary to Excel:\n{e}")
    def export_to_pdf(self):
        products, dataset, cash_total, gcash_total = self._get_summary_context()
        rows = self._assemble_sales_rows(products, dataset)
        if not rows:
            QMessageBox.information(self, "No Data", "No sales data to export.")
            return
        file_path, _ = QFileDialog.getSaveFileName(self, "Export Sales Summary to PDF", "", "PDF Files (*.pdf)")
        if not file_path:
            return
        if not file_path.lower().endswith(".pdf"):
            file_path += ".pdf"
        try:
            doc = SimpleDocTemplate(
                file_path,
                pagesize=A4,
                rightMargin=40,
                leftMargin=40,
                topMargin=60,
                bottomMargin=40,
            )
            styles = getSampleStyleSheet()
            title_style = styles["Heading1"]
            title_style.fontSize = 24
            title_style.leading = 30
            title_style.alignment = 1
            elements = [
                Paragraph("Sales Summary Report", title_style),
                Spacer(1, 24),
            ]
            headers = ["Code", "STOCK #", "Product Name", "Qty Sold", "Unit Price", "Total Revenue"]
            table_data = [headers]
            total_quantity_sold = 0
            total_revenue = 0.0
            max_qty = -1
            most_demanded_name = None
            for entry in rows:
                qty = entry["Qty Sold"]
                revenue = entry["Total Revenue"]
                unit_price = entry["Unit Price"]
                total_quantity_sold += qty
                total_revenue += revenue
                if qty > max_qty:
                    max_qty = qty
                    most_demanded_name = entry["Product Name"]
                table_data.append([
                    entry["Code"],
                    entry["STOCK #"],
                    entry["Product Name"],
                    f"{qty:,}",
                    f"P{unit_price:,.2f}",
                    f"P{revenue:,.2f}",
                ])
            col_widths = self._compute_pdf_column_widths(
                table_data,
                total_width=480,
                min_widths=[70, 80, 150, 70, 80, 120],
            )
            sales_table = Table(
                table_data,
                colWidths=col_widths,
                repeatRows=1,
            )
            sales_table.setStyle(TableStyle([
                ('TEXTCOLOR', (0, 0), (-1, -1), colors.black),
                ('ALIGN', (0, 0), (1, -1), 'LEFT'),
                ('ALIGN', (2, 1), (-1, -1), 'RIGHT'),
                ('FONTNAME', (0, 0), (-1, 0), 'Helvetica-Bold'),
                ('FONTNAME', (0, 1), (-1, -1), 'Helvetica'),
                ('FONTSIZE', (0, 0), (-1, 0), 11),
                ('FONTSIZE', (0, 1), (-1, -1), 9.5),
                ('BOTTOMPADDING', (0, 0), (-1, 0), 8),
                ('TOPPADDING', (0, 1), (-1, -1), 6),
                ('BOTTOMPADDING', (0, 1), (-1, -1), 6),
                ('LEFTPADDING', (0, 0), (-1, -1), 8),
                ('RIGHTPADDING', (0, 0), (-1, -1), 8),
                ('VALIGN', (0, 0), (-1, -1), 'MIDDLE'),
                ('LINEABOVE', (0, 0), (-1, 0), 0.75, colors.black),
                ('LINEBELOW', (0, 0), (-1, 0), 1.0, colors.black),
                ('INNERGRID', (0, 1), (-1, -1), 0.25, colors.black),
                ('BOX', (0, 0), (-1, -1), 0.75, colors.black),
            ]))
            elements.append(sales_table)
            elements.append(Spacer(1, 18))
            summary_rows = [
                ("Total Items Sold:", f"{total_quantity_sold:,}"),
                ("Total Revenue:", f"P{total_revenue:,.2f}"),
                ("Cash Tendered:", f"P{cash_total:,.2f}"),
                ("GCash Tendered:", f"P{gcash_total:,.2f}"),
            ]
            summary_table = Table(
                summary_rows,
                colWidths=[170, 200],
                hAlign='LEFT',
            )
            summary_table.setStyle(TableStyle([
                ('TEXTCOLOR', (0, 0), (-1, -1), colors.black),
                ('FONTNAME', (0, 0), (-1, -1), 'Helvetica'),
                ('FONTSIZE', (0, 0), (-1, -1), 11),
                ('ALIGN', (0, 0), (-1, -1), 'LEFT'),
                ('VALIGN', (0, 0), (-1, -1), 'MIDDLE'),
                ('LEFTPADDING', (0, 0), (-1, -1), 12),
                ('RIGHTPADDING', (0, 0), (-1, -1), 12),
                ('TOPPADDING', (0, 0), (-1, -1), 8),
                ('BOTTOMPADDING', (0, 0), (-1, -1), 8),
                ('LINEABOVE', (0, 0), (-1, 0), 0.5, colors.black),
                ('LINEBELOW', (0, -1), (-1, -1), 0.5, colors.black),
            ]))
            elements.append(summary_table)
            elements.append(Spacer(1, 18))
            heading2_style = styles['Heading2']
            heading2_style.textColor = colors.black
            heading2_style.fontSize = 16
            elements.append(Paragraph("Most In-Demand Item", heading2_style))
            demand_style = styles['Normal']
            demand_style.fontSize = 13
            elements.append(Spacer(1, 6))
            if most_demanded_name:
                elements.append(Paragraph(f"{most_demanded_name} (Sold: {max_qty:,} units)", demand_style))
            else:
                elements.append(Paragraph("No sales data available", demand_style))
            doc.build(elements)
            QMessageBox.information(self, "Export Successful", f"Sales summary has been exported to:\n{file_path}")
            self._post_export_reset_prompt("PDF", file_path)
        except Exception as e:
            QMessageBox.critical(self, "Export Error", f"Failed to export sales summary to PDF:\n{e}")
    def export_local_items_summary(self):
        parent = self.parent()
        if not parent or not hasattr(parent, "get_api_catalog_skus"):
            show_error("Unavailable", "API catalog access is not available right now.", self)
            return
        api_skus = parent.get_api_catalog_skus(parent_widget=self)
        if api_skus is None:
            return
        products, dataset, *_ = self._get_summary_context()
        rows = self._assemble_sales_rows(products, dataset)
        local_rows = [row for row in rows if row["STOCK #"] not in api_skus]
        if not local_rows:
            QMessageBox.information(
                self,
                "No Local Items",
                "All sales summary items are present in the API catalog.",
            )
            return
        local_skus = sorted({row["STOCK #"] for row in local_rows})
        file_path, _ = QFileDialog.getSaveFileName(
            self,
            "Export Local Items Summary",
            "",
            "Excel Files (*.xlsx *.xls)",
        )
        if not file_path:
            return
        if not (file_path.lower().endswith(".xlsx") or file_path.lower().endswith(".xls")):
            file_path += ".xlsx"
        try:
            df = pd.DataFrame(
                local_rows,
                columns=["Code", "STOCK #", "Product Name", "Qty Sold", "Unit Price", "Total Revenue"],
            )
            total_qty = df["Qty Sold"].sum()
            total_revenue = df["Total Revenue"].sum()
            totals_df = pd.DataFrame([{
                "Code": "",
                "STOCK #": "",
                "Product Name": "Totals",
                "Qty Sold": total_qty,
                "Unit Price": "",
                "Total Revenue": total_revenue,
            }])
            df_with_totals = pd.concat([df, totals_df], ignore_index=True)
            formatted = self._write_sales_dataframe(
                file_path,
                df_with_totals,
                "Local Items",
            )
            QMessageBox.information(
                self,
                "Export Successful",
                f"Local-only items have been exported to:\n{file_path}",
            )
            if not formatted:
                show_warning(
                    "Install xlsxwriter for styling",
                    "Local items export finished without Excel styling because 'xlsxwriter' is missing.\n"
                    "Install it with 'pip install xlsxwriter' for formatted sheets.",
                    self,
                )
            if hasattr(parent, "log_user_action"):
                parent.log_user_action(
                    "Exported local-only summary",
                    f"Rows: {len(local_rows)} | File: {file_path}",
                )
            action = QMessageBox.question(
                self,
                "Tag Exported Items?",
                "Do you want to tag these exported local items with a reference and clear them now?",
                QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
                QMessageBox.StandardButton.No,
            )
            if action == QMessageBox.StandardButton.Yes:
                self._prompt_clear_specific_skus(local_skus, "Local export")
            else:
                self.populate_sales_summary()
                self.update_metrics()
        except Exception as exc:
            QMessageBox.critical(self, "Export Error", f"Failed to export local items:\n{exc}")
class SalesSummaryArchiveDialog(QDialog):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setWindowTitle("Sales Summary Archive")
        self.resize(1100, 620)
        self._filter_text = ""
        self.filter_timer = QTimer(self)
        self.filter_timer.setSingleShot(True)
        self.filter_timer.timeout.connect(self.load_transactions)
        layout = QVBoxLayout(self)
        layout.setContentsMargins(20, 18, 20, 20)
        layout.setSpacing(12)
        filter_row = QHBoxLayout()
        filter_row.setSpacing(12)
        filter_label = QLabel("Filter by Reference Number")
        filter_label.setObjectName("ArchiveFilterLabel")
        self.filter_input = QLineEdit()
        self.filter_input.setPlaceholderText("Enter ref_no to search...")
        self.filter_input.textChanged.connect(self.on_filter_text_changed)
        filter_row.addWidget(filter_label)
        filter_row.addWidget(self.filter_input)
        layout.addLayout(filter_row)
        self.table = QTableWidget(self)
        self.table.setColumnCount(9)
        self.table.setHorizontalHeaderLabels([
            "Transaction ID",
            "Sales No.",
            "Reference No.",
            "Date / Time",
            "Cashier",
            "Payment Method",
            "Total Amount",
            "Amount Tendered",
            "Change",
        ])
        header = self.table.horizontalHeader()
        header.setStretchLastSection(False)
        for index in range(9):
            header.setSectionResizeMode(index, QHeaderView.ResizeMode.ResizeToContents)
        self.table.verticalHeader().setVisible(False)
        self.table.setAlternatingRowColors(True)
        self.table.setSelectionBehavior(QTableWidget.SelectionBehavior.SelectRows)
        self.table.setEditTriggers(QTableWidget.EditTrigger.NoEditTriggers)
        self.table.setSortingEnabled(True)
        self.table.setWordWrap(False)
        layout.addWidget(self.table)
        self.apply_archive_styles()
        self.load_transactions()
    def apply_archive_styles(self):
        parent = self.parent()
        effective = (getattr(parent, "current_effective_theme", None) or current_theme_effective or "light").lower()
        tokens = get_theme_tokens(effective)
        alt = self._mix_color(tokens["card_bg"], "#000000", 0.06) if effective == "light" else self._mix_color(tokens["card_bg"], "#ffffff", 0.12)
        header_bg = self._mix_color(tokens["card_bg"], "#000000", 0.1)
        self.setStyleSheet(f"""
            QDialog {{
                background-color: {tokens['background']};
                color: {tokens['text']};
            }}
            QLabel#ArchiveFilterLabel {{
                font-size: 12px;
                font-weight: 600;
                color: {tokens['muted']};
                letter-spacing: 0.05em;
            }}
            QLineEdit {{
                padding: 8px 12px;
                border-radius: 8px;
                border: 1px solid {tokens['card_border']};
                background: {tokens['card_bg']};
                color: {tokens['text']};
            }}
            QTableWidget {{
                background-color: {tokens['card_bg']};
                alternate-background-color: {alt};
                border: 1px solid {tokens['card_border']};
                border-radius: 10px;
            }}
            QHeaderView::section {{
                background: {header_bg};
                font-weight: 600;
                padding: 8px 10px;
                border: none;
                color: {tokens['title']};
            }}
        """)
    def _mix_color(self, base_color, blend_color, amount):
        return SalesSummaryDialog._mix_color(base_color, blend_color, amount)
    def on_filter_text_changed(self, text):
        self._filter_text = (text or "").strip()
        self.filter_timer.start(250)
    def load_transactions(self):
        conn = get_db_connection(self)
        if not conn:
            self.table.setRowCount(0)
            return
        rows = []
        try:
            ensure_sales_reference_columns(conn)
            with conn.cursor(dictionary=True) as cursor:
                parts = [
                    "SELECT",
                    "  transaction_id,",
                    "  sales_no,",
                    "  ref_no,",
                    "  transaction_time,",
                    "  cashier_id,",
                    "  total_amount,",
                    "  payment_method,",
                    "  amount_tendered,",
                    "  change_given",
                    "FROM sales_transactions",
                ]
                params = []
                if self._filter_text:
                    parts.append("WHERE ref_no LIKE %s")
                    params.append(f"%{self._filter_text}%")
                parts.append("ORDER BY transaction_time DESC")
                sql = "\n".join(parts)
                if params:
                    cursor.execute(sql, params)
                else:
                    cursor.execute(sql)
                rows = cursor.fetchall()
        except Error as exc:
            show_error("Database Error", f"Failed to load sales transactions:\n{exc}", self)
        finally:
            try:
                conn.close()
            except Exception:
                pass
        self.populate_table(rows or [])
    def populate_table(self, rows):
        self.table.setRowCount(len(rows))
        for row_index, entry in enumerate(rows):
            transaction_id = entry.get("transaction_id")
            sales_no = entry.get("sales_no") or ""
            ref_no = entry.get("ref_no") or ""
            transaction_time = entry.get("transaction_time")
            formatted_time = self._format_datetime(transaction_time)
            cashier = entry.get("cashier_id") or ""
            payment_method = entry.get("payment_method") or ""
            total_amount = self._format_currency(entry.get("total_amount"))
            tendered = self._format_currency(entry.get("amount_tendered"))
            change = self._format_currency(entry.get("change_given"))
            values = [
                str(transaction_id),
                str(sales_no),
                ref_no,
                formatted_time,
                cashier,
                payment_method,
                total_amount,
                tendered,
                change,
            ]
            for col, value in enumerate(values):
                item = QTableWidgetItem(value)
                align = Qt.AlignmentFlag.AlignRight if col >= 6 else Qt.AlignmentFlag.AlignLeft
                item.setTextAlignment(align | Qt.AlignmentFlag.AlignVCenter)
                self.table.setItem(row_index, col, item)
        self.table.resizeColumnsToContents()
    def _format_currency(self, value):
        if value is None:
            return "-"
        try:
            amount = float(value)
        except (TypeError, ValueError):
            return "-"
        return f"P{amount:,.2f}"
    def _format_datetime(self, value):
        if not value:
            return ""
        if isinstance(value, datetime):
            return value.strftime("%b %d, %Y %I:%M %p")
        try:
            parsed = datetime.fromisoformat(str(value))
            return parsed.strftime("%b %d, %Y %I:%M %p")
        except Exception:
            return str(value)
class ArchiveDialog(QDialog):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setWindowTitle("Archived Receipts")
        self.setFixedSize(400, 600)
        self.scanner_worker = None  # Archive dialog does not use the scanner thread
        self.receipts_archive = parent.receipts_archive if hasattr(parent, "receipts_archive") else {}
        layout = QVBoxLayout()
        self.setLayout(layout)
        self.list_widget = QListWidget()
        self.list_widget.setFont(QFont("Segoe UI", 11))
        layout.addWidget(self.list_widget)
        self.populate_receipts()
        btn_export = QPushButton("Export Receipts")
        btn_export.setFixedHeight(40)
        btn_export.setStyleSheet("""
            QPushButton {
                background-color: #2563eb;
                color: white;
                font-weight: 600;
                border-radius: 12px;
                padding: 8px 16px;
            }
            QPushButton:hover {
                background-color: #1e40af;
            }
        """)
        btn_export.clicked.connect(self.export_receipts)
        layout.addWidget(btn_export)
        btn_void = QPushButton("Void Selected Receipt")
        btn_void.setFixedHeight(40)
        btn_void.setStyleSheet("""
            QPushButton {
                background-color: #dc2626;
                color: white;
                font-weight: 600;
                border-radius: 12px;
                padding: 8px 16px;
            }
            QPushButton:hover {
                background-color: #b91c1c;
            }
        """)
        btn_void.clicked.connect(self.handle_void_selected)
        layout.addWidget(btn_void)
        # Connect double click signal to display receipt
        self.list_widget.itemDoubleClicked.connect(self.show_receipt_view)
    def populate_receipts(self):
        """Populate the list widget with archived receipts."""
        self.list_widget.clear()
        for receipt_id in receipts_archive.keys():
            self.list_widget.addItem(receipt_id)
    def export_receipts(self):
        """Export all archived receipts to a selected folder."""
        global receipts_archive  # Declare receipts_archive as global at the beginning
        folder_path = QFileDialog.getExistingDirectory(self, "Select Folder to Export Receipts")
        if not folder_path:
            return  # User canceled the dialog
        for receipt_id, receipt_content in receipts_archive.items():
            # Sanitize the filename by replacing invalid characters
            sanitized_filename = receipt_id.replace(' ', '_').replace(':', '_').replace('#', '_') + '.txt'
            file_path = os.path.join(folder_path, sanitized_filename)
            try:
                with open(file_path, 'w', encoding='utf-8') as f:
                    f.write(receipt_content)
            except Exception as e:
                QMessageBox.critical(self, "Export Error", f"Failed to export receipt '{receipt_id}': {e}", QMessageBox.StandardButton.Ok)
        QMessageBox.information(self, "Export Successful", "All receipts have been exported successfully.", QMessageBox.StandardButton.Ok)
        # Reset receipts archive after successful export
        receipts_archive = {}
        save_receipts_archive()
        self.populate_receipts()
    def show_receipt_view(self, item):
        receipt_id = item.text()
        receipt_content = receipts_archive.get(receipt_id, "Receipt content not found.")
        dlg = ReceiptDialog(receipt_content, self)
        dlg.exec()

    def handle_void_selected(self):
        item = self.list_widget.currentItem()
        if not item:
            show_warning("Void Receipt", "Please select a receipt to void.", self)
            return
        receipt_id = item.text()
        password, ok = QInputDialog.getText(
            self,
            "Admin Confirmation",
            "Enter admin password to void the selected receipt:",
            QLineEdit.EchoMode.Password,
        )
        if not ok:
            return
        if password != ADMIN_PASSWORD:
            show_error("Authorization Failed", "Invalid admin password.", self)
            return
        confirm = QMessageBox.question(
            self,
            "Confirm Void",
            f"Voiding '{receipt_id}' will restore stock and remove its sales data.\nProceed?",
            QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
            QMessageBox.StandardButton.No,
        )
        if confirm != QMessageBox.StandardButton.Yes:
            return
        parent = self.parent()
        if not parent or not hasattr(parent, "void_archived_receipt"):
            show_error("Void Receipt", "POS window unavailable. Please try again.", self)
            return
        if parent.void_archived_receipt(receipt_id, parent_widget=self):
            self.populate_receipts()
    def closeEvent(self, event):
        if self.scanner_worker:
            try:
                self.scanner_worker.stop()
            except Exception:
                pass
        super().closeEvent(event)
class ReceiptDialog(QDialog):
    def __init__(self, receipt_text_content, parent=None):
        super().__init__(parent)
        self.setWindowTitle("Sales Receipt")
        self.resize(400, 700)
        self._receipt_text_content = receipt_text_content
        layout = QVBoxLayout()
        self.setLayout(layout)
        self.text_edit = QTextEdit()
        self.text_edit.setReadOnly(True)
        layout_info = compute_receipt_layout()
        preview_font = QFont(get_receipt_font_name())
        preview_font.setPointSizeF(layout_info["font_size"])
        self.text_edit.setFont(preview_font)
        self.text_edit.setText(receipt_text_content)
        layout.addWidget(self.text_edit)
        self.print_two_checkbox = QCheckBox("Print 2 copies")
        self.print_two_checkbox.setToolTip("Default prints 1 copy. Check to print 2 copies.")
        layout.addWidget(self.print_two_checkbox)
        btn_layout = QHBoxLayout()
        layout.addLayout(btn_layout)
        btn_print = QPushButton("Print Receipt")
        btn_print.setStyleSheet("background-color: #007BFF; color: white; font-weight: bold;")
        btn_print.clicked.connect(self._handle_print_clicked)
        btn_layout.addWidget(btn_print)
        btn_save_pdf = QPushButton("Save as PDF")
        btn_save_pdf.setStyleSheet("background-color: #28A745; color: white; font-weight: bold;")
        btn_save_pdf.clicked.connect(lambda: self.save_receipt_as_pdf(receipt_text_content))
        btn_layout.addWidget(btn_save_pdf)
        btn_close = QPushButton("Close")
        btn_close.clicked.connect(self.accept)
        btn_layout.addWidget(btn_close)
        self.reprint_shortcut = QShortcut(QKeySequence("Ctrl+R"), self)
        self.reprint_shortcut.activated.connect(self._handle_reprint_shortcut)

    def _handle_print_clicked(self):
        copies = 2 if self.print_two_checkbox.isChecked() else 1
        print_receipt_pdf(self._receipt_text_content, self, copies)

    def _handle_reprint_shortcut(self):
        print_receipt_pdf(self._receipt_text_content, self, copies=1)

    def save_receipt_as_pdf(self, receipt_text_content):
        file_path, _ = QFileDialog.getSaveFileName(self, "Save Receipt as PDF", "", "PDF Files (*.pdf)")
        if file_path:
            if not file_path.lower().endswith('.pdf'):
                file_path += '.pdf'
            save_receipt_pdf(receipt_text_content, file_path)
            show_info("Save Successful", f"Receipt saved as PDF: {file_path}", self)
def _normalize_receipt_lines(receipt_text):
    # Convert receipt content (string, list, dict, etc.) into a flat list of printable strings.
    def strip_size_tag(value):
        if value is None:
            return ""
        if not isinstance(value, str):
            value = str(value)
        match = RECEIPT_SIZE_TAG_PATTERN.match(value)
        if match:
            value = value[match.end():]
        return value
    def sanitize(lines):
        return [strip_size_tag(line) for line in lines]
    if receipt_text is None:
        return []
    if isinstance(receipt_text, str):
        return sanitize(receipt_text.splitlines())
    if isinstance(receipt_text, dict):
        if "text" in receipt_text:
            text_value = receipt_text.get("text")
            if isinstance(text_value, (list, tuple, set)):
                lines = []
                for item in text_value:
                    lines.extend(_normalize_receipt_lines(item))
                return sanitize(lines)
            if text_value is None:
                return [""]
            return sanitize(str(text_value).splitlines())
        if "lines" in receipt_text and isinstance(receipt_text["lines"], (list, tuple, set)):
            lines = []
            for item in receipt_text["lines"]:
                lines.extend(_normalize_receipt_lines(item))
            return sanitize(lines)
        return sanitize([json.dumps(receipt_text, ensure_ascii=False)])
    if isinstance(receipt_text, (list, tuple, set)):
        lines = []
        for item in receipt_text:
            lines.extend(_normalize_receipt_lines(item))
        return sanitize(lines)
    return sanitize(str(receipt_text).splitlines())


def _parse_currency_amount(value):
    try:
        return float(str(value).replace(",", ""))
    except (TypeError, ValueError):
        return 0.0


def parse_receipt_payment_breakdown(receipt_text):
    """
    Extract cash / gcash amounts and payment method label from receipt text content.
    """
    normalized_text = ""
    if isinstance(receipt_text, str):
        normalized_text = receipt_text
    else:
        normalized_text = "\n".join(_normalize_receipt_lines(receipt_text))

    def extract(label):
        pattern = rf"{label}\s*:\s*P?\s*([0-9][0-9,]*(?:\.\d{{1,2}})?)"
        match = re.search(pattern, normalized_text, flags=re.IGNORECASE)
        if match:
            return _parse_currency_amount(match.group(1))
        return 0.0

    cash_amount = extract("Cash")
    gcash_amount = extract("GCash")
    payment_method = None
    pm_match = re.search(r"Payment\s+Method\s*:\s*(.+)", normalized_text, flags=re.IGNORECASE)
    if pm_match:
        payment_method = pm_match.group(1).strip()
    return {
        "cash": cash_amount,
        "gcash": gcash_amount,
        "payment_method": payment_method,
    }


def print_receipt_pdf(receipt_text, parent=None, copies=None):
    layout = compute_receipt_layout()
    width_mm = RECEIPT_PAGE_WIDTH_MM
    height_mm = 297
    margin_left_right = RECEIPT_MARGIN_MM * mm
    margin_top_bottom = RECEIPT_TOP_MARGIN_MM * mm
    page_width = width_mm * mm
    page_height = height_mm * mm

    try:
        with tempfile.NamedTemporaryFile(delete=False, suffix=".pdf") as temp_pdf:
            temp_pdf_path = temp_pdf.name
    except Exception as exc:
        show_error("Print Error", f"Failed to create temporary PDF file:\n{exc}", parent)
        if parent and hasattr(parent, "log_user_action"):
            parent.log_user_action("Print job failed", f"Temporary PDF creation error: {exc}")
        return

    try:
        c = canvas.Canvas(temp_pdf_path, pagesize=(page_width, page_height))
        normalized_layout = dict(layout)
        font_name = normalized_layout.get("font_name") or get_receipt_font_name()
        font_size = normalized_layout.get("font_size", RECEIPT_BASE_FONT_SIZE)
        normalized_layout["font_name"] = font_name
        normalized_layout["font_size"] = font_size
        x_start = margin_left_right
        y_start = page_height - margin_top_bottom

        render_receipt_text(c, str(receipt_text), normalized_layout, x_start, y_start)
        c.showPage()
        c.save()
    except Exception as exc:
        show_error("Print Error", f"Failed to generate receipt PDF:\n{exc}", parent)
        if parent and hasattr(parent, "log_user_action"):
            parent.log_user_action("Print job failed", f"Receipt render error: {exc}")
        return

    try:
        requested_copies = int(copies) if copies is not None else 1
    except (TypeError, ValueError):
        requested_copies = 1
    copies_to_print = max(requested_copies, 1)
    for copy_index in range(copies_to_print):
        try:
            if sys.platform.startswith("win"):
                os.startfile(temp_pdf_path, "print")
            elif sys.platform.startswith("darwin"):
                subprocess.run(["lp", temp_pdf_path], check=True)
            else:
                subprocess.run(["lp", temp_pdf_path], check=True)
        except Exception as exc:
            show_error(
                "Print Error",
                f"Failed to print receipt copy {copy_index + 1}: {exc}",
                parent,
            )
            if parent and hasattr(parent, "log_user_action"):
                parent.log_user_action("Print job failed", f"Copy {copy_index + 1} error: {exc}")
            return
        if copy_index < copies_to_print - 1:
            time.sleep(3)

    show_info("Print Job", f"Printed {copies_to_print} receipt copies.", parent)
    if parent and hasattr(parent, "log_user_action"):
        parent.log_user_action("Printed receipt", f"{copies_to_print} copies")
def main():
    app = QApplication(sys.argv)
    preferred_theme = load_ui_preferences()
    apply_theme(app, preferred_theme)
    # Ensure image folder exists
    os.makedirs(PRODUCT_IMAGE_FOLDER, exist_ok=True)
    if not load_products_from_database():
        # Error shown inside load_products_from_database function
        sys.exit()
    if not load_promo_inventory():
        sys.exit()
    if not load_bundle_promos():
        sys.exit()
    if not load_basket_promos():
        sys.exit()
    rebuild_product_variant_lookup()
    load_users()
    # Load saved data
    load_inventory_summary()
    load_sales_summary()
    load_sales_vault()
    load_receipts_archive()
    load_tendered_amounts()  # Load tendered amounts at startup
    login_dlg = LoginDialog()
    if login_dlg.exec() == QDialog.DialogCode.Accepted:
        main_win = POSMainWindow(login_dlg.current_user_name)
        main_win.show()
        exit_code = app.exec()
        # Save data before exiting
        save_inventory_summary()
        save_sales_summary()
        save_receipts_archive()
        save_sales_vault()
        save_tendered_amounts()  # Save tendered amounts before closing
        sys.exit(exit_code)
    else:
        sys.exit()
if __name__ == "__main__":
    main()
