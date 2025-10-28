import sys
import os
import re
import csv
import glob
from datetime import datetime, timedelta
import time
from functools import partial
import tempfile
import subprocess
import json  # Import the json module
from copy import deepcopy
import shutil
import textwrap
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
from PIL import Image, ImageQt
from PyQt6.QtWidgets import (QApplication, QCompleter, QGroupBox, QMainWindow, QTableWidget, QTableWidgetItem, QWidget, QLabel, QLineEdit, QPushButton, QComboBox,
                             QListWidget, QListWidgetItem, QTextEdit, QHBoxLayout, QVBoxLayout, QGridLayout, QDialog,
                             QMessageBox, QInputDialog, QFileDialog, QScrollArea, QFrame, QSpinBox,
                             QDoubleSpinBox, QDialogButtonBox, QCheckBox, QHeaderView, QToolButton)
from PyQt6.QtGui import QColor, QPixmap, QAction, QActionGroup, QIcon, QFont, QPalette, QPainter, QPen, QBrush
from PyQt6.QtCore import Qt, QSize, QStringListModel, QPointF, QRectF, QThread, pyqtSignal
# --- Global Variables ---
products = {}  # Stores product data from CSV: {barcode: [{"name": "...", "price": ..., "stock": ..., "image_filename": "...", "promos": {...}}]}
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
product_variant_lookup = {}  # Maps SKU (including promo variants) to lookup data for scanning/searching
promo_inventory_map = {}  # Maps promo code to the number of base units consumed per sale
product_promo_columns = []  # Tracks additional promo pricing columns detected in the products CSV
bundle_promos = {}  # Stores bundle promos with their component details
current_theme_preference = "system"
current_theme_effective = "light"
basket_promos = []  # Stores basket-size promo tiers
BUNDLE_IMAGE_COLUMN_AVAILABLE = None  # Tracks bundles.image_filename availability
users_data = {}  # Stores usernames and hashed passwords: {username: {"password_hash": "...", "is_admin": bool}}
current_user_name = None  # Stores the username of the currently logged-in user
ADMIN_PASSWORD_FILE = "admin_password.txt"
DEFAULT_ADMIN_PASSWORD = "p@ssw0rd01"
PRODUCTS_CSV_FILE = "POSProducts.csv"  # Name of the CSV file for products
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
USERS_FILE = "users.txt"  # Name of the text file for user credentials
PRODUCT_IMAGE_FOLDER = os.path.join(BASE_DIR, "product_images")  # Folder where product images are stored
SUPPORTED_IMAGE_EXTENSIONS = (".png", ".jpg", ".jpeg", ".bmp", ".gif", ".webp")
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
DEFAULT_SALES_INVOICE_STUB_RESPONSE = {
    "code": 201,
    "message": "Sales invoice created",
    "data": {
        "id": 98541,
        "ref_no": "OS0026",
        "order_no": "EXHIBIT-2025-10-28",
        "txn_date": "2025-10-28",
        "amount_due": 12791.52,
        "warehouse_id": "3",
    },
    "warning": [],
}

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
    Ensures that a JSON file exists at the given path containing the default stub payload.
    """
    try:
        os.makedirs(os.path.dirname(os.path.abspath(file_path)), exist_ok=True)
    except Exception:
        pass
    candidate = os.path.abspath(file_path)
    if os.path.exists(candidate):
        return True
    try:
        with open(candidate, "w", encoding="utf-8") as fh:
            json.dump(DEFAULT_INVENTORY_STUB_DATA, fh, indent=2)
        return True
    except Exception as exc:
        show_warning("Inventory Stub", f"Failed to create stub file '{candidate}':\n{exc}", parent)
        return False
# --- Database configuration ---
DB_CONFIG = {
    "host": "localhost",
    "user": "user",
    "password": "philtop",
    "database": "pos_db",
    "use_pure": True,
}
# --- Promo pricing support tracking ---
PROMO_PRICE_COLUMN_AVAILABLE = None
PROMO_PRICE_WARNING_SHOWN = False
# --- New Global Variables for Auto-Saving ---
INVENTORY_SUMMARY_FILE = "inventory_summary.csv"
SALES_SUMMARY_FILE = "sales_summary.json"
RECEIPTS_ARCHIVE_FILE = "receipts_archive.json"
TENDERED_AMOUNTS_FILE = "tendered_amounts.json"
PROMO_INVENTORY_FILE = "PromoInventory.csv"
PROMO_BUNDLES_FILE = "PromoBundles.json"
UI_PREFERENCES_FILE = "ui_preferences.json"
BASKET_PROMOS_FILE = "BasketPromos.json"
# --- New Global Variable for Receipts Archive ---
receipts_archive = {}  # Stores all generated receipts: {"SALES#_TRANS#": "receipt_text_content"}
RECEIPT_FONT_NAME = "LucidaConsole"
FALLBACK_RECEIPT_FONT_NAME = "Courier"
RECEIPT_PAGE_WIDTH_MM = 58
RECEIPT_MARGIN_MM = 0.5
RECEIPT_TOP_MARGIN_MM = 2
RECEIPT_BASE_FONT_SIZE = 10
RECEIPT_MIN_FONT_SIZE = 8
RECEIPT_PRICE_COLUMN_WIDTH = 10
RECEIPT_LEFT_COLUMN_TARGET = 24
RECEIPT_LINE_SPACING_MULTIPLIER = 1.2
RECEIPT_BOLD_OFFSET_PT = 0.3
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
    # Try to add the column so promo pricing can match the CSV behavior.
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
def get_receipt_font_name():
    """
    Returns the registered font name to use for receipts.
    Attempts to register Lucida Console from the system fonts and falls back to Courier if unavailable.
    """
    try:
        pdfmetrics.getFont(RECEIPT_FONT_NAME)
        return RECEIPT_FONT_NAME
    except KeyError:
        possible_paths = []
        windows_dir = os.environ.get("WINDIR")
        if windows_dir:
            possible_paths.append(os.path.join(windows_dir, "Fonts", "Lucon.ttf"))
            possible_paths.append(os.path.join(windows_dir, "Fonts", "lucon.ttf"))
        possible_paths.append("Lucon.ttf")
        for candidate in possible_paths:
            if candidate and os.path.exists(candidate):
                try:
                    pdfmetrics.registerFont(TTFont(RECEIPT_FONT_NAME, candidate))
                    return RECEIPT_FONT_NAME
                except Exception as exc:
                    print(f"Warning: failed to register Lucida Console font from '{candidate}': {exc}")
                    continue
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
    try:
        with open(UI_PREFERENCES_FILE, 'r', encoding='utf-8') as f:
            data = json.load(f)
            theme = data.get("theme", "system")
            current_theme_preference = theme
            return theme
    except FileNotFoundError:
        return "system"
    except Exception as exc:
        print(f"Warning: failed to load UI preferences: {exc}")
        return "system"
def save_ui_preferences(theme):
    """Persists UI preferences such as theme selection to disk."""
    try:
        with open(UI_PREFERENCES_FILE, 'w', encoding='utf-8') as f:
            json.dump({"theme": theme}, f, ensure_ascii=False, indent=4)
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
    font_size = layout["font_size"]
    max_chars_per_line = max(int(layout["total_width"]), 1)
    line_height = font_size * layout.get("line_spacing", RECEIPT_LINE_SPACING_MULTIPLIER)
    bold_offset = layout.get("bold_offset", RECEIPT_BOLD_OFFSET_PT)
    current_y = start_y
    for line in receipt_text.split("\n"):
        if line:
            remaining = line
            while remaining:
                segment = remaining[:max_chars_per_line]
                _draw_bold_text(canvas_obj, start_x, current_y, segment, font_name, font_size, bold_offset)
                remaining = remaining[max_chars_per_line:]
                current_y -= line_height
        else:
            current_y -= line_height
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
        return deepcopy(DEFAULT_INVENTORY_STUB_DATA)
    candidate = os.path.abspath(file_path)
    try:
        with open(candidate, "r", encoding="utf-8") as f:
            data = json.load(f)
            if isinstance(data, dict):
                return data
        show_warning("Inventory Stub", f"Inventory stub file '{candidate}' does not contain a JSON object.", parent)
    except Exception as exc:
        show_warning("Inventory Stub", f"Failed to read inventory stub file '{candidate}':\n{exc}", parent)
    return deepcopy(DEFAULT_INVENTORY_STUB_DATA)
def ensure_sales_invoice_stub_file(file_path, parent=None):
    try:
        os.makedirs(os.path.dirname(os.path.abspath(file_path)), exist_ok=True)
    except Exception:
        pass
    candidate = os.path.abspath(file_path)
    if os.path.exists(candidate):
        return True
    try:
        with open(candidate, "w", encoding="utf-8") as fh:
            json.dump(DEFAULT_SALES_INVOICE_STUB_RESPONSE, fh, indent=2)
        return True
    except Exception as exc:
        show_warning("Sales Stub", f"Failed to create stub file '{candidate}':\n{exc}", parent)
        return False
def load_sales_invoice_stub_response(parent=None):
    if not ensure_api_settings_loaded(parent):
        return None
    file_path = api_settings.get("sales_stub_file") or "sales_invoice_stub.json"
    if not ensure_sales_invoice_stub_file(file_path, parent):
        return deepcopy(DEFAULT_SALES_INVOICE_STUB_RESPONSE)
    candidate = os.path.abspath(file_path)
    try:
        with open(candidate, "r", encoding="utf-8") as fh:
            data = json.load(fh)
            if isinstance(data, dict):
                return data
            show_warning("Sales Stub", f"Sales stub file '{candidate}' does not contain a JSON object.", parent)
    except Exception as exc:
        show_warning("Sales Stub", f"Failed to read sales stub file '{candidate}':\n{exc}", parent)
    return deepcopy(DEFAULT_SALES_INVOICE_STUB_RESPONSE)


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
# --- CSV Handling Functions ---
def load_products_from_csv(parent=None):
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
        supports_promo_prices = ensure_promo_price_column(conn)
        with conn.cursor(dictionary=True) as cursor:
            cursor.execute(
                """
                SELECT product_id, stock_no, name, price, stock, image_filename
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
    global product_variant_lookup
    product_variant_lookup = {}
    for barcode, variants in products.items():
        for index, variant in enumerate(variants):
            base_entry = {
                "sku": barcode,
                "base_barcode": barcode,
                "variant_index": index,
                "promo_code": None,
                "price": variant['price'],
                "name": variant['name'],
                "inventory_usage": 1,
                "image_filename": variant.get('image_filename', '')
            }
            # Only set the base barcode entry once to preserve the primary lookup
            product_variant_lookup.setdefault(barcode, base_entry)
            promos = variant.get('promos', {}) or {}
            for promo_code, promo_price in promos.items():
                promo_sku = f"{barcode}_{promo_code}"
                inventory_usage = promo_inventory_map.get(promo_code, 1)
                if promo_code not in promo_inventory_map:
                    print(f"Warning: promo code '{promo_code}' is missing from '{PROMO_INVENTORY_FILE}'. Defaulting inventory usage to 1.")
                promo_price_value = promo_price if promo_price is not None else variant['price']
                product_variant_lookup[promo_sku] = {
                    "sku": promo_sku,
                    "base_barcode": barcode,
                    "variant_index": index,
                    "promo_code": promo_code,
                    "price": promo_price_value,
                    "name": variant['name'],
                    "inventory_usage": inventory_usage,
                    "image_filename": variant.get('image_filename', '')
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
        sku = bundle.get("sku") or f"BUNDLE_{bundle_code}"
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
            "display_components": display_components
        }
def save_products_to_csv(parent=None):
    """
    Saves the current product data (including updated stock and image filename) to the CSV file.
    """
    conn = get_db_connection(parent)
    if not conn:
        return
    try:
        supports_promo_prices = ensure_promo_price_column(conn)
        with conn.cursor() as cursor:
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
                    if product_id:
                        cursor.execute(
                            update_query,
                            (name, price, stock, image_filename, product_id),
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
def save_receipts_archive():
    """Receipts are persisted in MySQL; no file save required."""
    return True
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
    try:
        with conn.cursor(dictionary=True) as cursor:
            cursor.execute(
                """
                SELECT p.stock_no, SUM(si.quantity) AS qty_sold, SUM(si.total_price) AS revenue
                  FROM sales_items si
                  JOIN products p ON si.product_id = p.product_id
                 WHERE si.is_freebie = FALSE
              GROUP BY p.stock_no
                """
            )
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
        layout = QVBoxLayout()
        self.setLayout(layout)
        self.text_edit = QTextEdit()
        self.text_edit.setReadOnly(True)
        layout_info = compute_receipt_layout()
        preview_font = QFont(get_receipt_font_name())
        preview_font.setPointSizeF(layout_info["font_size"])
        preview_font.setBold(True)
        self.text_edit.setFont(preview_font)
        self.text_edit.setText(receipt_text_content)
        layout.addWidget(self.text_edit)
        btn_layout = QHBoxLayout()
        layout.addLayout(btn_layout)
        btn_print = QPushButton("Print Receipt")
        btn_print.setStyleSheet("background-color: #007BFF; color: white; font-weight: bold;")
        btn_print.clicked.connect(lambda: print_receipt_pdf(receipt_text_content, self))
        btn_layout.addWidget(btn_print)
        btn_save_pdf = QPushButton("Save as PDF")
        btn_save_pdf.setStyleSheet("background-color: #28A745; color: white; font-weight: bold;")
        btn_save_pdf.clicked.connect(lambda: self.save_receipt_as_pdf(receipt_text_content))
        btn_layout.addWidget(btn_save_pdf)
        btn_close = QPushButton("Close")
        btn_close.clicked.connect(self.accept)
        btn_layout.addWidget(btn_close)
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
        self.inventory_table = QTableWidget(0, 3, card)
        self.inventory_table.setHorizontalHeaderLabels(["Stock No.", "Product Name", "Stock Left"])
        self.inventory_table.horizontalHeader().setStretchLastSection(True)
        self.inventory_table.setAlternatingRowColors(True)
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
        btn_sync_api = QPushButton("Sync via API", self)
        btn_sync_api.clicked.connect(self.sync_inventory_from_api)
        button_grid.addWidget(btn_sync_api, 1, 0)
        btn_post_sales = QPushButton("Post Sales Invoice", self)
        btn_post_sales.clicked.connect(self.post_sales_invoice)
        button_grid.addWidget(btn_post_sales, 1, 1, 1, 2)
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
        self.bundle_table.horizontalHeader().setStretchLastSection(True)
        self.bundle_table.setAlternatingRowColors(True)
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
        self.promos_table.horizontalHeader().setStretchLastSection(True)
        self.promos_table.setAlternatingRowColors(True)
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
        self.basket_table.horizontalHeader().setStretchLastSection(True)
        self.basket_table.setAlternatingRowColors(True)
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
                save_products_to_csv(self)  # Save updated products to CSV
                self.populate_table()  # Refresh the table
                show_info("Replenish Successful", f"Stocks replenished for {replenished_count} products.", self)
            except Exception as e:
                show_error("Replenish Error", f"Failed to replenish stock from Excel file: {e}", self)
    def populate_table(self):
        if not hasattr(self, "inventory_table"):
            return
        self.inventory_table.setRowCount(0)  # Clear existing rows
        # Sort products by name
        sorted_products = sorted(self.products.items(), key=lambda item: item[1][0]["name"].lower())
        for barcode, variants in sorted_products:
            for variant in variants:
                row = self.inventory_table.rowCount()
                self.inventory_table.insertRow(row)
                self.inventory_table.setItem(row, 0, QTableWidgetItem(barcode))
                self.inventory_table.setItem(row, 1, QTableWidgetItem(variant["name"]))
                self.inventory_table.setItem(row, 2, QTableWidgetItem(str(variant["stock"])))
    def populate_bundle_table(self):
        if not hasattr(self, "bundle_table"):
            return
        if not load_bundle_promos(self):
            return
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
                save_products_to_csv(self)
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
                save_products_to_csv(self)  # Save updated products to CSV
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
        save_products_to_csv(self)
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
    def post_sales_invoice(self):
        global sales_summary, total_cash_tendered, total_gcash_tendered
        if not ensure_api_settings_loaded(self):
            return
        if not sales_summary:
            show_info("Sales Invoice", "No sales data available to post.", self)
            return
        items = []
        for sku, data in sales_summary.items():
            qty = int(data.get("qty_sold") or 0)
            if qty <= 0:
                continue
            revenue = float(data.get("revenue") or 0.0)
            unit_price = revenue / qty if qty and api_settings.get("include_unit_price") else None
            variant_name = sku
            variants = self.products.get(sku)
            if variants:
                variant_name = variants[0].get("name", sku)
            item_entry = {
                "sku": sku,
                "quantity": qty,
                "unitPrice": round(unit_price, 2) if unit_price is not None else None,
                "remarks": variant_name,
            }
            items.append(item_entry)
        if not items:
            show_info("Sales Invoice", "No qualifying sales items found to post.", self)
            return
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
            body = load_sales_invoice_stub_response(parent=self)
            if body is None:
                show_error("Sales Invoice Error", "Sales stub response could not be loaded.", self)
                return
        else:
            response = api_request("POST", "sales-invoices", parent=self, json_payload=payload)
            if response is None:
                return
            if response.status_code not in (200, 201):
                try:
                    error_body = response.json()
                except ValueError:
                    error_body = response.text
                show_error("Sales Invoice Error", f"API returned {response.status_code}:\n{error_body}", self)
                return
            try:
                body = response.json()
            except ValueError:
                body = {}
            if not isinstance(body, dict):
                body = {}
            if body.get("code") not in (200, 201):
                message = body.get("message") or body.get("error") or response.text
                show_error("Sales Invoice Error", f"API responded with code {body.get('code')}:\n{message}", self)
                return
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
        ref_no = data.get("ref_no") or data.get("id")
        amount_due = data.get("amount_due")
        message_lines = ["Sales invoice created successfully."]
        if ref_no:
            message_lines.append(f"Reference: {ref_no}")
        if amount_due is not None:
            message_lines.append(f"Amount Due: {amount_due}")
        show_info("Sales Invoice Posted", "\n".join(message_lines), self)
        if using_stub:
            show_info(
                "Stub Data Used",
                "Sales invoice request used stub response. Disable 'use_sales_stub' in api_settings.json to call the live API.",
                self,
            )
        if api_settings.get("clear_sales_summary_after_post"):
            sales_summary = {}
            total_cash_tendered = 0.0
            total_gcash_tendered = 0.0
            save_sales_summary()
            parent = self.parent()
            if parent and hasattr(parent, "sales_summary"):
                parent.sales_summary = sales_summary
    def export_summary(self):
        file_path, _ = QFileDialog.getSaveFileName(self, "Export Summary as Excel", "", "Excel Files (*.xlsx *.xls)")
        if file_path:
            try:
                rows = []
                for barcode, variants in self.products.items():
                    for variant in variants:
                        starting_stock = variant.get('original_stock', variant.get('stock', 0))  # Use original stock
                        sold = sales_summary.get(barcode, {}).get('qty_sold', 0)
                        expected_stock = starting_stock - sold
                        row_data = {
                            "Parent": "",
                            "Category": "",
                            "Stock No": barcode,
                            "Name": variant['name'],
                            "[Z95] - Exibition Warehouse": starting_stock,
                            "Sold": sold,
                            "Expected Stocks": expected_stock,
                            "Available Stocks": variant['stock']
                        }
                        rows.append(row_data)
                columns = ["Parent", "Category", "Stock No", "Name", "[Z95] - Exibition Warehouse", "Sold", "Expected Stocks", "Available Stocks"]
                df = pd.DataFrame(rows, columns=columns)
                df.to_excel(file_path, index=False)
                show_info("Export Successful", "Inventory summary has been exported successfully.", self)
            except Exception as e:
                show_error("Export Error", f"Failed to export summary: {e}", self)
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
        self.load_promo_data(self.promo_code_combo.currentText())
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
        save_products_to_csv(self)
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
        self.btn_select_bundle_image = QPushButton("Choose Imageâ€¦")
        self.btn_select_bundle_image.clicked.connect(self.choose_bundle_image)
        controls_col.addWidget(self.btn_select_bundle_image)
        image_row.addLayout(controls_col)
        header_layout.addLayout(image_row, 3, 0, 1, 4)
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
        self.load_bundle_data(self.bundle_code_combo.currentText())
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
        sku = f"BUNDLE_{bundle_code}"
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
        self.variant_combo = QComboBox()
        add_layout.addWidget(self.variant_combo, stretch=1)
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
        self.populate_tier_combo()
        self.tier_combo.currentIndexChanged.connect(self.handle_tier_selected)
        if self.tier_combo.count() > 0:
            self.handle_tier_selected(self.tier_combo.currentIndex())
        else:
            self.clear_form()
    def populate_variant_options(self):
        self.variant_combo.clear()
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
                self.variant_combo.addItem(label, option)
        if self.variant_options:
            self.variant_combo.setCurrentIndex(0)
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
class POSMainWindow(QMainWindow):
    def __init__(self, username, parent=None):
        super().__init__(parent)
        self.current_user_name = username
        self.setWindowTitle(f"POS System - Logged in as: {username}")
        self.central_widget = QWidget()
        self.setCentralWidget(self.central_widget)
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
        self.init_ui()
        self.initialize_customer_queue()
        self.init_barcode_scanner()
        self.showMaximized()
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
        self.customer_tabs.tabCloseRequested.connect(self.close_customer_session)
        self.customer_tabs.currentChanged.connect(self.on_customer_tab_changed)
        queue_layout.addWidget(self.customer_tabs, stretch=1)
        self.btn_add_customer = QPushButton("Add Customer")
        self.btn_add_customer.setFont(QFont("Arial", 12, QFont.Weight.Bold))
        self.btn_add_customer.setStyleSheet("padding: 6px 12px;")
        self.btn_add_customer.clicked.connect(lambda: self.add_customer_session())
        queue_layout.addWidget(self.btn_add_customer)
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
        info_group.setMaximumWidth(600)  # Adjust as needed to reduce width
        info_group.setFixedHeight(600)
        info_group.setStyleSheet("QGroupBox { border: 1px solid #CCC; border-radius: 8px; background-color: white; }") # Added styling
        info_layout = QVBoxLayout()
        info_group.setLayout(info_layout) # Set layout for the group box
        self.info_group = info_group
        # Product Image Section
        lbl_image_title = QLabel("PRODUCT INFORMATION")
        lbl_image_title.setAlignment(Qt.AlignmentFlag.AlignCenter)
        lbl_image_title.setFont(QFont("Arial", 20, QFont.Weight.Bold))
        info_layout.addWidget(lbl_image_title, alignment=Qt.AlignmentFlag.AlignCenter) # Added directly to info_layout
        self.default_pixmap = QPixmap(550, 250)
        self.default_pixmap.fill(QColor("#D9D9D9")) # Changed to a light grey color as per the new image
        self.label_product_image = QLabel()
        self.label_product_image.setPixmap(self.default_pixmap)
        self.label_product_image.setFixedSize(550, 250)
        # Removed setFixedSize, using setScaledContents for responsiveness
        self.label_product_image.setScaledContents(True)
        self.label_product_image.setMinimumSize(200, 150) # Minimum size for the image area
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
        self.label_product_barcode_number = QLabel("STOCK NO.: ")
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
        for index, (text, slot) in enumerate(button_specs):
            btn = QPushButton(text)
            btn.setMinimumSize(160, fixed_button_height)
            btn.setFixedHeight(fixed_button_height)
            btn.setCursor(Qt.CursorShape.PointingHandCursor)
            btn.setObjectName(f"ActionButton_{text.replace(' ', '_')}")
            btn.clicked.connect(slot)
            row = index // 2
            col = index % 2
            buttons_grid_layout.addWidget(btn, row, col)
            self.action_buttons[text] = btn
        self.update_action_button_styles(self.current_effective_theme)
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
        # Setup signals to handle selection from completer
        self.setup_product_search_signals()
        # Add this in POSMainWindow.__init__ or __init_ui__ after creating self.listbox:    
        self.listbox.setSelectionMode(QListWidget.SelectionMode.SingleSelection)  # Only single item selection allowed
        self.listbox.currentRowChanged.connect(self.display_selected_cart_item)
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
    def initialize_customer_queue(self):
        if self.customer_tabs is None:
            return
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
        session = {"cart": []}
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
            self.customer_tabs.setTabText(idx, f"Customer {idx + 1}")
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
        name = item.get("name", "")
        qty = item.get("qty", 1)
        line_total = item.get("price", 0) * qty
        suffix = " (Bundle)" if item.get("bundle_components") else ""
        return f"{sku} - {name}{suffix} x{qty} - P{line_total:.2f}"
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
            self.label_product_barcode_number.setText(f"Stock No.: {sku}")
            self.display_product_image(variant.get('image_filename'), sku)
            self.set_display_context(base_barcode, variant_index, item.get('bundle_code'))
        else:
            self.clear_product_display()
    def void_selected_item(self):
        """
        Asks for admin password, then removes the selected item from cart if authorized.
        """
        selected_row = self.listbox.currentRow()
        if selected_row < 0:
            show_warning("Void Item", "Please select an item from the cart to void.", self)
            return
        # Ask for admin password
        password, ok = QInputDialog.getText(self, "Admin Authorization", "Enter admin password to void item:", QLineEdit.EchoMode.Password)
        if not ok:
            # User cancelled
            return
        if password != ADMIN_PASSWORD:
            show_error("Authorization Failed", "Incorrect admin password. You are not authorized to void items.", self)
            return
        # Remove the item from cart and listbox
        voided_item = self.cart.pop(selected_row)
        self.listbox.takeItem(selected_row)
        # Clear product display since item was removed
        self.clear_product_display()
        # Update total
        self.update_total()
        show_info("Item Voided", f"'{voided_item['name']}' has been removed from the cart.", self)
    def setup_product_search_combobox(self):
        # Initial setup for the combobox to be editable with styling and completer
        self.entry_product_search.setEditable(True)
        self.entry_product_search.setFixedWidth(1200)
        self.entry_product_search.setFont(QFont("Segoe UI", 20))
        self.entry_product_search.lineEdit().setAlignment(Qt.AlignmentFlag.AlignLeft)
        self.apply_combobox_style(self.current_effective_theme)
        # Store full product list as display strings: "Product Name (barcode)"
        self._product_search_list = [
            f"{data['name']} ({sku})" for sku, data in product_variant_lookup.items()
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
    def filter_product_search_list(self, text):
        # Filter underlying model of completer based on typed text to update dropdown options.
        text_lower = text.lower().strip()
        if not text_lower:
            # Show no completions when empty to avoid list show
            self._completer_model.setStringList([])
            return
        filtered = []
        for sku, data in product_variant_lookup.items():
            display_text = f"{data['name']} ({sku})"
            if text_lower in data['name'].lower() or text_lower in sku.lower():
                filtered.append(display_text)
        self._completer_model.setStringList(filtered)
    def setup_product_search_signals(self):
        self._completer.activated.connect(self.on_product_search_selected)
    def refresh_product_search_options(self):
        if not hasattr(self, "_completer_model"):
            return
        self._product_search_list = [
            f"{data['name']} ({sku})" for sku, data in product_variant_lookup.items()
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
        """Apply neutral, theme-aware styling to the primary action buttons."""
        if not hasattr(self, "action_buttons") or not self.action_buttons:
            return
        tokens = get_theme_tokens(theme)
        if theme == "dark":
            base = "#1f2937"
            hover = "#334155"
            pressed = "#475569"
            text_color = tokens["title"]
            border = "#3e4c5e"
        else:
            base = "#e8f0ff"
            hover = "#dbe7ff"
            pressed = "#cbdfff"
            text_color = tokens["title"]
            border = "#b8cfff"
        disabled_bg = hover if theme == "dark" else "#e1e7f8"
        disabled_text = tokens["muted"]
        disabled_border = border
        for button in self.action_buttons.values():
            button.setStyleSheet(f"""
                QPushButton {{
                    background-color: {base};
                    color: {text_color};
                    border-radius: 12px;
                    padding: 14px 18px;
                    font-size: 22px;
                    font-weight: 600;
                    border: 1px solid {border};
                }}
                QPushButton:hover {{
                    background-color: {hover};
                }}
                QPushButton:pressed {{
                    background-color: {pressed};
                }}
                QPushButton:disabled {{
                    background-color: {disabled_bg};
                    color: {disabled_text};
                    border: 1px solid {disabled_border};
                }}
            """)
    def remove_existing_freebies_from_cart(self):
        """Remove any previously added freebies from the cart and UI list."""
        if not self.cart:
            return
        indices_to_remove = [idx for idx, item in enumerate(self.cart) if item.get("is_freebie")]
        if not indices_to_remove:
            return
        for offset, idx in enumerate(indices_to_remove):
            adjusted_index = idx - offset
            self.cart.pop(adjusted_index)
            if 0 <= adjusted_index < self.listbox.count():
                self.listbox.takeItem(adjusted_index)
        self.update_total()
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
            "base_stock_no": barcode,
            "variant_index": variant_index,
            "inventory_usage": 1,
            "promo_code": promo_code,
            "original_unit_price": 0.0,
            "is_freebie": True
        }
        self.cart.append(item)
        self.listbox.addItem(f"{barcode} - {item['name']} x{quantity} - FREE")
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
    def on_product_search_selected(self, selected_text):
        # Parse barcode from selected_text, update product info display and barcode entry
        start_idx = selected_text.rfind('(')
        end_idx = selected_text.rfind(')')
        if start_idx != -1 and end_idx != -1:
            sku = selected_text[start_idx + 1:end_idx]
            if not self.add_item_to_cart_by_sku(sku, show_not_found=False):
                show_warning("Product Not Found", f"Product with SKU '{sku}' not found in database.", self)
                self.clear_product_display()
            else:
                self.entry_product_search.setEditText("")
        else:
            show_warning("Format Error", "Invalid product selection format.", self)
            self.clear_product_display()
    def clear_product_display(self):
        self.label_product_name_display.setText("PRODUCT NAME: ")
        self.label_product_price_display.setText("PRICE: ")
        self.label_product_stock_display.setText("STOCK: ")
        self.label_product_barcode_number.setText("STOCK NO.: ")
        self.label_product_image.setPixmap(self.default_pixmap)
        self.set_display_context()
    def display_product_image(self, image_filename, stock_no=None):
        if stock_no is None:
            stock_no = getattr(self, "current_display_barcode", None)
        resolved_filename = resolve_product_image_filename(stock_no, image_filename)
        if resolved_filename:
            image_path = os.path.join(PRODUCT_IMAGE_FOLDER, resolved_filename)
            if os.path.exists(image_path):
                try:
                    pil_image = Image.open(image_path)
                    # Resize image to fit label size, maintaining aspect ratio
                    label_size = self.label_product_image.size()
                    pil_image = pil_image.convert("RGBA")
                    pil_image = pil_image.resize((label_size.width(), label_size.height()), Image.Resampling.LANCZOS)
                    qt_image = ImageQt.ImageQt(pil_image)
                    pixmap = QPixmap.fromImage(qt_image)
                    # Scale pixmap to fit label size with aspect ratio and smooth transformation
                    scaled_pixmap = pixmap.scaled(label_size, Qt.AspectRatioMode.KeepAspectRatio, Qt.TransformationMode.SmoothTransformation)
                    self.label_product_image.setPixmap(scaled_pixmap)
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
        save_products_to_csv(self)
        rebuild_product_variant_lookup()
        self.display_product_image(new_filename, self.current_display_barcode)
        self.set_display_context(self.current_display_barcode, variant_index, None)
        show_info("Image Updated", "Product image has been updated.", self)
    def add_item_to_cart_by_sku(self, sku, show_not_found=True):
        global current_item_count, current_discount
        lookup = product_variant_lookup.get(sku)
        if lookup is None:
            if show_not_found:
                show_warning("Not Found", f"Barcode '{sku}' not found in product database.", self)
                self.display_product_image(None, sku)
            return False
        qty = current_item_count
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
                return False
            item = {
                "name": lookup['name'],
                "price": price,
                "qty": qty,
                "Stock No.": lookup['sku'],
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
            current_item_count = 1
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
            "base_stock_no": base_barcode,
            "variant_index": variant_index,
            "inventory_usage": lookup.get('inventory_usage', 1),
            "promo_code": lookup.get('promo_code'),
            "original_unit_price": lookup['price'],
            "image_filename": variant.get('image_filename'),
        }
        self.cart.append(item)
        self.listbox.addItem(self.format_cart_item_label(item))
        self.label_product_name_display.setText(f"Name: {item['name']}")
        self.label_product_price_display.setText(f"Price: P{lookup['price']:.2f}")
        self.label_product_stock_display.setText(f"Stock: {variant['stock']}")
        self.label_product_barcode_number.setText(f"Stock No.: {lookup['sku']}")
        self.display_product_image(variant.get('image_filename'), lookup.get('sku'))
        self.set_display_context(base_barcode, variant_index, None)
        current_item_count = 1
        current_discount = 0.0
        self.update_total()
        return True
    def process_scanned_code(self, barcode_input):
        global current_item_count, current_discount
        barcode_input = (barcode_input or "").strip()
        if not barcode_input:
            return
        self.entry_product_search.setEditText("")
        # Clear previous product info display
        self.clear_product_display()
        added = self.add_item_to_cart_by_sku(barcode_input)
        if not added:
            self.display_product_image(None, barcode_input)
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
    def checkout(self):
        global current_sales_number, current_transaction_number, receipts_archive
        global total_cash_tendered, total_gcash_tendered
        if not self.cart:
            show_info("Info", "Cart is empty. Please add items before checking out.", self)
            return
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
            return
        cash_amount = 0.0
        gcash_amount = 0.0
        total_paid = 0.0
        if payment_method == "cash only":
            cash_amount_input, ok = QInputDialog.getDouble(self, "Cash Payment", f"Total due: P{total:,.2f}\nEnter cash amount:", min=total)
            if not ok:
                return
            cash_amount = cash_amount_input
            total_paid = cash_amount
            if total_paid < total:
                show_error("Payment Error", "Insufficient cash payment. Please pay the full amount.", self)
                return
        elif payment_method == "gcash only":
            gcash_amount_input, ok = QInputDialog.getDouble(self, "GCash Payment", f"Total due: P{total:,.2f}\nEnter GCash amount:", min=total)
            if not ok:
                return
            gcash_amount = gcash_amount_input
            total_paid = gcash_amount
            if total_paid < total:
                show_error("Payment Error", "Insufficient GCash payment. Please pay the full amount.", self)
                return
        elif payment_method == "cash and gcash":
            cash_amount_input, ok = QInputDialog.getDouble(self, "Cash Payment", f"Total due: P{total:,.2f}\nEnter cash amount (0 for no cash):", min=0)
            if not ok:
                return
            cash_amount = cash_amount_input
            gcash_amount_input, ok = QInputDialog.getDouble(self, "GCash Payment", f"Total due: P{total:,.2f}\nEnter GCash amount (0 for no GCash):", min=0)
            if not ok:
                return
            gcash_amount = gcash_amount_input
            total_paid = cash_amount + gcash_amount
            if total_paid < total:
                show_error("Payment Error", f"Insufficient combined payment. Total paid: P{total_paid:,.2f}\nRemaining due: P{total - total_paid:,.2f}", self)
                return
        change = total_paid - total
        self.apply_basket_freebies_to_cart(subtotal_for_promos)
        # Find the highest existing sales number and transaction number in receipts_archive
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
        # Calculate the next available sales number and transaction number
        next_sales_number = highest_sales_number + 1
        next_transaction_number = highest_transaction_number + 1
        # Generate the unique sales transaction label
        current_date = datetime.now().strftime("%Y-%m-%d")
        current_time = datetime.now().strftime("%H:%M:%S")
        sales_trans_label = f"SALES#: {next_sales_number:06d}   TRANS#: {next_transaction_number:06d}"
        sales_trans_line = f"{sales_trans_label}   {current_date}"
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
        receipt_text_content += f"{'Booth #: A003-A006':^{width}}\n"
        receipt_text_content += f"{'SUNNYWARE PHILIPPINES':^{width}}\n"
        receipt_text_content += f"{'Metro Manila, Philippines':^{width}}\n"
        receipt_text_content += f"{'---SALES ORDER SLIP---':^{width}}\n"
        receipt_text_content += f"{sales_trans_line:^{width}}\n\n"
        for item in self.cart:
            name = item['name']
            qty = item.get('qty', 1)
            price = item['price']
            line_total_val = price * qty
            line_total = f"P{line_total_val:,.2f}"
            unit_price = f"P{price:,.2f}"
            promo_suffix = item.get('promo_code')
            full_name = name.replace("\n", " ")
            append_columns(full_name)
            if promo_suffix:
                label = promo_suffix if qty == 1 else f"{qty} x {promo_suffix}"
                append_columns(f"{label} @ {unit_price}", line_total)
            else:
                append_columns(f"{qty} @ {unit_price}", line_total)
            if item.get('bundle_components'):
                for component in item['bundle_components']:
                    component_name = component.get("name") or component.get("barcode")
                    component_qty = component.get("quantity", 1)
                    append_columns(f"  - {component_qty} x {component_name}")
            receipt_text_content += "\n"
        receipt_text_content += "-" * width + "\n"
        append_columns("Total Amount Due:", f"P{total:,.2f}")
        if payment_method == "cash and gcash":
            append_columns("Cash:", f"P{cash_amount:,.2f}")
            append_columns("GCash:", f"P{gcash_amount:,.2f}")
            total_gcash_tendered += gcash_amount
            total_cash_tendered += cash_amount
        elif payment_method == "cash only":
            append_columns("Cash:", f"P{cash_amount:,.2f}")
            total_cash_tendered += cash_amount
        elif payment_method == "gcash only":
            append_columns("GCash:", f"P{gcash_amount:,.2f}")
            total_gcash_tendered += gcash_amount
        append_columns("Change:", f"P{change:,.2f}")
        append_columns(f"Payment Method: {payment_method.title()}")
        receipt_text_content += "-" * width + "\n"
        receipt_text_content += f"{current_time:^{width}}\n"
        receipt_text_content += f"{'Cashier: ' + self.current_user_name:^{width}}\n"
        receipt_text_content += f"{'SUNNYWARE PHILIPPINES':^{width}}\n"
        freebie_messages = [msg for msg in self.applied_freebie_messages if msg]
        closing_messages = freebie_messages if freebie_messages else ["THANK YOU SO MUCH!"]
        for message in closing_messages:
            wrapped_lines = textwrap.wrap(message, width) or [""]
            for line in wrapped_lines:
                receipt_text_content += f"{line:^{width}}\n"
        # Store the receipt in archive
        receipts_archive[sales_trans_label] = receipt_text_content
        # Show receipt window
        receipt_dialog = ReceiptDialog(receipt_text_content, self)
        receipt_dialog.exec()
        # Update stock & sales summary after transaction
        for item in self.cart:
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
                        "deduction_units": deduction_units,
                        "base_value": base_value
                    })
                for info in component_infos:
                    barcode = info["barcode"]
                    if barcode not in sales_summary:
                        sales_summary[barcode] = {"qty_sold": 0, "revenue": 0.0}
                    sales_summary[barcode]["qty_sold"] += info["deduction_units"]
                    if total_base_value > 0:
                        share = info["base_value"] / total_base_value
                    else:
                        share = 1 / len(component_infos) if component_infos else 0
                    sales_summary[barcode]["revenue"] += item['price'] * bundle_qty * share
                continue
            sku = item.get('Stock No.')
            base_barcode = item.get('base_stock_no', sku)
            qty = item.get('qty', 1)
            inventory_usage = item.get('inventory_usage', 1)
            variant_index = item.get('variant_index', 0)
            deduction_units = qty * inventory_usage
            if isinstance(deduction_units, float) and deduction_units.is_integer():
                deduction_units = int(deduction_units)
            variants = products.get(base_barcode, [])
            if variants:
                target_variant = variants[variant_index] if variant_index < len(variants) else variants[0]
                target_variant["stock"] -= deduction_units
            else:
                print(f"Warning: Unable to update inventory. Base product '{base_barcode}' not found.")
                continue
            if base_barcode not in sales_summary:
                sales_summary[base_barcode] = {"qty_sold": 0, "revenue": 0.0}
            sales_summary[base_barcode]["qty_sold"] += deduction_units
            sales_summary[base_barcode]["revenue"] += item['price'] * qty
        # Save updated products to CSV
        save_products_to_csv(self)
        # Increment transaction numbers AFTER generating the label and receipt
        current_sales_number = next_sales_number
        current_transaction_number = next_transaction_number
        # Save data after checkout
        save_sales_summary()
        save_receipts_archive()
        save_inventory_summary()
        # Clear cart and UI
        self.cart.clear()
        self.listbox.clear()
        self.update_total()
        self.clear_product_display()
        self.handle_session_after_checkout()
    def set_discount(self):
        disc, ok = QInputDialog.getDouble(self, "Apply Discount", "Enter discount percentage (0-100):", min=0, max=100)
        if ok:
            global current_discount
            current_discount = disc
            show_info("Discount Set", f"Discount for next item set to {current_discount:.2f}%", self)
    def set_item_count(self):
        count, ok = QInputDialog.getInt(self, "Set Item Quantity", "Enter item quantity (1 or more):", min=1)
        if ok:
            global current_item_count
            current_item_count = count
            show_info("Item Quantity Set", f"Quantity for next item set to {current_item_count}", self)
    def inventory_management(self):
        dlg = InventoryManagementDialog(products, self)  # Pass the global products dictionary
        dlg.exec()
        # Refresh product search and product display after stock changes
        self.clear_product_display()
        rebuild_product_variant_lookup()
        self.refresh_product_search_options()
        save_inventory_summary()
        save_products_to_csv(self)
    def summary_view(self):
        dlg = SalesSummaryDialog(self)
        dlg.exec()
    def show_archive_labels(self):
        dlg = ArchiveDialog(self)
        dlg.exec()
class SalesSummaryDialog(QDialog):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setWindowTitle("Sales Summary")
        self.resize(1024, 620)
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
        self.table.setColumnCount(5)
        self.table.setHorizontalHeaderLabels(["STOCK #", "Product Name", "Quantity Sold", "Unit Price", "Total Revenue"])
        self.table.horizontalHeader().setDefaultAlignment(Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter)
        self.table.horizontalHeader().setStretchLastSection(True)
        self.table.horizontalHeader().setSectionResizeMode(QHeaderView.ResizeMode.Stretch)
        self.table.horizontalHeader().setHighlightSections(False)
        self.table.verticalHeader().setVisible(False)
        self.table.verticalHeader().setSectionResizeMode(QHeaderView.ResizeMode.Fixed)
        self.table.verticalHeader().setDefaultSectionSize(48)
        self.table.setSelectionBehavior(QTableWidget.SelectionBehavior.SelectRows)
        self.table.setAlternatingRowColors(True)
        self.table.setSortingEnabled(True)
        self.table.setEditTriggers(QTableWidget.EditTrigger.NoEditTriggers)
        self.table.setShowGrid(False)
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
        self.export_excel_button = QPushButton("Export to Excel")
        self.export_excel_button.setObjectName("SummaryAction")
        self.export_excel_button.setCursor(Qt.CursorShape.PointingHandCursor)
        self.export_excel_button.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Fixed)
        self.export_pdf_button = QPushButton("Export to PDF")
        self.export_pdf_button.setObjectName("SummaryAction")
        self.export_pdf_button.setCursor(Qt.CursorShape.PointingHandCursor)
        self.export_pdf_button.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Fixed)
        side_layout.addWidget(self.export_excel_button)
        side_layout.addWidget(self.export_pdf_button)
        content_row.addWidget(side_panel, 1)
        main_layout.addWidget(content_card)
        self.export_excel_button.clicked.connect(self.export_to_excel)
        self.export_pdf_button.clicked.connect(self.export_to_pdf)
        self.populate_sales_summary()
        self.update_metrics()
        self.apply_theme_styles()
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
            metric_bg = self._mix_color(tokens["card_bg"], "#ffffff", 0.12)
            metric_border = self._mix_color(metric_bg, "#000000", 0.45)
            button_bg = self._mix_color(tokens["card_bg"], "#ffffff", 0.05)
            button_hover = self._mix_color(button_bg, "#ffffff", 0.12)
            button_pressed = self._mix_color(button_bg, "#000000", 0.25)
            button_text = tokens["title"]
            button_border = self._mix_color(button_bg, "#000000", 0.35)
            table_border = self._mix_color(table_bg, "#000000", 0.35)
            header_bg = self._mix_color(tokens["card_bg"], "#000000", 0.35)
            header_text = tokens["title"]
            alt_row = self._mix_color(table_bg, "#ffffff", 0.08)
        else:
            table_bg = self._mix_color(tokens["card_bg"], "#000000", 0.05)
            side_panel_bg = self._mix_color(tokens["card_bg"], "#000000", 0.02)
            metric_bg = self._mix_color(tokens["card_bg"], "#ffffff", 0.7)
            metric_border = self._mix_color(metric_bg, "#000000", 0.12)
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
                border: 1px solid {metric_border};
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
    def populate_sales_summary(self):
        products = self.parent().products
        self.table.setRowCount(len(products))
        row = 0
        for barcode, variants in products.items():
            product_name = variants[0]['name']
            sales_data = self.parent().sales_summary.get(barcode, {"qty_sold": 0, "revenue": 0.0})
            quantity_sold = sales_data['qty_sold']
            total_revenue = sales_data['revenue']
            price_per_item = total_revenue / quantity_sold if quantity_sold > 0 else 0.0
            total_price = price_per_item * quantity_sold
            self.table.setItem(row, 0, QTableWidgetItem(barcode))
            self.table.setItem(row, 1, QTableWidgetItem(product_name))
            self.table.setItem(row, 2, QTableWidgetItem(f"{quantity_sold:,}"))
            self.table.setItem(row, 3, QTableWidgetItem(f"P{price_per_item:,.2f}"))
            self.table.setItem(row, 4, QTableWidgetItem(f"P{total_price:,.2f}"))
            row += 1
    def update_metrics(self):
        sales_data = self.parent().sales_summary
        total_quantity_sold = sum(data['qty_sold'] for data in sales_data.values())
        total_revenue = sum(data['revenue'] for data in sales_data.values())
        global total_cash_tendered, total_gcash_tendered
        best_code = None
        best_qty = 0
        for barcode, data in sales_data.items():
            if data['qty_sold'] > best_qty:
                best_qty = data['qty_sold']
                best_code = barcode
        top_label = "No sales recorded yet"
        if best_code and best_code in self.parent().products:
            product_name = self.parent().products[best_code][0]['name']
            top_label = f"{product_name}\n{best_qty:,} sold"
        self.metric_labels["items"].setText(f"{total_quantity_sold:,}")
        self.metric_labels["revenue"].setText(f"P{total_revenue:,.2f}")
        self.metric_labels["cash"].setText(f"P{total_cash_tendered:,.2f}")
        self.metric_labels["gcash"].setText(f"P{total_gcash_tendered:,.2f}")
        self.metric_labels["top"].setText(top_label)
    def export_to_excel(self):
        global sales_summary, total_cash_tendered, total_gcash_tendered
        products = self.parent().products
        sales_data = self.parent().sales_summary
        if not products:
            QMessageBox.information(self, "No Data", "No product data to export.")
            return
        file_path, _ = QFileDialog.getSaveFileName(self, "Export Sales Summary to Excel", "", "Excel Files (*.xlsx *.xls)")
        if not file_path:
            return
        if not (file_path.lower().endswith('.xlsx') or file_path.lower().endswith('.xls')):
            file_path += '.xlsx'
        try:
            rows = []
            for barcode, variants in products.items():
                product_name = variants[0]['name']
                data_item = sales_data.get(barcode, {"qty_sold": 0, "revenue": 0.0})
                qty_sold = data_item['qty_sold']
                revenue = data_item['revenue']
                price_per_item = revenue / qty_sold if qty_sold > 0 else 0.0
                total_price = price_per_item * qty_sold
                rows.append({
                    "STOCK #": barcode,
                    "Product Name": product_name,
                    "Quantity Sold": qty_sold,
                    "Price": price_per_item,
                    "Total Revenue": total_price
                })
            df = pd.DataFrame(rows, columns=["STOCK #", "Product Name", "Quantity Sold", "Price", "Total Revenue"])
            total_qty = df["Quantity Sold"].sum()
            total_revenue = df["Total Revenue"].sum()
            totals_df = pd.DataFrame([{
                "STOCK #": "",
                "Product Name": "Totals",
                "Quantity Sold": total_qty,
                "Price": "",
                "Total Revenue": total_revenue
            }])
            df = pd.concat([df, totals_df], ignore_index=True)
            with pd.ExcelWriter(file_path, engine='xlsxwriter') as writer:
                df.to_excel(writer, sheet_name='Sales Summary', index=False)
                workbook = writer.book
                worksheet = writer.sheets['Sales Summary']
                currency_format = workbook.add_format({'num_format': 'Php #,##0.00'})
                worksheet.set_column('D:D', 18, currency_format)
                worksheet.set_column('E:E', 18, currency_format)
                bold_format = workbook.add_format({'bold': True})
                totals_row = len(df) - 1
                worksheet.set_row(totals_row, None, bold_format)
                row_after = len(df) + 1
                worksheet.write(row_after, 0, "Cash:")
                worksheet.write(row_after, 1, total_cash_tendered, currency_format)
                worksheet.write(row_after + 1, 0, "GCash:")
                worksheet.write(row_after + 1, 1, total_gcash_tendered, currency_format)
            QMessageBox.information(self, "Export Successful", f"Sales summary has been exported to:\n{file_path}")
        except Exception as e:
            QMessageBox.critical(self, "Export Error", f"Failed to export sales summary to Excel:\n{e}")
        sales_summary = {}
        total_cash_tendered = 0.0
        total_gcash_tendered = 0.0
        save_sales_summary()
        self.populate_sales_summary()
        self.update_metrics()
    def export_to_pdf(self):
        sales_data = self.parent().sales_summary
        products = self.parent().products
        if not products:
            QMessageBox.information(self, "No Data", "No sales data to export.")
            return
        file_path, _ = QFileDialog.getSaveFileName(self, "Export Sales Summary to PDF", "", "PDF Files (*.pdf)")
        if not file_path:
            return
        if not file_path.lower().endswith('.pdf'):
            file_path += '.pdf'
        try:
            doc = SimpleDocTemplate(file_path, pagesize=A4,
                                    rightMargin=40, leftMargin=40,
                                    topMargin=60, bottomMargin=40)
            styles = getSampleStyleSheet()
            elements = []
            title_style = styles['Heading1']
            title_style.fontSize = 24
            title_style.leading = 30
            title_style.alignment = 1
            elements.append(Paragraph("Sales Summary Report", title_style))
            elements.append(Spacer(1, 24))
            data = [["STOCK #", "Product Name", "Quantity", "Price", "Revenue"]]
            max_qty = -1
            most_demanded_name = None
            total_quantity_sold = 0
            total_revenue = 0.0
            for barcode, variants in products.items():
                product_name = variants[0]['name']
                data_item = sales_data.get(barcode, {"qty_sold": 0, "revenue": 0.0})
                qty_sold = data_item['qty_sold']
                revenue = data_item['revenue']
                price_per_item = revenue / qty_sold if qty_sold > 0 else 0
                total_price = price_per_item * qty_sold
                data.append([
                    barcode,
                    product_name,
                    str(qty_sold),
                    f"P{price_per_item:,.2f}",
                    f"P{total_price:,.2f}"
                ])
                total_quantity_sold += qty_sold
                total_revenue += revenue
                if qty_sold > max_qty:
                    max_qty = qty_sold
                    most_demanded_name = product_name
            table_style = TableStyle([
                ('BACKGROUND', (0, 0), (-1, 0), colors.HexColor("#e5e7eb")),
                ('TEXTCOLOR', (0, 0), (-1, 0), colors.HexColor("#1f2937")),
                ('ALIGN', (2, 1), (-1, -1), 'RIGHT'),
                ('FONTNAME', (0, 0), (-1, 0), 'Helvetica-Bold'),
                ('FONTSIZE', (0, 0), (-1, 0), 14),
                ('BOTTOMPADDING', (0, 0), (-1, 0), 12),
                ('BACKGROUND', (0, 1), (-1, -1), colors.HexColor("#f8fafc")),
                ('GRID', (0, 0), (-1, -1), 1, colors.HexColor("#d1d5db")),
                ('ROWBACKGROUNDS', (0, 1), (-1, -1), [colors.white, colors.HexColor("#f3f4f6")])
            ])
            col_widths = [70, 180, 80, 80, 100]
            sales_table = Table(data, colWidths=col_widths)
            sales_table.setStyle(table_style)
            elements.append(sales_table)
            elements.append(Spacer(1, 24))
            normal_style = styles['Normal']
            normal_style.fontSize = 16
            normal_style.textColor = colors.HexColor("#6b7280")
            elements.append(Paragraph(f"<b>Total Items Sold:</b> {total_quantity_sold}", normal_style))
            elements.append(Paragraph(f"<b>Total Revenue:</b> P{total_revenue:,.2f}", normal_style))
            global total_cash_tendered, total_gcash_tendered
            elements.append(Paragraph(f"<b>Cash Tendered:</b> P{total_cash_tendered:,.2f}", normal_style))
            elements.append(Paragraph(f"<b>GCash Tendered:</b> P{total_gcash_tendered:,.2f}", normal_style))
            elements.append(Spacer(1, 24))
            heading2_style = styles['Heading2']
            heading2_style.textColor = colors.HexColor("#6b7280")
            heading2_style.fontSize = 20
            elements.append(Paragraph("Most In Demand Item", heading2_style))
            demand_style = styles['Normal']
            demand_style.fontSize = 16
            elements.append(Spacer(1, 6))
            if most_demanded_name:
                elements.append(Paragraph(f"{most_demanded_name} (Sold: {max_qty} units)", demand_style))
            else:
                elements.append(Paragraph("No sales data available", demand_style))
            doc.build(elements)
            QMessageBox.information(self, "Export Successful", f"Sales summary has been exported to:\n{file_path}")
        except Exception as e:
            QMessageBox.critical(self, "Export Error", f"Failed to export sales summary to PDF:\n{e}")
        sales_summary = {}
        total_cash_tendered = 0.0
        total_gcash_tendered = 0.0
        save_sales_summary()
        self.populate_sales_summary()
        self.update_metrics()
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
        layout = QVBoxLayout()
        self.setLayout(layout)
        self.text_edit = QTextEdit()
        self.text_edit.setReadOnly(True)
        layout_info = compute_receipt_layout()
        preview_font = QFont(get_receipt_font_name())
        preview_font.setPointSizeF(layout_info["font_size"])
        preview_font.setBold(True)
        self.text_edit.setFont(preview_font)
        self.text_edit.setText(receipt_text_content)
        layout.addWidget(self.text_edit)
        btn_layout = QHBoxLayout()
        layout.addLayout(btn_layout)
        btn_print = QPushButton("Print Receipt")
        btn_print.setStyleSheet("background-color: #007BFF; color: white; font-weight: bold;")
        btn_print.clicked.connect(lambda: print_receipt_pdf(receipt_text_content, self))
        btn_layout.addWidget(btn_print)
        btn_save_pdf = QPushButton("Save as PDF")
        btn_save_pdf.setStyleSheet("background-color: #28A745; color: white; font-weight: bold;")
        btn_save_pdf.clicked.connect(lambda: self.save_receipt_as_pdf(receipt_text_content))
        btn_layout.addWidget(btn_save_pdf)
        btn_close = QPushButton("Close")
        btn_close.clicked.connect(self.accept)
        btn_layout.addWidget(btn_close)
    def save_receipt_as_pdf(self, receipt_text_content):
        file_path, _ = QFileDialog.getSaveFileName(self, "Save Receipt as PDF", "", "PDF Files (*.pdf)")
        if file_path:
            if not file_path.lower().endswith('.pdf'):
                file_path += '.pdf'
            save_receipt_pdf(receipt_text_content, file_path)
            show_info("Save Successful", f"Receipt saved as PDF: {file_path}", self)
def _normalize_receipt_lines(receipt_text):
    # Convert receipt content (string, list, dict, etc.) into a flat list of printable strings.
    if receipt_text is None:
        return []
    if isinstance(receipt_text, str):
        return receipt_text.splitlines()
    if isinstance(receipt_text, dict):
        if "text" in receipt_text:
            text_value = receipt_text.get("text")
            if isinstance(text_value, (list, tuple, set)):
                lines = []
                for item in text_value:
                    lines.extend(_normalize_receipt_lines(item))
                return lines
            if text_value is None:
                return [""]
            return str(text_value).splitlines()
        if "lines" in receipt_text and isinstance(receipt_text["lines"], (list, tuple, set)):
            lines = []
            for item in receipt_text["lines"]:
                lines.extend(_normalize_receipt_lines(item))
            return lines
        return [json.dumps(receipt_text, ensure_ascii=False)]
    if isinstance(receipt_text, (list, tuple, set)):
        lines = []
        for item in receipt_text:
            lines.extend(_normalize_receipt_lines(item))
        return lines
    return str(receipt_text).splitlines()


def print_receipt_pdf(receipt_text, parent=None):
    layout = compute_receipt_layout()
    normalized_lines = _normalize_receipt_lines(receipt_text)
    try:
        formatted_receipt = "\n".join("" if line is None else str(line) for line in normalized_lines)
    except Exception:
        formatted_receipt = str(receipt_text)
    if sys.platform.startswith("win"):
        if win32print is None or win32ui is None or win32con is None:
            show_error(
                "Print Error",
                "Direct printing requires the 'pywin32' package (win32print/win32ui/win32con). Install it with 'pip install pywin32' and try again.",
                parent,
            )
            return
        printer_name = CUSTOM_RECEIPT_PRINTER_NAME.strip()
        if not printer_name:
            try:
                printer_name = win32print.GetDefaultPrinter()
            except win32print.error as exc:
                show_error("Print Error", f"Unable to determine default printer:\n{exc}", parent)
                return
        if not printer_name:
            show_error(
                "Print Error",
                "No printer selected. Set Windows default printer or update CUSTOM_RECEIPT_PRINTER_NAME.",
                parent,
            )
            return
        try:
            hdc = win32ui.CreateDC()
            hdc.CreatePrinterDC(printer_name)
        except win32print.error as exc:
            show_error("Print Error", f"Unable to access printer '{printer_name}':\n{exc}", parent)
            return
        except Exception as exc:
            show_error("Print Error", f"Failed to create printer context:\n{exc}", parent)
            return
        job_name = f"POS Receipt {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}"
        doc_started = False
        page_started = False
        try:
            hdc.StartDoc({"DocName": job_name})
            doc_started = True
            hdc.StartPage()
            page_started = True
            dpi_x = hdc.GetDeviceCaps(win32con.LOGPIXELSX)
            dpi_y = hdc.GetDeviceCaps(win32con.LOGPIXELSY)
            margin_left = int(RECEIPT_MARGIN_MM / 25.4 * dpi_x)
            top_margin = int(RECEIPT_TOP_MARGIN_MM / 25.4 * dpi_y)
            font_name = layout.get("font_name") or get_receipt_font_name()
            font_size_pt = layout.get("font_size", RECEIPT_BASE_FONT_SIZE)
            font_height = int(-dpi_y * font_size_pt / 72.0) or -12
            try:
                font = win32ui.CreateFont(
                    {
                        "name": font_name,
                        "height": font_height,
                        "weight": win32con.FW_NORMAL,
                        "charSet": win32con.ANSI_CHARSET,
                    }
                )
            except Exception:
                fallback_font = FALLBACK_RECEIPT_FONT_NAME
                font = win32ui.CreateFont(
                    {
                        "name": fallback_font,
                        "height": font_height,
                        "weight": win32con.FW_NORMAL,
                        "charSet": win32con.ANSI_CHARSET,
                    }
                )
            hdc.SelectObject(font)
            hdc.SetBkMode(win32con.TRANSPARENT)
            line_spacing = layout.get("line_spacing", 1.0)
            line_height = int(abs(font_height) * max(line_spacing, 1.0))
            if line_height <= 0:
                line_height = abs(font_height) or 12
            y_pos = top_margin
            for raw_line in normalized_lines:
                line_text = "" if raw_line is None else str(raw_line)
                line_text = line_text.rstrip()
                line_text = line_text.replace("\u2022", "*").replace("\u2013", "-").replace("\u2014", "-")
                hdc.TextOut(margin_left, y_pos, line_text)
                y_pos += line_height
            hdc.EndPage()
            page_started = False
            hdc.EndDoc()
            doc_started = False
            show_info("Print Job", f"Receipt sent to '{printer_name}'.", parent)
        except Exception as exc:
            if page_started:
                try:
                    hdc.EndPage()
                except Exception:
                    pass
            if doc_started:
                try:
                    hdc.EndDoc()
                except Exception:
                    pass
            show_error("Print Error", f"Failed to print the receipt:\n{exc}", parent)
        finally:
            try:
                hdc.DeleteDC()
            except Exception:
                pass
        return

    width_mm = RECEIPT_PAGE_WIDTH_MM
    height_mm = 297
    margin_left_right = RECEIPT_MARGIN_MM * mm
    margin_top_bottom = RECEIPT_TOP_MARGIN_MM * mm
    page_width = width_mm * mm
    page_height = height_mm * mm

    try:
        with tempfile.NamedTemporaryFile(delete=False, suffix=".pdf") as temp_pdf:
            temp_pdf_path = temp_pdf.name
        c = canvas.Canvas(temp_pdf_path, pagesize=(page_width, page_height))
        x_start = margin_left_right
        y_start = page_height - margin_top_bottom
        render_receipt_text(c, formatted_receipt, layout, x_start, y_start)
        c.showPage()
        c.save()
    except Exception as exc:
        show_error("Print Error", f"Failed to create receipt PDF:\n{exc}", parent)
        return

    try:
        subprocess.run(['lp', temp_pdf_path], check=True)
        show_info("Print Job", "The receipt has been sent to the printer.", parent)
    except Exception as e:
        show_error("Print Error", f"Failed to print the receipt: {e}", parent)
def main():
    app = QApplication(sys.argv)
    preferred_theme = load_ui_preferences()
    apply_theme(app, preferred_theme)
    # Ensure image folder exists
    os.makedirs(PRODUCT_IMAGE_FOLDER, exist_ok=True)
    if not load_products_from_csv():
        # Error shown inside load_products_from_csv function
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
        save_tendered_amounts()  # Save tendered amounts before closing
        sys.exit(exit_code)
    else:
        sys.exit()
if __name__ == "__main__":
    main()
