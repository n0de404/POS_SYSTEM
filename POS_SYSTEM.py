import sys
import os
import re
import csv
from datetime import datetime
from functools import partial
import tempfile
import subprocess
import json  # Import the json module
from copy import deepcopy
import pandas as pd
from reportlab.lib.pagesizes import letter, A4
from reportlab.pdfgen import canvas
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.lib.units import inch, mm
from reportlab.lib import colors
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from PyQt6.QtWidgets import QSizePolicy, QSpacerItem, QTabWidget  # Import QTabWidget
from PyQt6.QtWidgets import QFileDialog  # Import QFileDialog for file dialog

from PIL import Image, ImageQt

from PyQt6.QtWidgets import (QApplication, QCompleter, QGroupBox, QMainWindow, QTableWidget, QTableWidgetItem, QWidget, QLabel, QLineEdit, QPushButton, QComboBox,
                             QListWidget, QTextEdit, QHBoxLayout, QVBoxLayout, QGridLayout, QDialog,
                             QMessageBox, QInputDialog, QFileDialog, QScrollArea, QFrame, QSpinBox,
                             QDoubleSpinBox, QDialogButtonBox, QCheckBox, QHeaderView)
from PyQt6.QtGui import QColor, QPixmap, QAction, QActionGroup, QIcon, QFont, QPalette
from PyQt6.QtCore import Qt, QSize, QStringListModel

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

sales_summary = {}  # Stores sales data for reporting: {barcode: {"qty_sold": ..., "revenue": ...}}
product_variant_lookup = {}  # Maps SKU (including promo variants) to lookup data for scanning/searching
promo_inventory_map = {}  # Maps promo code to the number of base units consumed per sale
product_promo_columns = []  # Tracks additional promo pricing columns detected in the products CSV
bundle_promos = {}  # Stores bundle promos with their component details
current_theme_preference = "system"
current_theme_effective = "light"
basket_promos = []  # Stores basket-size promo tiers

users_data = {}  # Stores usernames and their passwords: {username: password}
current_user_name = None  # Stores the username of the currently logged-in user

ADMIN_PASSWORD_FILE = "admin_password.txt"
DEFAULT_ADMIN_PASSWORD = "p@ssw0rd01"
PRODUCTS_CSV_FILE = "POSProducts.csv"  # Name of the CSV file for products
USERS_FILE = "users.txt"  # Name of the text file for user credentials
PRODUCT_IMAGE_FOLDER = "product_images"  # Folder where product images are stored

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


# --- CSV Handling Functions ---
def load_products_from_csv(parent=None):
    global products, sales_summary, product_promo_columns
    products = {}
    sales_summary = {}
    product_promo_columns = []
    try:
        with open(PRODUCTS_CSV_FILE, mode='r', newline='', encoding='utf-8') as file:
            reader = csv.DictReader(file)
            base_headers = ['Stock No.', 'name', 'price', 'stock', 'image_filename']

            if not reader.fieldnames:
                show_error("CSV Format Error", f"The '{PRODUCTS_CSV_FILE}' file is missing a header row.", parent)
                return False

            missing_headers = [field for field in base_headers if field not in reader.fieldnames]
            if missing_headers:
                show_error(
                    "CSV Format Error",
                    f"The '{PRODUCTS_CSV_FILE}' file is missing required columns: {', '.join(missing_headers)}",
                    parent
                )
                return False

            promo_columns = [field for field in reader.fieldnames if field not in base_headers]
            product_promo_columns = promo_columns

            for row in reader:
                try:
                    barcode = row['Stock No.'].strip()
                    if not barcode:
                        continue  # Skip empty rows
                    name = row['name'].strip()
                    price = float(row['price'])
                    stock = int(row['stock'])
                    image_filename = row.get('image_filename', '').strip()

                    promo_prices = {}
                    for promo_code in promo_columns:
                        value = row.get(promo_code, "").strip()
                        if not value:
                            continue
                        try:
                            promo_prices[promo_code] = float(value)
                        except ValueError:
                            print(f"Skipping promo price for '{promo_code}' on product '{barcode}' due to invalid value: {value}")

                    if barcode not in products:
                        products[barcode] = []  # Initialize a list for variants

                    products[barcode].append({
                        "name": name,
                        "price": price,
                        "stock": stock,
                        "original_stock": stock,
                        "image_filename": image_filename,
                        "promos": promo_prices
                    })

                    if barcode not in sales_summary:
                        sales_summary[barcode] = {"qty_sold": 0, "revenue": 0.0}
                except (ValueError, KeyError) as e:
                    print(f"Skipping row due to data error in '{PRODUCTS_CSV_FILE}': {row} - {e}")

            if not products:
                show_warning(
                    "No Products Found",
                    f"The '{PRODUCTS_CSV_FILE}' file is empty or contains no valid product data after filtering errors.",
                    parent
                )
                return False
    except FileNotFoundError:
        show_error(
            "File Not Found",
            f"The product CSV file '{PRODUCTS_CSV_FILE}' was not found.\nPlease ensure it exists in the same directory as the script and includes the required columns.",
            parent
        )
        return False
    except Exception as e:
        show_error("Error", f"An unexpected error occurred while loading products: {e}", parent)
        return False
    return True


def load_promo_inventory(parent=None):
    """
    Loads the promo inventory mapping file that defines how many base units are consumed per promo sale.
    Expected columns: promo_code, units_per_sale
    """
    global promo_inventory_map
    promo_inventory_map = {}

    if not os.path.exists(PROMO_INVENTORY_FILE):
        print(f"Promo inventory file '{PROMO_INVENTORY_FILE}' not found. Defaulting promo usage to 1 per sale.")
        return True

    try:
        with open(PROMO_INVENTORY_FILE, mode='r', newline='', encoding='utf-8') as file:
            reader = csv.DictReader(file)
            required_headers = ['promo_code', 'units_per_sale']
            if not reader.fieldnames or any(field not in reader.fieldnames for field in required_headers):
                show_error(
                    "Promo CSV Format Error",
                    f"The '{PROMO_INVENTORY_FILE}' file must contain the columns: promo_code, units_per_sale.",
                    parent
                )
                return False

            for row in reader:
                promo_code = row.get('promo_code', '').strip()
                units_value = row.get('units_per_sale', '').strip()
                if not promo_code or not units_value:
                    continue
                try:
                    units_per_sale = float(units_value)
                    if units_per_sale.is_integer():
                        units_per_sale = int(units_per_sale)
                    promo_inventory_map[promo_code] = units_per_sale
                except ValueError:
                    print(f"Skipping promo inventory entry due to invalid units_per_sale value: {row}")
    except Exception as e:
        show_error("Error", f"An unexpected error occurred while loading promo inventory: {e}", parent)
        return False

    return True


def load_bundle_promos(parent=None):
    """
    Loads saved bundle promo definitions that map a bundle code to component products and price.
    """
    global bundle_promos
    bundle_promos = {}

    if not os.path.exists(PROMO_BUNDLES_FILE):
        return True

    try:
        with open(PROMO_BUNDLES_FILE, mode='r', encoding='utf-8') as file:
            data = json.load(file)
            if isinstance(data, dict):
                bundle_promos = data
            elif isinstance(data, list):
                # Support legacy list format by converting to dict
                for entry in data:
                    code = entry.get("code")
                    if not code:
                        continue
                    bundle_promos[code] = entry
            else:
                bundle_promos = {}
    except Exception as exc:
        show_error("Error", f"Failed to load bundle promos: {exc}", parent)
        return False

    return True


def save_bundle_promos(parent=None):
    """
    Persists bundle promo definitions to disk.
    """
    try:
        with open(PROMO_BUNDLES_FILE, mode='w', encoding='utf-8') as file:
            json.dump(bundle_promos, file, indent=2)
    except Exception as exc:
        show_error("Save Error", f"Failed to save bundle promos: {exc}", parent)


def save_basket_promos(parent=None):
    """
    Persists basket-size promo tiers to disk.
    """
    try:
        with open(BASKET_PROMOS_FILE, mode='w', encoding='utf-8') as file:
            json.dump({"tiers": basket_promos}, file, ensure_ascii=False, indent=4)
    except Exception as exc:
        show_error("Save Error", f"Failed to save basket promos: {exc}", parent)


def load_basket_promos(parent=None):
    """
    Loads basket-size promos that award freebies when order totals reach defined thresholds.
    """
    global basket_promos
    basket_promos = []

    if not os.path.exists(BASKET_PROMOS_FILE):
        return True

    try:
        with open(BASKET_PROMOS_FILE, mode='r', encoding='utf-8') as file:
            data = json.load(file)
            if isinstance(data, dict):
                entries = data.get("tiers") or data.get("promos") or list(data.values())
            elif isinstance(data, list):
                entries = data
            else:
                entries = []

            for entry in entries:
                try:
                    threshold = float(entry.get("threshold", 0))
                except (TypeError, ValueError):
                    continue
                freebies = entry.get("freebies") or []
                if not isinstance(freebies, list) or threshold <= 0:
                    continue
                basket_promos.append({
                    "code": entry.get("code") or f"BASKET_{int(threshold)}",
                    "name": entry.get("name") or "",
                    "threshold": threshold,
                    "freebies": freebies,
                    "message": entry.get("message", "")
                })
            basket_promos.sort(key=lambda x: x["threshold"])
    except Exception as exc:
        show_error("Error", f"Failed to load basket promos: {exc}", parent)
        return False

    return True


def save_promo_inventory(parent=None):
    """
    Persists the promo inventory mapping to disk so units per sale stay in sync with promo pricing.
    """
    try:
        with open(PROMO_INVENTORY_FILE, mode='w', newline='', encoding='utf-8') as file:
            fieldnames = ['promo_code', 'units_per_sale']
            writer = csv.DictWriter(file, fieldnames=fieldnames)
            writer.writeheader()
            for promo_code in sorted(promo_inventory_map.keys()):
                writer.writerow({
                    'promo_code': promo_code,
                    'units_per_sale': promo_inventory_map[promo_code]
                })
    except Exception as e:
        show_error("Save Error", f"Failed to save promo inventory: {e}", parent)


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
                product_variant_lookup[promo_sku] = {
                    "sku": promo_sku,
                    "base_barcode": barcode,
                    "variant_index": index,
                    "promo_code": promo_code,
                    "price": promo_price,
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
    try:
        with open(PRODUCTS_CSV_FILE, mode='w', newline='', encoding='utf-8') as file:
            base_fields = ['Stock No.', 'name', 'price', 'stock', 'image_filename']
            fieldnames = base_fields + product_promo_columns
            writer = csv.DictWriter(file, fieldnames=fieldnames)
            writer.writeheader()
            for barcode, variants in products.items():
                for variant in variants:
                    row = {
                        'Stock No.': barcode,
                        'name': variant['name'],
                        'price': variant['price'],
                        'stock': variant['stock'],
                        'image_filename': variant.get('image_filename', '')
                    }
                    promos = variant.get('promos', {})
                    for promo_code in product_promo_columns:
                        value = promos.get(promo_code, "")
                        row[promo_code] = value
                    writer.writerow(row)
    except Exception as e:
        show_error("Save Error", f"Failed to save product data to CSV: {e}", parent)


# --- User Management Functions ---
def load_users(parent=None):
    """
    Loads usernames and passwords from the USERS_FILE.
    If the file doesn't exist or is empty, it creates a default 'cashier' user.
    """
    global users_data
    users_data = {}
    if os.path.exists(USERS_FILE):
        try:
            with open(USERS_FILE, 'r', encoding='utf-8') as f:
                for line in f:
                    parts = line.strip().split(',', 1)  # Split only on the first comma
                    if len(parts) == 2:
                        username, password = parts
                        users_data[username] = password
                    else:
                        print(f"Skipping malformed line in {USERS_FILE}: {line.strip()}")
        except Exception as e:
            show_error("Error", f"Failed to load user data from '{USERS_FILE}': {e}", parent)

    # Ensure there's at least one user if file was empty or didn't exist
    if not users_data:
        users_data["cashier"] = "cashier123"  # Default password for cashier
        save_users(parent)


def save_users(parent=None):
    """
    Saves the current usernames and passwords to the USERS_FILE.
    """
    try:
        with open(USERS_FILE, 'w', newline='', encoding='utf-8') as f:
            for username, password in users_data.items():
                f.write(f"{username},{password}\n")
    except Exception as e:
        show_error("Error", f"Failed to save user data to '{USERS_FILE}': {e}", parent)



def save_tendered_amounts():
    """Saves the total cash and GCash tendered amounts to a JSON file."""
    global total_cash_tendered, total_gcash_tendered
    try:
        with open(TENDERED_AMOUNTS_FILE, 'w', encoding='utf-8') as f:
            json.dump({"cash": total_cash_tendered, "gcash": total_gcash_tendered}, f, ensure_ascii=False, indent=4)
        print("Tendered amounts saved successfully.")
    except Exception as e:
        print(f"Error saving tendered amounts: {e}")

def load_tendered_amounts():
    """Loads the total cash and GCash tendered amounts from a JSON file."""
    global total_cash_tendered, total_gcash_tendered
    try:
        with open(TENDERED_AMOUNTS_FILE, 'r', encoding='utf-8') as f:
            data = json.load(f)
            total_cash_tendered = data.get("cash", 0.0)
            total_gcash_tendered = data.get("gcash", 0.0)
        print("Tendered amounts loaded successfully.")
    except FileNotFoundError:
        print("Tendered amounts file not found. Starting with zero amounts.")
        total_cash_tendered = 0.0
        total_gcash_tendered = 0.0
    except Exception as e:
        print(f"Error loading tendered amounts: {e}")
        total_cash_tendered = 0.0
        total_gcash_tendered = 0.0
    

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
    """Saves the inventory summary to a CSV file."""
    try:
        with open(INVENTORY_SUMMARY_FILE, mode='w', newline='', encoding='utf-8') as file:
            fieldnames = ['Stock No.', 'name', 'price', 'stock', 'original_stock', 'qty_sold', 'revenue']
            writer = csv.DictWriter(file, fieldnames=fieldnames)
            writer.writeheader()
            for barcode, variants in products.items():
                for variant in variants:
                    # Get qty_sold and revenue from sales_summary, default to 0 if not found
                    qty_sold = sales_summary.get(barcode, {}).get('qty_sold', 0)
                    revenue = sales_summary.get(barcode, {}).get('revenue', 0.0)
                    writer.writerow({
                        'Stock No.': barcode,
                        'name': variant['name'],
                        'price': variant['price'],
                        'stock': variant['stock'],
                        'original_stock': variant['original_stock'],
                        'qty_sold': qty_sold,
                        'revenue': revenue
                    })
        print("Inventory summary saved successfully.")
    except Exception as e:
        print(f"Error saving inventory summary: {e}")

def save_sales_summary():
    """Saves the sales summary to a JSON file."""
    try:
        with open(SALES_SUMMARY_FILE, 'w', encoding='utf-8') as file:
            json.dump(sales_summary, file, indent=4)
        print("Sales summary saved successfully.")
    except Exception as e:
        print(f"Error saving sales summary: {e}")

def save_receipts_archive():
    """Saves the receipts archive to a JSON file."""
    try:
        with open(RECEIPTS_ARCHIVE_FILE, 'w', encoding='utf-8') as file:
            json.dump(receipts_archive, file, indent=4)
        print("Receipts archive saved successfully.")
    except Exception as e:
        print(f"Error saving receipts archive: {e}")
        
def load_inventory_summary():
    """
    Loads the inventory summary from a CSV file without overriding the authoritative
    product data that was loaded from POSProducts.csv.
    """
    global sales_summary
    sales_summary = sales_summary or {}

    try:
        with open(INVENTORY_SUMMARY_FILE, mode='r', newline='', encoding='utf-8') as file:
            reader = csv.DictReader(file)
            for row in reader:
                barcode = row['Stock No.'].strip()
                qty_sold = int(row.get('qty_sold', 0) or 0)
                revenue = float(row.get('revenue', 0) or 0)

                if barcode in products:
                    variant = products[barcode][0]
                    original_stock_value = row.get('original_stock')
                    if original_stock_value is not None:
                        try:
                            variant['original_stock'] = int(original_stock_value)
                        except ValueError:
                            pass
                else:
                    print(f"Warning: inventory summary references missing product '{barcode}'. Skipping stock restore.")

                sales_summary[barcode] = {
                    "qty_sold": qty_sold,
                    "revenue": revenue
                }
        print("Inventory summary loaded successfully.")
    except FileNotFoundError:
        print("Inventory summary file not found. Starting with empty data.")
    except Exception as e:
        print(f"Error loading inventory summary: {e}")


def load_sales_summary():
    """Loads the sales summary from a JSON file."""
    global sales_summary
    try:
        with open(SALES_SUMMARY_FILE, 'r', encoding='utf-8') as file:
            sales_summary = json.load(file)
        print("Sales summary loaded successfully.")
    except FileNotFoundError:
        print("Sales summary file not found. Starting with empty data.")
        sales_summary = {}
    except Exception as e:
        print(f"Error loading sales summary: {e}")
        sales_summary = {}

def load_receipts_archive():
    """Loads the receipts archive from a JSON file."""
    global receipts_archive
    try:
        with open(RECEIPTS_ARCHIVE_FILE, 'r', encoding='utf-8') as file:
            receipts_archive = json.load(file)
        print("Receipts archive loaded successfully.")
    except FileNotFoundError:
        print("Receipts archive file not found. Starting with empty archive.")
        receipts_archive = {}
    except Exception as e:
        print(f"Error loading receipts archive: {e}")
        receipts_archive = {}

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
        self.setWindowTitle("Login")
        self.setFixedSize(400, 280)
        self.current_user_name = None

        self.all_usernames_list = list(users_data.keys())

        layout = QVBoxLayout()

        lbl_username = QLabel("Username:")
        lbl_username.setFont(QFont("Arial", 10))
        layout.addWidget(lbl_username)

        self.combo_username = QComboBox()
        self.combo_username.setEditable(True)
        self.combo_username.addItems(self.all_usernames_list)
        if self.all_usernames_list:
            self.combo_username.setCurrentIndex(0)
        self.combo_username.setFixedWidth(300)
        layout.addWidget(self.combo_username)

        lbl_password = QLabel("Password:")
        lbl_password.setFont(QFont("Arial", 10))
        layout.addWidget(lbl_password)

        password_layout = QHBoxLayout()
        self.entry_password = QLineEdit()
        self.entry_password.setEchoMode(QLineEdit.EchoMode.Password)
        self.entry_password.setFixedWidth(300)
        password_layout.addWidget(self.entry_password)

        self.btn_toggle_password = QPushButton("Show")
        self.btn_toggle_password.setFixedWidth(50)
        self.btn_toggle_password.clicked.connect(self.toggle_password_visibility)
        password_layout.addWidget(self.btn_toggle_password)

        layout.addLayout(password_layout)

        btn_login = QPushButton("Login")
        btn_login.setStyleSheet("background-color: #4CAF50; color: white; font-weight: bold;")
        btn_login.clicked.connect(self.do_login)
        btn_login.setFixedWidth(150)
        layout.addWidget(btn_login, alignment=Qt.AlignmentFlag.AlignCenter)

        btn_create_account = QPushButton("Create Account")
        btn_create_account.setStyleSheet("background-color: #2196F3; color: white; font-weight: bold;")
        btn_create_account.clicked.connect(self.create_account_flow)
        btn_create_account.setFixedWidth(150)
        layout.addWidget(btn_create_account, alignment=Qt.AlignmentFlag.AlignCenter)

        self.setLayout(layout)

        # Connect completer-like behavior manually
        self.combo_username.lineEdit().textEdited.connect(self.update_username_options)
        self.combo_username.activated.connect(self.handle_combobox_selection)

    def toggle_password_visibility(self):
        if self.entry_password.echoMode() == QLineEdit.EchoMode.Password:
            self.entry_password.setEchoMode(QLineEdit.EchoMode.Normal)
            self.btn_toggle_password.setText("Hide")
        else:
            self.entry_password.setEchoMode(QLineEdit.EchoMode.Password)
            self.btn_toggle_password.setText("Show")

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

    def do_login(self):
        username = self.combo_username.currentText().strip()
        password = self.entry_password.text()
        if not username or not password:
            show_error("Login Error", "Please enter both username and password.", self)
            return
        if username not in users_data:
            show_error("Login Error", "User  not found.", self)
            return
        if users_data[username] == password:
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
        self.entry_new_password = QLineEdit()
        self.entry_new_password.setEchoMode(QLineEdit.EchoMode.Password)
        self.entry_new_password.setFixedWidth(300)
        pass_layout.addWidget(self.entry_new_password)
        self.btn_toggle_new_password = QPushButton("Show")
        self.btn_toggle_new_password.setFixedWidth(50)
        self.btn_toggle_new_password.clicked.connect(self.toggle_password_visibility_new)
        pass_layout.addWidget(self.btn_toggle_new_password)
        layout.addLayout(pass_layout)

        lbl_confirm_password = QLabel("Confirm Password:")
        lbl_confirm_password.setFont(QFont("Arial", 10))
        layout.addWidget(lbl_confirm_password)
        conf_pass_layout = QHBoxLayout()
        self.entry_confirm_password = QLineEdit()
        self.entry_confirm_password.setEchoMode(QLineEdit.EchoMode.Password)
        self.entry_confirm_password.setFixedWidth(300)
        conf_pass_layout.addWidget(self.entry_confirm_password)
        self.btn_toggle_confirm_password = QPushButton("Show")
        self.btn_toggle_confirm_password.setFixedWidth(50)
        self.btn_toggle_confirm_password.clicked.connect(self.toggle_password_visibility_confirm)
        conf_pass_layout.addWidget(self.btn_toggle_confirm_password)
        layout.addLayout(conf_pass_layout)

        btn_create_account = QPushButton("Create Account")
        btn_create_account.setStyleSheet("background-color: #4CAF50; color: white; font-weight: bold;")
        btn_create_account.clicked.connect(self.save_new_user)
        btn_create_account.setFixedWidth(150)
        layout.addWidget(btn_create_account, alignment=Qt.AlignmentFlag.AlignCenter)

        self.setLayout(layout)

    def toggle_password_visibility_new(self):
        if self.entry_new_password.echoMode() == QLineEdit.EchoMode.Password:
            self.entry_new_password.setEchoMode(QLineEdit.EchoMode.Normal)
            self.btn_toggle_new_password.setText("Hide")
        else:
            self.entry_new_password.setEchoMode(QLineEdit.EchoMode.Password)
            self.btn_toggle_new_password.setText("Show")

    def toggle_password_visibility_confirm(self):
        if self.entry_confirm_password.echoMode() == QLineEdit.EchoMode.Password:
            self.entry_confirm_password.setEchoMode(QLineEdit.EchoMode.Normal)
            self.btn_toggle_confirm_password.setText("Hide")
        else:
            self.entry_confirm_password.setEchoMode(QLineEdit.EchoMode.Password)
            self.btn_toggle_confirm_password.setText("Show")

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

        users_data[new_username] = new_password  # Store the plaintext password
        save_users(self)

        show_info("Success", f"User  '{new_username}' created successfully. You can now login with this account.", self)
        self.accept()


class InventoryManagementDialog(QDialog):
    def __init__(self, products, parent=None):
        super().__init__(parent)
        self.setWindowTitle("Inventory Management - Product Stock")
        self.resize(700, 450)
        self.products = products  # Store the products dictionary

        layout = QVBoxLayout()
        self.setLayout(layout)

        title = QLabel("Current Product Stocks")
        title.setFont(QFont("Arial", 14, QFont.Weight.Bold))
        layout.addWidget(title)

        self.table = QTableWidget(0, 3)
        self.table.setHorizontalHeaderLabels(["Stock No.", "Product Name", "Stock Left"])
        self.table.horizontalHeader().setStretchLastSection(True)
        layout.addWidget(self.table)

        # Add Import, Replenish, and Export buttons
        btn_layout = QHBoxLayout()
        self.btn_import = QPushButton("Import Excel")
        self.btn_import.clicked.connect(self.import_excel)
        btn_layout.addWidget(self.btn_import)

        self.btn_replenish = QPushButton("Replenish Stock")
        self.btn_replenish.clicked.connect(self.replenish_stock)
        btn_layout.addWidget(self.btn_replenish)

        self.btn_export = QPushButton("Export Summary")
        self.btn_export.clicked.connect(self.export_summary)
        btn_layout.addWidget(self.btn_export)

        self.btn_manage_promos = QPushButton("Manage Promos")
        self.btn_manage_promos.clicked.connect(self.manage_promos)
        btn_layout.addWidget(self.btn_manage_promos)

        self.btn_manage_bundles = QPushButton("Manage Bundles")
        self.btn_manage_bundles.clicked.connect(self.manage_bundles)
        btn_layout.addWidget(self.btn_manage_bundles)

        self.btn_manage_basket = QPushButton("Manage Basket Rewards")
        self.btn_manage_basket.clicked.connect(self.manage_basket_promos)
        btn_layout.addWidget(self.btn_manage_basket)

        self.btn_close = QPushButton("Close")
        self.btn_close.clicked.connect(self.close)
        btn_layout.addWidget(self.btn_close)

        layout.addLayout(btn_layout)

        self.populate_table()

    def manage_promos(self):
        dlg = PromoManagementDialog(self.products, self)
        if dlg.exec() == QDialog.DialogCode.Accepted:
            # Table content may not change, but refresh to reflect any potential data updates.
            self.populate_table()
            parent = self.parent()
            if parent and hasattr(parent, "refresh_product_search_options"):
                parent.refresh_product_search_options()

    def manage_bundles(self):
        dlg = BundlePromoDialog(self.products, self)
        if dlg.exec() == QDialog.DialogCode.Accepted:
            parent = self.parent()
            if parent and hasattr(parent, "refresh_product_search_options"):
                parent.refresh_product_search_options()

    def manage_basket_promos(self):
        dlg = BasketPromoDialog(self.products, self)
        if dlg.exec() == QDialog.DialogCode.Accepted:
            load_basket_promos(self)

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
        self.table.setRowCount(0)  # Clear existing rows

        # Sort products by name
        sorted_products = sorted(self.products.items(), key=lambda item: item[1][0]["name"].lower())

        for barcode, variants in sorted_products:
            for variant in variants:
                row = self.table.rowCount()
                self.table.insertRow(row)
                self.table.setItem(row, 0, QTableWidgetItem(barcode))
                self.table.setItem(row, 1, QTableWidgetItem(variant["name"]))
                self.table.setItem(row, 2, QTableWidgetItem(str(variant["stock"])))

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

    def load_bundle_data(self, bundle_code):
        bundle_code = (bundle_code or "").strip()
        bundle = bundle_promos.get(bundle_code, {})

        self.bundle_name_edit.setText(bundle.get("name", ""))
        self.bundle_price_spin.blockSignals(True)
        self.bundle_price_spin.setValue(float(bundle.get("price", 0)))
        self.bundle_price_spin.blockSignals(False)
        self.bundle_price_spin.setProperty("custom_edit", False)

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

        bundle_promos[bundle_code] = {
            "code": bundle_code,
            "name": bundle_name,
            "price": round(bundle_price, 2),
            "components": selected_components,
            "sku": sku
        }

        save_bundle_promos(self)
        rebuild_product_variant_lookup()

        if self.bundle_code_combo.findText(bundle_code) == -1:
            self.bundle_code_combo.addItem(bundle_code)

        show_info("Bundle Saved", f"Bundle '{bundle_code}' saved successfully.", self)
        self.accept()


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

        form_layout.addWidget(QLabel("Threshold Amount (₱):"), 2, 0)
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
            display = f"{code} - ₱{entry.get('threshold', 0):,.2f}"
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

        self.cart = cart  # reference global cart
        self.current_item_count = current_item_count
        self.current_discount = current_discount
        self.products = products  # Make sure this is accessibl
        self.sales_summary = sales_summary  # Make sure this is accessible
        self.current_theme_mode = current_theme_preference
        self.current_effective_theme = current_theme_effective
        self.theme_actions = {}
        self.theme_action_group = None
        self.applied_freebies = []
        self.applied_freebie_messages = []

        self.init_ui()
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

        # Scan Stock No. Label and Entry
        scan_layout = QHBoxLayout()
        lbl_scan = QLabel("Scan Stock No.:")
        lbl_scan.setFont(QFont("Arial", 15, QFont.Weight.Bold))
        scan_layout.addWidget(lbl_scan)

        self.entry_barcode = QLineEdit()
        self.entry_barcode.setPlaceholderText("Enter barcode or stock number") # Added placeholder
        self.entry_barcode.setFont(QFont("Arial", 14))
        scan_layout.addWidget(self.entry_barcode, stretch=1) # Allow it to expand
        self.entry_barcode.returnPressed.connect(self.handle_scan)

        input_layout.addLayout(scan_layout)

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
        self.label_total.setStyleSheet("color: navy;")
        total_layout.addWidget(self.label_total)

        self.label_total_amount = QLabel("") # Separate label for the amount
        self.label_total_amount.setFont(QFont("Arial", 20, QFont.Weight.Bold))
        self.label_total_amount.setStyleSheet("color: navy;")
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

        # Product Details Section
        self.label_product_name_display = QLabel("PRODUCT NAME: ")
        self.label_product_name_display.setFont(QFont("Arial", 15))
        self.label_product_name_display.setWordWrap(False)  # Ensure word wrap disabled to favor one line
        info_layout.addWidget(self.label_product_name_display, alignment=Qt.AlignmentFlag.AlignLeft)

        self.label_product_price_display = QLabel("PRICE: ")
        self.label_product_price_display.setFont(QFont("Arial", 15))
        self.label_product_price_display.setStyleSheet("color: darkgreen;")
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
        # Add buttons to the grid layout with specified colors, fixed sizes, and updated style for Default Design Guidelines
        # Assuming this list is used to create QPushButton widgets and apply their styles
        buttons = [
            ("DISCOUNT", self.set_discount, """
                QPushButton {
                    background-color: #6C757D;
                    color: white;
                    font-size: 25px;  
                    border-radius: 10px;
                }
                QPushButton:hover {
                    background-color: #5a6268; /* Darker gray on hover */
                }
            """),
            ("SET QUANTITY", self.set_item_count, """
                QPushButton {
                    background-color: #6C757D;
                    color: white;
                    font-size: 25px;
                    border-radius: 10px;
                }
                QPushButton:hover {
                    background-color: #5a6268; /* Darker gray on hover */
                }
            """),
            ("INVENTORY", self.inventory_management, """
                QPushButton {
                    background-color: #ADD8E6;
                    font-size: 25px;
                    color: black;
                    border-radius: 10px;
                }
                QPushButton:hover {
                    background-color: #9ac7d1; /* Darker blue on hover */
                }
            """),
            ("SALES SUMMARY", self.summary_view, """
                QPushButton {
                    background-color: #ffa940;
                    font-size: 25px;
                    color: white;
                    border-radius: 10px;
                }
                QPushButton:hover {
                    background-color: #e69537; /* Darker orange on hover */
                }
            """),
            ("VOID", self.void_selected_item, """
                QPushButton {
                    background-color: #d32f2f;
                    color: white;
                    font-size: 25px;
                    border-radius: 10px;
                }
                QPushButton:hover {
                    background-color: #b71c1c; /* Darker red on hover */
                }
            """),
            ("CHECKOUT", self.checkout, """
                QPushButton {
                    background-color: #73d13d;
                    color: black;
                    font-size: 25px;
                    border-radius: 10px;
                }
                QPushButton:hover {
                    background-color: #61b332; /* Darker green on hover */
                }
            """)
        ]
        # Set a fixed height for the buttons
        fixed_button_height = 100  # Set your desired height here
        # Add buttons to the grid layout (2 columns, 3 rows)
        for i, (text, slot, style) in enumerate(buttons):
            btn = QPushButton(text)
            btn.setMinimumSize(140, fixed_button_height)  # Set minimum width and fixed height
            btn.setFixedHeight(fixed_button_height)  # Set fixed height for the button
            btn.setStyleSheet(style + " font-size: 25px; font-weight: bold; padding: 10px;")
            btn.clicked.connect(slot)
            row = i // 2  # 2 columns
            col = i % 2   # column 0 or 1
            buttons_grid_layout.addWidget(btn, row, col)
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
        variants = products.get(base_barcode, [])

        variant = variants[variant_index] if variant_index < len(variants) else (variants[0] if variants else None)
        if variant:
            self.label_product_name_display.setText(f"Name: {item['name']}")
            self.label_product_price_display.setText(f"Price: P{item['price']:.2f}")
            self.label_product_stock_display.setText(f"Stock: {variant['stock']}")
            self.label_product_barcode_number.setText(f"Stock No.: {sku}")
            self.display_product_image(variant.get('image_filename'))
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
                self.entry_barcode.clear()
                self.entry_barcode.setFocus()
        else:
            show_warning("Format Error", "Invalid product selection format.", self)
            self.clear_product_display()

    def clear_product_display(self):
        self.label_product_name_display.setText("PRODUCT NAME: ")
        self.label_product_price_display.setText("PRICE: ")
        self.label_product_stock_display.setText("STOCK: ")
        self.label_product_barcode_number.setText("STOCK NO.: ")
        self.label_product_image.setPixmap(self.default_pixmap)


    def display_product_image(self, image_filename):
        if image_filename:
            image_path = os.path.join(PRODUCT_IMAGE_FOLDER, image_filename)
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

    def add_item_to_cart_by_sku(self, sku, show_not_found=True):
        global current_item_count, current_discount
        lookup = product_variant_lookup.get(sku)
        if lookup is None:
            if show_not_found:
                show_warning("Not Found", f"Barcode '{sku}' not found in product database.", self)
                self.display_product_image(None)
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
                "original_unit_price": lookup['price']
            }

            self.cart.append(item)
            bundle_label = f"{lookup['sku']} - {item['name']} (Bundle) x{qty} - P{item['price'] * qty:.2f}"
            self.listbox.addItem(bundle_label)

            component_summary = ", ".join(
                f"{component['quantity']}x {component['name']}"
                for component in components_copy
            )

            self.label_product_name_display.setText(f"BUNDLE: {item['name']}")
            self.label_product_price_display.setText(f"Price: P{lookup['price']:.2f}")
            stock_caption = "Unlimited" if bundle_stock_cap is None else str(bundle_stock_cap)
            self.label_product_stock_display.setText(f"Bundle Stock: {stock_caption}")
            self.label_product_barcode_number.setText(f"Includes: {component_summary}")
            self.display_product_image(lookup.get("image_filename"))

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
                self.display_product_image(None)
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
            "original_unit_price": lookup['price']
        }

        self.cart.append(item)
        self.listbox.addItem(f"{lookup['sku']} - {item['name']} x{qty} - P{item['price'] * qty:.2f}")

        self.label_product_name_display.setText(f"Name: {item['name']}")
        self.label_product_price_display.setText(f"Price: P{lookup['price']:.2f}")
        self.label_product_stock_display.setText(f"Stock: {variant['stock']}")
        self.label_product_barcode_number.setText(f"Stock No.: {lookup['sku']}")
        self.display_product_image(variant.get('image_filename'))

        current_item_count = 1
        current_discount = 0.0
        self.update_total()
        return True

    def handle_scan(self):
        global current_item_count, current_discount

        barcode_input = self.entry_barcode.text().strip()
        self.entry_barcode.clear()
        self.entry_product_search.setEditText("")

        # Clear previous product info display
        self.clear_product_display()

        if not barcode_input:
            return

        added = self.add_item_to_cart_by_sku(barcode_input)
        if not added:
            self.display_product_image(None)

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
        if self.applied_freebies:
            append_columns("Rewards Earned:")
            for freebie in self.applied_freebies:
                label = f"{freebie['name']} x{freebie['qty']}"
                append_columns(label, "FREE")
            for message in self.applied_freebie_messages:
                if message:
                    append_columns(message)
        receipt_text_content += "-" * width + "\n"

        receipt_text_content += f"{current_time:^{width}}\n"
        receipt_text_content += f"{'Cashier: ' + self.current_user_name:^{width}}\n"
        receipt_text_content += f"{'SUNNYWARE PHILIPPINES':^{width}}\n"
        receipt_text_content += f"{'THANK YOU SO MUCH!':^{width}}\n"

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
        self.applied_freebies = []
        self.applied_freebie_messages = []

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

# Replace the SalesSummaryDialog class entirely with:

class SalesSummaryDialog(QDialog):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setWindowTitle("Sales Summary")
        self.resize(1000, 540)
        self.setStyleSheet("""
            QDialog {
                background-color: #ffffff;
                font-family: 'Segoe UI', Tahoma, Geneva, Verdana, sans-serif;
                color: #6b7280;
                padding: 24px;
                border-radius: 12px;
                max-width: 1200px;
            }
            QLabel#titleLabel {
                font-size: 20px;
                font-weight: 700;
                color: #111827;
                margin-bottom: 24px;
            }
            QTableWidget {
                border: none;
                border-radius: 12px;
                font-size: 15px;
                color: #374151;
                background-color: #f9fafb;
                padding: 8px;
            }
            QTableWidget::item {
                padding: 12px 8px;
            }
            QHeaderView::section {
                background-color: #2563eb;
                color: white;
                font-weight: 700;
                font-size: 15px;
                padding: 12px;
                border: none;
                letter-spacing: 0.05em;
            }
            QPushButton {
                background-color: #2563eb;
                color: white;
                border-radius: 12px;
                font-size: 15px;
                margin-top: 24px;
                min-width: 140px;
            }
            QPushButton:hover {
                background-color: #1e40af;
            }
            .summaryLabel {
                font-size: 18px;
                color: #6b7280;
                margin-top: 16px;
                font-weight: 600;
            }
            QHBoxLayout {
                spacing: 16px;
            }
        """)

        main_layout = QVBoxLayout(self)
        main_layout.setAlignment(Qt.AlignmentFlag.AlignTop)

        title = QLabel("Sales Summary Report")
        title.setObjectName("titleLabel")
        title.setAlignment(Qt.AlignmentFlag.AlignCenter)
        main_layout.addWidget(title)

        self.table = QTableWidget()
        self.table.setColumnCount(5)
        self.table.setHorizontalHeaderLabels(["STOCK #", "Product Name", "Quantity Sold", "Price", "Total Revenue"])
        self.table.horizontalHeader().setDefaultSectionSize(140)
        self.table.horizontalHeader().setStretchLastSection(True)
        self.table.setSortingEnabled(True)
        self.table.setSelectionBehavior(QTableWidget.SelectionBehavior.SelectRows)
        main_layout.addWidget(self.table)

        self.populate_sales_summary()

        # Summary labels for totals and payments
        self.label_total_items = QLabel()
        self.label_total_revenue = QLabel()
        self.label_cash_tendered = QLabel()
        self.label_gcash_tendered = QLabel()

        # Apply common style class
        self.label_total_items.setProperty("class", "summaryLabel")
        self.label_total_revenue.setProperty("class", "summaryLabel")
        self.label_cash_tendered.setProperty("class", "summaryLabel")
        self.label_gcash_tendered.setProperty("class", "summaryLabel")

        # Create a layout for the summary labels
        summary_layout = QVBoxLayout()
        summary_layout.addWidget(self.label_total_items)
        summary_layout.addWidget(self.label_total_revenue)
        summary_layout.addWidget(self.label_cash_tendered)
        summary_layout.addWidget(self.label_gcash_tendered)
        main_layout.addLayout(summary_layout)

        # Update the summary labels with the calculated values
        self.update_summary_labels()

        # Button layout
        button_layout = QHBoxLayout()
        self.export_excel_button = QPushButton("Export to Excel")
        self.export_pdf_button = QPushButton("Export to PDF")
        button_layout.addWidget(self.export_excel_button)
        button_layout.addWidget(self.export_pdf_button)
        main_layout.addLayout(button_layout)

        self.export_excel_button.clicked.connect(self.export_to_excel)
        self.export_pdf_button.clicked.connect(self.export_to_pdf)

    def populate_sales_summary(self):
        products = self.parent().products  # Get the products dictionary
        self.table.setRowCount(len(products))  # Set row count to the number of products

        row = 0
        for barcode, variants in products.items():
            # Get the first variant's name (assuming all variants have the same name)
            product_name = variants[0]['name']

            # Get sales data from sales_summary, defaulting to 0 if not found
            sales_data = self.parent().sales_summary.get(barcode, {"qty_sold": 0, "revenue": 0.0})
            quantity_sold = sales_data['qty_sold']
            total_revenue = sales_data['revenue']

            # Calculate price per item
            price_per_item = total_revenue / quantity_sold if quantity_sold > 0 else 0.0
            total_price = price_per_item * quantity_sold

            # Set the items in the table
            self.table.setItem(row, 0, QTableWidgetItem(barcode))
            self.table.setItem(row, 1, QTableWidgetItem(product_name))
            self.table.setItem(row, 2, QTableWidgetItem(str(quantity_sold)))
            self.table.setItem(row, 3, QTableWidgetItem(f"P{price_per_item:,.2f}"))  # Price per item
            self.table.setItem(row, 4, QTableWidgetItem(f"P{total_price:,.2f}"))

            row += 1  # Increment row counter

        self.table.resizeColumnsToContents()
        self.table.resizeRowsToContents()

    def update_summary_labels(self):
        sales_data = self.parent().sales_summary
        total_quantity_sold = sum(data['qty_sold'] for data in sales_data.values())
        total_revenue = 0.0
        for barcode, data in sales_data.items():
            total_revenue += data['revenue']

        global total_cash_tendered, total_gcash_tendered

        self.label_total_items.setText(f"<b>Total Items Sold:</b> {total_quantity_sold}")
        self.label_total_revenue.setText(f"<b>Total:</b> P{total_revenue:,.2f}")
        self.label_cash_tendered.setText(f"<b>Cash:</b> P{total_revenue - total_gcash_tendered:,.2f}")
        self.label_gcash_tendered.setText(f"<b>GCash:</b> P{total_gcash_tendered:,.2f}")


    def export_to_excel(self):
        global sales_summary, total_cash_tendered, total_gcash_tendered  # Declare globals at the beginning
        products = self.parent().products  # Get the products dictionary
        sales_data = self.parent().sales_summary

        if not products:  # Check if there are any products
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
                product_name = variants[0]['name']  # Get the first variant's name
                # Get sales data from sales_summary, defaulting to 0 if not found
                data_item = sales_data.get(barcode, {"qty_sold": 0, "revenue": 0.0})
                qty_sold = data_item['qty_sold']
                revenue = data_item['revenue']

                # Calculate price per item
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

                # Write cash and gcash tendered info two rows below totals
                row_after = len(df) + 1
                worksheet.write(row_after, 0, "Cash:")
                worksheet.write(row_after, 1, total_revenue - total_gcash_tendered, currency_format)
                worksheet.write(row_after + 1, 0, "GCash:")
                worksheet.write(row_after + 1, 1, total_gcash_tendered, currency_format)

            QMessageBox.information(self, "Export Successful", f"Sales summary has been exported to:\n{file_path}")

        except Exception as e:
            QMessageBox.critical(self, "Export Error", f"Failed to export sales summary to Excel:\n{e}")

        # Reset sales summary after successful export
        sales_summary = {}
        total_cash_tendered = 0.0
        total_gcash_tendered = 0.0
        save_sales_summary()
        self.populate_sales_summary()
        self.update_summary_labels()

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

            # Title Style
            title_style = styles['Heading1']
            title_style.fontSize = 24
            title_style.leading = 30
            title_style.alignment = 1  # Center
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

                # Calculate price per item and total revenue
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

            # Table Style
            table_style = TableStyle([
                ('BACKGROUND', (0, 0), (-1, 0), colors.HexColor("#2563eb")),
                ('TEXTCOLOR', (0, 0), (-1, 0), colors.whitesmoke),
                ('ALIGN', (2, 1), (-1, -1), 'RIGHT'),
                ('FONTNAME', (0, 0), (-1, 0), 'Helvetica-Bold'),
                ('FONTSIZE', (0, 0), (-1, 0), 14),
                ('BOTTOMPADDING', (0, 0), (-1, 0), 12),
                ('BACKGROUND', (0, 1), (-1, -1), colors.HexColor("#f9f9f9")),
                ('GRID', (0, 0), (-1, -1), 1, colors.grey),
                ('ROWBACKGROUNDS', (0, 1), (-1, -1), [colors.white, colors.HexColor("#e1eaf7")])
            ])

            col_widths = [70, 180, 80, 80, 100]
            sales_table = Table(data, colWidths=col_widths)
            sales_table.setStyle(table_style)

            elements.append(sales_table)
            elements.append(Spacer(1, 24))

            # Normal Style
            normal_style = styles['Normal']
            normal_style.fontSize = 16
            normal_style.textColor = colors.HexColor("#6b7280")

            elements.append(Paragraph(f"<b>Total Items Sold:</b> {total_quantity_sold}", normal_style))
            elements.append(Paragraph(f"<b>Total Revenue:</b> P{total_revenue:,.2f}", normal_style))

            global total_cash_tendered, total_gcash_tendered
            elements.append(Paragraph(f"<b>Cash Tendered:</b> P{total_revenue - total_cash_tendered:,.2f}", normal_style))
            elements.append(Paragraph(f"<b>GCash Tendered:</b> P{total_gcash_tendered:,.2f}", normal_style))

            elements.append(Spacer(1, 24))

            # Most In Demand Item Section
            heading2_style = styles['Heading2']
            heading2_style.textColor = colors.HexColor("#2563eb")
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
        self.update_summary_labels()


class ArchiveDialog(QDialog):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setWindowTitle("Archived Receipts")
        self.setFixedSize(400, 600)

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



def print_receipt_pdf(receipt_text, parent=None):
    layout = compute_receipt_layout()
    width_mm = RECEIPT_PAGE_WIDTH_MM
    height_mm = 297
    margin_left_right = RECEIPT_MARGIN_MM * mm
    margin_top_bottom = RECEIPT_TOP_MARGIN_MM * mm
    page_width = width_mm * mm
    page_height = height_mm * mm

    with tempfile.NamedTemporaryFile(delete=False, suffix=".pdf") as temp_pdf:
        temp_pdf_path = temp_pdf.name

    c = canvas.Canvas(temp_pdf_path, pagesize=(page_width, page_height))

    x_start = margin_left_right
    y_start = page_height - margin_top_bottom

    render_receipt_text(c, receipt_text, layout, x_start, y_start)
    c.showPage()
    c.save()

    try:
        if sys.platform.startswith('win'):
            os.startfile(temp_pdf_path, "print")
        elif sys.platform.startswith('darwin'):
            subprocess.run(['lp', temp_pdf_path], check=True)
        else:
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
