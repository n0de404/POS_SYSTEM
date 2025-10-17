import sys
import os
import re
import csv
from datetime import datetime
import tempfile
import subprocess
import json  # Import the json module
import pandas as pd
from reportlab.lib.pagesizes import letter, A4
from reportlab.pdfgen import canvas
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.lib.units import inch, mm
from reportlab.lib import colors
from PyQt6.QtWidgets import QSizePolicy, QSpacerItem, QTabWidget  # Import QTabWidget
from PyQt6.QtWidgets import QFileDialog  # Import QFileDialog for file dialog

from PIL import Image, ImageQt

from PyQt6.QtWidgets import (QApplication, QCompleter, QGroupBox, QMainWindow, QTableWidget, QTableWidgetItem, QWidget, QLabel, QLineEdit, QPushButton, QComboBox,
                             QListWidget, QTextEdit, QHBoxLayout, QVBoxLayout, QGridLayout, QDialog,
                             QMessageBox, QInputDialog, QFileDialog, QScrollArea, QFrame)
from PyQt6.QtGui import QColor, QPixmap, QAction, QIcon, QFont
from PyQt6.QtCore import Qt, QSize, QStringListModel

# --- Global Variables ---
products = {}  # Stores product data from CSV: {barcode: [{"name": "...", "price": ..., "stock": ..., "image_filename": "..."}]}
cart = []  # Stores items currently in the cart
current_item_count = 1  # Default quantity for next scanned item
current_discount = 0.0  # Default discount percentage for next scanned item
# Added global variables for cash and gcash tendered totals
total_cash_tendered = 0.0
total_gcash_tendered = 0.0
current_sales_number = 1  # For unique sales receipt numbers
current_transaction_number = 1  # For unique transaction numbers

sales_summary = {}  # Stores sales data for reporting: {barcode: {"qty_sold": ..., "revenue": ...}}

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
# --- New Global Variable for Receipts Archive ---
receipts_archive = {}  # Stores all generated receipts: {"SALES#_TRANS#": "receipt_text_content"}


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
    global products, sales_summary
    products = {}
    sales_summary = {}
    try:
        with open(PRODUCTS_CSV_FILE, mode='r', newline='', encoding='utf-8') as file:
            reader = csv.DictReader(file)
            expected_headers = ['Stock No.', 'name', 'price', 'stock', 'image_filename']
            if not reader.fieldnames or not all(field in reader.fieldnames for field in expected_headers):
                show_error("CSV Format Error", f"The '{PRODUCTS_CSV_FILE}' file has incorrect headers.\nExpected: {', '.join(expected_headers)}", parent)
                return False

            for row in reader:
                try:
                    barcode = row['Stock No.'].strip()
                    name = row['name'].strip()
                    price = float(row['price'])
                    stock = int(row['stock'])
                    image_filename = row.get('image_filename', '').strip()

                    if barcode not in products:
                        products[barcode] = []  # Initialize a list for variants

                    # Store both current stock and original stock
                    products[barcode].append({
                        "name": name,
                        "price": price,
                        "stock": stock,
                        "original_stock": stock,  # Store original stock
                        "image_filename": image_filename
                    })

                    if barcode not in sales_summary:
                        sales_summary[barcode] = {"qty_sold": 0, "revenue": 0.0}
                except (ValueError, KeyError) as e:
                    print(f"Skipping row due to data error in '{PRODUCTS_CSV_FILE}': {row} - {e}")
            if not products:
                show_warning("No Products Found", f"The '{PRODUCTS_CSV_FILE}' file is empty or contains no valid product data after filtering errors.", parent)
                return False
    except FileNotFoundError:
        show_error("File Not Found", f"The product CSV file '{PRODUCTS_CSV_FILE}' was not found.\nPlease ensure it exists in the same directory as the script with 'barcode, name, price, stock, image_filename' columns.", parent)
        return False
    except Exception as e:
        show_error("Error", f"An unexpected error occurred while loading products: {e}", parent)
        return False
    return True



def save_products_to_csv(parent=None):
    """
    Saves the current product data (including updated stock and image filename) to the CSV file.
    """
    try:
        with open(PRODUCTS_CSV_FILE, mode='w', newline='', encoding='utf-8') as file:
            fieldnames = ['Stock No.', 'name', 'price', 'stock', 'image_filename']
            writer = csv.DictWriter(file, fieldnames=fieldnames) 
            writer.writeheader()
            for barcode, variants in products.items():
                for variant in variants:
                    writer.writerow({
                        'Stock No.': barcode,
                        'name': variant['name'],
                        'price': variant['price'],
                        'stock': variant['stock'],
                        'image_filename': variant.get('image_filename', '')  # Ensure image_filename is written
                    })
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
    width_mm = 105
    height_mm = 297
    margin_left_right = 10 * mm
    margin_top_bottom = 10 * mm
    page_width = width_mm * mm
    page_height = height_mm * mm

    c = canvas.Canvas(file_path, pagesize=(page_width, page_height))

    c.setFont("Courier", 8)
    x_start = margin_left_right
    y_start = page_height - margin_top_bottom

    text_obj = c.beginText()
    text_obj.setTextOrigin(x_start, y_start)
    text_obj.setFont("Courier", 8)
    line_height = 10

    printable_width = page_width - 2 * margin_left_right
    max_chars_per_line = int(printable_width / c.stringWidth("W", "Courier", 8))

    for line in receipt_text.split("\n"):
        while len(line) > max_chars_per_line:
            segment = line[:max_chars_per_line]
            text_obj.textLine(segment)
            line = line[max_chars_per_line:]
        text_obj.textLine(line)

    c.drawText(text_obj)
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
    """Loads the inventory summary from a CSV file."""
    global products, sales_summary
    try:
        with open(INVENTORY_SUMMARY_FILE, mode='r', newline='', encoding='utf-8') as file:
            reader = csv.DictReader(file)
            for row in reader:
                barcode = row['Stock No.'].strip()
                name = row['name'].strip()
                price = float(row['price'])
                stock = int(row['stock'])
                original_stock = int(row['original_stock'])
                qty_sold = int(row['qty_sold'])
                revenue = float(row['revenue'])

                if barcode in products:
                    # Product exists, update the first variant (assuming name is consistent)
                    products[barcode][0]["stock"] = stock
                    products[barcode][0]["original_stock"] = original_stock
                else:
                    # Product doesn't exist, create a new entry
                    products[barcode] = [{
                        "name": name,
                        "price": price,
                        "stock": stock,
                        "original_stock": original_stock,
                        "image_filename": ""  # You might want to load the image filename from somewhere
                    }]

                sales_summary[barcode] = {"qty_sold": qty_sold, "revenue": revenue}
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
        self.text_edit.setFontFamily("Consolas")
        self.text_edit.setFontPointSize(10)
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

        self.btn_close = QPushButton("Close")
        self.btn_close.clicked.connect(self.close)
        btn_layout.addWidget(self.btn_close)

        layout.addLayout(btn_layout)

        self.populate_table()

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

        self.listbox.setStyleSheet("background-color: white; border: 1px solid #CCC;") # Added styling
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
        archive_menu = menubar.addMenu("Archive")
        view_archive_action = QAction("View Archived Receipts", self)
        view_archive_action.triggered.connect(self.show_archive_labels)
        archive_menu.addAction(view_archive_action)

        # Setup signals to handle selection from completer
        self.setup_product_search_signals()
        # Add this in POSMainWindow.__init__ or __init_ui__ after creating self.listbox:    
        self.listbox.setSelectionMode(QListWidget.SelectionMode.SingleSelection)  # Only single item selection allowed
        self.listbox.currentRowChanged.connect(self.display_selected_cart_item)

    def display_selected_cart_item(self, current_row):
        """
        When the user selects an item in the cart listbox, display its product info.
        """
        if current_row < 0 or current_row >= len(self.cart):
            self.clear_product_display()
            return
        item = self.cart[current_row]
        barcode = item.get('Stock No.')
        if barcode in products:
            variants = products[barcode]
            # Find variant with matching name and price (in case multiple variants)
            # Fallback to first variant if no exact match found
            variant = None
            for v in variants:
                if v['name'] == item['name']:
                    variant = v
                    break
            if variant is None:
                variant = variants[0]
            self.label_product_name_display.setText(f"Name: {item['name']}")
            self.label_product_price_display.setText(f"Price: P{item['price']:.2f}")
            self.label_product_stock_display.setText(f"Stock: {variant['stock']}")
            self.label_product_barcode_number.setText(f"Stock No.: {barcode}")
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
        self.entry_product_search.setStyleSheet("""
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
                selection-background-color: #e5e7eb;
                background-color: #ffffff;
                font-size: 20px;
            }
        """)

        # Store full product list as display strings: "Product Name (barcode)"
        self._product_search_list = [f"{variant['name']} ({barcode})" for barcode, variants in products.items() for variant in variants]

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
        for barcode, variants in products.items():
            for variant in variants:
                display_text = f"{variant['name']} ({barcode})"
                if text_lower in variant['name'].lower() or text_lower in barcode.lower():
                    filtered.append(display_text)

        self._completer_model.setStringList(filtered)

    def setup_product_search_signals(self):
        self._completer.activated.connect(self.on_product_search_selected)

    def on_product_search_selected(self, selected_text):
        # Parse barcode from selected_text, update product info display and barcode entry
        start_idx = selected_text.rfind('(')
        end_idx = selected_text.rfind(')')
        if start_idx != -1 and end_idx != -1:
            barcode = selected_text[start_idx + 1:end_idx]
            if barcode in products:
                for variant in products[barcode]:
                    # Update displays similarly as previous logic:
                    self.label_product_name_display.setText(f"PRODUCT NAME: {variant['name']}")
                    self.label_product_price_display.setText(f"PRICE: P{variant['price']:.2f}")
                    self.label_product_stock_display.setText(f"STOCK: {variant['stock']}")
                    self.label_product_barcode_number.setText(f"STOCK NO.: {barcode}")
                    self.display_product_image(variant.get('image_filename'))

                # Load barcode into the barcode entry for confirmation
                self.entry_barcode.setText(barcode)
                self.entry_barcode.setFocus()

                # Clear the product search text to keep UI clean
                self.entry_product_search.setEditText("")
            else:
                show_warning("Product Not Found", f"Product with barcode '{barcode}' not found in database.", self)
                self.clear_product_display()
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

    def handle_scan(self):
        global current_item_count, current_discount

        barcode_input = self.entry_barcode.text().strip()
        self.entry_barcode.clear()
        self.entry_product_search.setEditText("")

        # Clear previous product info display
        self.clear_product_display()

        if not barcode_input:
            return

        if barcode_input in products:
            for variant in products[barcode_input]:
                item = variant.copy()

                # Determine quantity based on Buy 1 Take 1 eligibility
                if barcode_input not in ['870-BROWN', '870-GRAY', '870-MOCHA', '871-BROWN', '871-GRAY', '871-MOCHA']:
                    qty = current_item_count * 2  # Multiply quantity by 2 for eligible items
                else:
                    qty = current_item_count    # Use quantity as set for ineligible items

                # REMOVE THIS STOCK CHECK
                # if qty > variant["stock"]:
                #     show_error("Insufficient Stock", f"Not enough stock for {item['name']}.\nAvailable: {variant['stock']} units.", self)
                #     current_item_count = 1
                #     current_discount = 0.0
                #     return

                price = item['price']
                if current_discount > 0:
                    price = price * (1 - current_discount / 100)

                item['price'] = round(price, 2)
                item['qty'] = qty
                item['Stock No.'] = barcode_input

                self.cart.append(item)
                self.listbox.addItem(f"{barcode_input} - {item['name']} x{qty} - P{item['price'] * current_item_count:.2f}")

                # Display product info and image like product search
                self.label_product_name_display.setText(f"Name: {item['name']}")
                self.label_product_price_display.setText(f"Price: P{variant['price']:.2f}")
                self.label_product_stock_display.setText(f"Stock: {variant['stock']}")  # Keep displaying stock
                self.label_product_barcode_number.setText(f"Stock No.: {barcode_input}")
                self.display_product_image(variant.get('image_filename'))

                # Reset quantity and discount after adding item
                current_item_count = 1
                current_discount = 0.0
                self.update_total()
        else:
            show_warning("Not Found", f"Barcode '{barcode_input}' not found in product database.", self)
            self.display_product_image(None)

    def update_total(self):
        total = 0
        for item in self.cart:
            qty = item.get('qty', 1)
            price = item['price']
            barcode = item.get('Stock No.')
            # Check if item is eligible for buy 1 take 1
            if barcode not in ['870-BROWN', '870-GRAY', '870-MOCHA', '871-BROWN', '871-GRAY', '871-MOCHA']:   
                # Charge only for half the qty (rounded up)
                charge_qty = (qty + 1) // 2
            else:
                charge_qty = qty
            total += price * charge_qty
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

        # ... (Existing code for stock availability, total calculation, payment, etc.) ...
        total = 0
        for item in self.cart:
            barcode = item['Stock No.']
            qty = item.get('qty', 1)
            price = item['price']

            # Check if item is eligible for Buy 1 Take 1
            if barcode not in ['870-BROWN', '870-GRAY', '870-MOCHA', '871-BROWN', '871-GRAY', '871-MOCHA']:
                # Charge only for half the quantity (rounded up)
                charge_qty = (qty + 1) // 2
            else:
                charge_qty = qty

            total += price * charge_qty  # Calculate total based on charge_qty

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

        # Generate receipt text content
        width = 50
        receipt_text_content = ""
        receipt_text_content += f"{'SUNNYWARE PHILIPPINES':^{width}}\n"
        receipt_text_content += f"{'Metro Manila, Philippines':^{width}}\n"
        receipt_text_content += f"{'-------- SALES ORDER SLIP --------':^{width}}\n"
        receipt_text_content += f"{sales_trans_line:^{width}}\n\n"
        for item in self.cart:
            name = item['name']
            barcode = item['Stock No.']
            qty = item.get('qty', 1)
            price = item['price']
            # Calculate the chargeable quantity for the receipt *for each item*
            if barcode not in ['870-BROWN', '870-GRAY', '870-MOCHA', '871-BROWN', '871-GRAY', '871-MOCHA']:
                charge_qty = (qty + 1) // 2  # Charge for half the quantity
            else:
                charge_qty = qty
            line_total_val = price * charge_qty
            line_total = f"P{line_total_val:,.2f}"
            unit_price = f"P{price:,.2f}"
            line1 = f"{name} x{qty}"
            receipt_text_content += f"{line1:<38}{line_total:>12}\n"
            receipt_text_content += f"{charge_qty}  @ {unit_price}\n\n"

        receipt_text_content += "-" * width + "\n"
        receipt_text_content += f"{'Total Amount Due:':<40} P{total:,.2f}\n"

        if payment_method == "cash and gcash":
            receipt_text_content += f"{'Cash:':<40} P{cash_amount:,.2f}\n"
            receipt_text_content += f"{'GCash:':<40} P{gcash_amount:,.2f}\n"
            total_gcash_tendered += gcash_amount
            total_cash_tendered += cash_amount
        elif payment_method == "cash only":
            receipt_text_content += f"{'Cash:':<40} P{cash_amount:,.2f}\n"
            total_cash_tendered += cash_amount
        elif payment_method == "gcash only":
            receipt_text_content += f"{'GCash:':<40} P{gcash_amount:,.2f}\n"
            total_gcash_tendered += gcash_amount
        receipt_text_content += f"{'Change:':<42} P{change:,.2f}\n"
        receipt_text_content += f"Payment Method: {payment_method.title():<34}\n"
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
            barcode = item['Stock No.']
            qty = item.get('qty', 1)

            # Initialize sales_summary[barcode] if it doesn't exist
            if barcode not in sales_summary:
                sales_summary[barcode] = {"qty_sold": 0, "revenue": 0.0}

            for variant in products[barcode]:
                variant["stock"] -= qty  # Update stock for the variant
            sales_summary[barcode]["qty_sold"] += qty
            sales_summary[barcode]["revenue"] += item['price'] * qty

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

            if barcode not in ['870-BROWN', '870-GRAY', '870-MOCHA', '871-BROWN', '871-GRAY', '871-MOCHA']:
                charge_qty = (quantity_sold + 1) // 2
            else:
                charge_qty = quantity_sold

            # Calculate price per item
            price_per_item = total_revenue / quantity_sold if quantity_sold > 0 else 0.0
            # Calculate total price based on charge quantity
            total_price = price_per_item * charge_qty

            # Set the items in the table
            self.table.setItem(row, 0, QTableWidgetItem(barcode))
            self.table.setItem(row, 1, QTableWidgetItem(product_name))
            self.table.setItem(row, 2, QTableWidgetItem(str(quantity_sold)))
            self.table.setItem(row, 3, QTableWidgetItem(f"P{price_per_item:,.2f}"))  # Price per item
            self.table.setItem(row, 4, QTableWidgetItem(f"P{total_price:,.2f}"))  # Total price based on charge quantity

            row += 1  # Increment row counter

        self.table.resizeColumnsToContents()
        self.table.resizeRowsToContents()

    def update_summary_labels(self):
        sales_data = self.parent().sales_summary
        total_quantity_sold = sum(data['qty_sold'] for data in sales_data.values())
        
        # Calculate total revenue considering the charge quantity for BOGO
        total_revenue = 0.0
        for barcode, data in sales_data.items():
            quantity_sold = data['qty_sold']
            if barcode not in ['870-BROWN', '870-GRAY', '870-MOCHA', '871-BROWN', '871-GRAY', '871-MOCHA']:
                charge_qty = (quantity_sold + 1) // 2  # BOGO logic
            else:
                charge_qty = quantity_sold  # No discount for tables
            
            # Calculate revenue based on charge quantity
            total_revenue += (data['revenue'] / quantity_sold) * charge_qty if quantity_sold > 0 else 0.0

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

                # Apply BOGO logic for charge quantity
                if barcode not in ['870-BROWN', '870-GRAY', '870-MOCHA', '871-BROWN', '871-GRAY', '871-MOCHA']:
                    charge_qty = (qty_sold + 1) // 2  # Calculate how many items the customer pays for
                else:
                    charge_qty = qty_sold  # No discount for tables

                # Calculate price per item
                price_per_item = revenue / qty_sold if qty_sold > 0 else 0.0
                total_price = price_per_item * charge_qty

                rows.append({
                    "STOCK #": barcode,
                    "Product Name": product_name,
                    "Quantity Sold": qty_sold,
                    "Price": price_per_item,
                    "Total Revenue": total_price  # Use total price based on charge quantity
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

                # Apply BOGO logic for charge quantity
                if barcode not in ['870-BROWN', '870-GRAY', '870-MOCHA', '871-BROWN', '871-GRAY', '871-MOCHA']:
                    charge_qty = (qty_sold + 1) // 2  # BOGO logic
                else:
                    charge_qty = qty_sold  # No discount for tables

                # Calculate price per item and total revenue based on charge quantity
                price_per_item = revenue / qty_sold if qty_sold > 0 else 0
                total_price = price_per_item * charge_qty
                data.append([
                    barcode,
                    product_name,
                    str(qty_sold),
                    f"P{price_per_item:,.2f}",
                    f"P{total_price:,.2f}"
                ])

                total_quantity_sold += qty_sold

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
        self.text_edit.setFontFamily("Consolas")
        self.text_edit.setFontPointSize(10)
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
    width_mm = 105
    height_mm = 297
    margin_left_right = 10 * mm
    margin_top_bottom = 10 * mm
    page_width = width_mm * mm
    page_height = height_mm * mm

    with tempfile.NamedTemporaryFile(delete=False, suffix=".pdf") as temp_pdf:
        temp_pdf_path = temp_pdf.name

    c = canvas.Canvas(temp_pdf_path, pagesize=(page_width, page_height))

    c.setFont("Courier", 8)
    x_start = margin_left_right
    y_start = page_height - margin_top_bottom

    text_obj = c.beginText()
    text_obj.setTextOrigin(x_start, y_start)
    text_obj.setFont("Courier", 8)
    line_height = 10

    printable_width = page_width - 2 * margin_left_right
    max_chars_per_line = int(printable_width / c.stringWidth("W", "Courier", 8))

    for line in receipt_text.split("\n"):
        while len(line) > max_chars_per_line:
            segment = line[:max_chars_per_line]
            text_obj.textLine(segment)
            line = line[max_chars_per_line:]
        text_obj.textLine(line)

    c.drawText(text_obj)
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
    # Ensure image folder exists
    os.makedirs(PRODUCT_IMAGE_FOLDER, exist_ok=True)

    if not load_products_from_csv():
        # Error shown inside load_products_from_csv function
        sys.exit()

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