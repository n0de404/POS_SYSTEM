import sys
import os
import csv
import json
import mysql.connector
from mysql.connector import Error
from werkzeug.security import generate_password_hash

# --- DATABASE CONFIGURATION ---
# IMPORTANT: Fill in your MySQL database details here!
# This MUST match the details in POS_SYSTEM_MYSQL.py
DB_CONFIG = {
    'host': 'localhost',
    'user': 'user',       # <-- TODO: Update this
    'password': 'philtop', # <-- TODO: Update this
    'database': 'pos_db'             # <-- The database you created
}
# --- END DATABASE CONFIGURATION ---

# --- File Paths (Constants) ---
# Assumes files are in the same directory as this script
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
USERS_FILE = os.path.join(BASE_DIR, 'users.txt')
PRODUCTS_FILE = os.path.join(BASE_DIR, 'POSProducts.csv')
PROMO_INV_FILE = os.path.join(BASE_DIR, 'PromoInventory.csv')
PROMO_BUNDLES_FILE = os.path.join(BASE_DIR, 'PromoBundles.json')
BASKET_PROMOS_FILE = os.path.join(BASE_DIR, 'BasketPromos.json')

# Files we are NOT migrating (they are derived from sales):
# - inventory_summary.csv
# - sales_summary.json
# - receipts_archive.json
# - tendered_amounts.json

def get_db_connection():
    """Establishes a connection to the MySQL database."""
    try:
        conn = mysql.connector.connect(**DB_CONFIG)
        return conn
    except Error as e:
        print(f"[ERROR] Error connecting to MySQL database: {e}")
        return None

def migrate_users(conn):
    """Migrates users from users.txt to the 'users' table with hashed passwords."""
    print("Starting user migration...")
    if not os.path.exists(USERS_FILE):
        print(f"[WARN] {USERS_FILE} not found. Skipping user migration.")
        return

    try:
        with open(USERS_FILE, 'r') as f:
            lines = f.readlines()
        
        with conn.cursor() as cursor:
            insert_query = """
                INSERT INTO users (username, password_hash, is_admin)
                VALUES (%s, %s, %s)
                ON DUPLICATE KEY UPDATE 
                    password_hash = VALUES(password_hash),
                    is_admin = VALUES(is_admin)
            """
            
            count = 0
            for line in lines:
                line = line.strip()
                if not line:
                    continue
                
                try:
                    # Check for admin flag
                    parts = line.split(',')
                    username = parts[0]
                    password = parts[1]
                    is_admin = False
                    if len(parts) > 2 and parts[2].lower() == 'admin':
                        is_admin = True

                    password_hash = generate_password_hash(password)
                    cursor.execute(insert_query, (username, password_hash, is_admin))
                    print(f"  Migrated user: {username}")
                    count += 1
                except (ValueError, IndexError):
                    print(f"  [WARN] Skipping malformed line in users.txt: {line}")
            
            conn.commit()
            print(f"[SUCCESS] Migrated {count} users.")

    except Exception as e:
        conn.rollback()
        print(f"[ERROR] Failed to migrate users: {e}")

def migrate_promo_types(conn):
    """Migrates data from PromoInventory.csv to 'promo_types' table."""
    print("Starting promo types migration...")
    if not os.path.exists(PROMO_INV_FILE):
        print(f"[WARN] {PROMO_INV_FILE} not found. Skipping promo types migration.")
        return

    try:
        with open(PROMO_INV_FILE, mode='r', encoding='utf-8') as f:
            reader = csv.DictReader(f)
            promos = list(reader)
        
        with conn.cursor() as cursor:
            insert_query = """
                INSERT INTO promo_types (promo_code, units_per_sale, name)
                VALUES (%s, %s, %s)
                ON DUPLICATE KEY UPDATE 
                    units_per_sale = VALUES(units_per_sale), 
                    name = VALUES(name)
            """
            
            count = 0
            for promo in promos:
                try:
                    code = promo['promo_code']
                    units = int(promo['units_per_sale'])
                    # Use 'name' column if it exists, otherwise default to 'promo_code'
                    name = promo.get('name', code) 
                    
                    cursor.execute(insert_query, (code, units, name))
                    print(f"  Migrated promo type: {code}")
                    count += 1
                except (KeyError, ValueError, TypeError) as e:
                    print(f"  [WARN] Skipping malformed row in PromoInventory.csv: {promo} - Error: {e}")
            
            conn.commit()
            print(f"[SUCCESS] Migrated {count} promo types.")

    except Exception as e:
        conn.rollback()
        print(f"[ERROR] Failed to migrate promo types: {e}")

def migrate_products(conn):
    """Migrates data from POSProducts.csv to 'products' and 'product_promotions' tables."""
    print("Starting product migration...")
    if not os.path.exists(PRODUCTS_FILE):
        print(f"[ERROR] {PRODUCTS_FILE} not found. Cannot migrate products.")
        return

    try:
        # Use 'utf-8-sig' to handle the BOM (Byte Order Mark)
        # that sometimes appears in CSVs from Excel
        with open(PRODUCTS_FILE, mode='r', encoding='utf-8-sig') as f:
            reader = csv.DictReader(f)
            products = list(reader)
        
        with conn.cursor() as cursor:
            product_insert_query = """
                INSERT INTO products (stock_no, name, price, stock, image_filename)
                VALUES (%s, %s, %s, %s, %s)
                ON DUPLICATE KEY UPDATE 
                    name = VALUES(name), 
                    price = VALUES(price), 
                    stock = VALUES(stock), 
                    image_filename = VALUES(image_filename)
            """
            promo_insert_query = """
                INSERT INTO product_promotions (product_id, promo_code)
                VALUES (%s, %s)
                ON DUPLICATE KEY UPDATE 
                    product_id = VALUES(product_id), 
                    promo_code = VALUES(promo_code)
            """
            
            # Get existing promo codes from DB
            cursor.execute("SELECT promo_code FROM promo_types")
            valid_promo_codes = {row[0] for row in cursor.fetchall()}
            print(f"  Valid promo codes found in DB: {valid_promo_codes}")
            
            product_count = 0
            promo_count = 0
            
            for prod in products:
                try:
                    stock_no = prod['Stock No.']
                    if not stock_no:
                        print(f"  [WARN] Skipping row with empty Stock No.: {prod}")
                        continue
                        
                    name = prod['name']
                    price = float(prod['price'])
                    stock = int(prod['stock'])
                    image = prod.get('image_filename') or None
                    
                    # 1. Insert product
                    cursor.execute(product_insert_query, (stock_no, name, price, stock, image))
                    product_id = cursor.lastrowid
                    
                    # If product already existed (lastrowid=0), get its ID
                    if product_id == 0:
                        cursor.execute("SELECT product_id FROM products WHERE stock_no = %s", (stock_no,))
                        result = cursor.fetchone()
                        if result:
                            product_id = result[0]
                        else:
                            print(f"  [ERROR] Could not find product_id for existing stock_no {stock_no}. Skipping promos for this item.")
                            continue
                        
                    print(f"  Migrated product: {stock_no} - {name}")
                    product_count += 1
                    
                    # 2. Insert promos
                    # Find promo columns (like 'B1T1', 'B3T1')
                    for promo_code in valid_promo_codes:
                        if promo_code in prod and prod[promo_code]: # Check if column exists and has a value
                            try:
                                cursor.execute(promo_insert_query, (product_id, promo_code))
                                print(f"    - Added promo: {promo_code}")
                                promo_count += 1
                            except mysql.connector.Error as e:
                                # This will catch violations of the UNIQUE key
                                print(f"    - [WARN] Could not add promo {promo_code} to {stock_no} (may already exist): {e}")
                            
                except (KeyError, ValueError, TypeError) as e:
                    print(f"  [WARN] Skipping malformed row in POSProducts.csv: {prod} - Error: {e}")
            
            conn.commit()
            print(f"[SUCCESS] Migrated {product_count} products and {promo_count} product promotions.")

    except Exception as e:
        conn.rollback()
        print(f"[ERROR] Failed to migrate products: {e}")

def migrate_bundles(conn):
    """Migrates data from PromoBundles.json to 'bundles' and 'bundle_components' tables."""
    print("Starting bundle migration...")
    if not os.path.exists(PROMO_BUNDLES_FILE):
        print(f"[WARN] {PROMO_BUNDLES_FILE} not found. Skipping bundle migration.")
        return

    try:
        with open(PROMO_BUNDLES_FILE, 'r', encoding='utf-8') as f:
            bundles_data = json.load(f)
        
        with conn.cursor() as cursor:
            bundle_insert_query = """
                INSERT INTO bundles (bundle_code, name, price, sku)
                VALUES (%s, %s, %s, %s)
                ON DUPLICATE KEY UPDATE 
                    name = VALUES(name), 
                    price = VALUES(price), 
                    sku = VALUES(sku)
            """
            component_insert_query = """
                INSERT INTO bundle_components (bundle_id, product_stock_no, variant_index, quantity)
                VALUES (%s, %s, %s, %s)
            """
            
            bundle_count = 0
            component_count = 0
            
            for bundle_code, bundle in bundles_data.items():
                try:
                    # 1. Insert bundle
                    cursor.execute(bundle_insert_query, (
                        bundle['code'], bundle['name'], float(bundle['price']), bundle['sku']
                    ))
                    bundle_id = cursor.lastrowid
                    
                    # If it existed, get its ID
                    if bundle_id == 0:
                        cursor.execute("SELECT bundle_id FROM bundles WHERE bundle_code = %s", (bundle['code'],))
                        bundle_id = cursor.fetchone()[0]
                    
                    print(f"  Migrated bundle: {bundle['code']}")
                    bundle_count += 1
                    
                    # 2. Delete old components for this bundle (to allow re-runs)
                    cursor.execute("DELETE FROM bundle_components WHERE bundle_id = %s", (bundle_id,))
                    
                    # 3. Insert new components
                    components_to_insert = []
                    for comp in bundle['components']:
                        components_to_insert.append((
                            bundle_id,
                            comp['barcode'],
                            int(comp['variant_index']),
                            int(comp['quantity'])
                        ))
                    
                    cursor.executemany(component_insert_query, components_to_insert)
                    print(f"    - Added {len(components_to_insert)} components")
                    component_count += len(components_to_insert)

                except (KeyError, ValueError, TypeError) as e:
                    print(f"  [WARN] Skipping malformed bundle in PromoBundles.json: {bundle_code} - Error: {e}")
            
            conn.commit()
            print(f"[SUCCESS] Migrated {bundle_count} bundles and {component_count} components.")

    except Exception as e:
        conn.rollback()
        print(f"[ERROR] Failed to migrate bundles: {e}")

def migrate_basket_promos(conn):
    """Migrates data from BasketPromos.json to 'basket_promos' and 'basket_promo_freebies' tables."""
    print("Starting basket promo migration...")
    if not os.path.exists(BASKET_PROMOS_FILE):
        print(f"[WARN] {BASKET_PROMOS_FILE} not found. Skipping basket promo migration.")
        return
        
    try:
        with open(BASKET_PROMOS_FILE, 'r', encoding='utf-8') as f:
            promo_data = json.load(f)
        
        tiers = promo_data.get('tiers', [])
        if not tiers:
            print("[INFO] No tiers found in BasketPromos.json. Skipping.")
            return

        with conn.cursor() as cursor:
            promo_insert_query = """
                INSERT INTO basket_promos (code, name, threshold, message)
                VALUES (%s, %s, %s, %s)
                ON DUPLICATE KEY UPDATE 
                    code = VALUES(code), 
                    threshold = VALUES(threshold), 
                    message = VALUES(message)
            """
            
            # Use name as the unique key for lookup
            promo_lookup_query = "SELECT promo_id FROM basket_promos WHERE name = %s"

            freebie_insert_query = """
                INSERT INTO basket_promo_freebies (promo_id, product_stock_no, variant_index, quantity)
                VALUES (%s, %s, %s, %s)
            """
            
            promo_count = 0
            freebie_count = 0
            
            for tier in tiers:
                try:
                    # 1. Insert promo tier
                    cursor.execute(promo_insert_query, (
                        tier['code'], tier['name'], float(tier['threshold']), tier['message']
                    ))
                    promo_id = cursor.lastrowid
                    
                    # If it existed, get its ID
                    if promo_id == 0:
                        cursor.execute(promo_lookup_query, (tier['name'],))
                        result = cursor.fetchone()
                        if result:
                            promo_id = result[0]
                        else:
                            print(f"  [ERROR] Could not find promo_id for existing tier {tier['name']}")
                            continue

                    print(f"  Migrated basket promo: {tier['name']}")
                    promo_count += 1
                    
                    # 2. Delete old freebies (to allow re-runs)
                    cursor.execute("DELETE FROM basket_promo_freebies WHERE promo_id = %s", (promo_id,))
                    
                    # 3. Insert new freebies
                    freebies_to_insert = []
                    for freebie in tier['freebies']:
                        freebies_to_insert.append((
                            promo_id,
                            freebie['barcode'],
                            int(freebie['variant_index']),
                            int(freebie['quantity'])
                        ))
                    
                    cursor.executemany(freebie_insert_query, freebies_to_insert)
                    print(f"    - Added {len(freebies_to_insert)} freebies")
                    freebie_count += len(freebies_to_insert)

                except (KeyError, ValueError, TypeError) as e:
                    print(f"  [WARN] Skipping malformed tier in BasketPromos.json: {tier.get('name', 'N/A')} - Error: {e}")
            
            conn.commit()
            print(f"[SUCCESS] Migrated {promo_count} basket promos and {freebie_count} freebies.")
            
    except Exception as e:
        conn.rollback()
        print(f"[ERROR] Failed to migrate basket promos: {e}")

def main():
    print("--- Starting Data Migration to MySQL ---")
    
    conn = get_db_connection()
    if not conn:
        print("[FATAL] Could not connect to database. Aborting migration.")
        sys.exit(1)
        
    print(f"Successfully connected to database '{DB_CONFIG['database']}' on '{DB_CONFIG['host']}'.")
    
    try:
        # Run migrations in order
        migrate_users(conn)
        migrate_promo_types(conn)
        migrate_products(conn)
        migrate_bundles(conn)
        migrate_basket_promos(conn)
        
        print("\n--- Data Migration Complete! ---")
        print("Please review any [WARN] messages above.")
        print("Your data should now be in the MySQL database.")

    except Exception as e:
        print(f"\n[FATAL] An unexpected error occurred: {e}")
    finally:
        if conn.is_connected():
            conn.close()
            print("Database connection closed.")

if __name__ == "__main__":
    main()

