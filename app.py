import streamlit as st
import folium
from streamlit_folium import st_folium
import requests
import pandas as pd
import math
import sqlite3
import hashlib
import time
from datetime import datetime, timezone
from concurrent.futures import ThreadPoolExecutor, as_completed

# ==============================================================================
# 1. API & PAYMENT GATEWAY CONFIGURATION (ADD YOUR KEYS HERE Or IN ST.SECRETS)
# ==============================================================================
GOOGLE_MAPS_API_KEY = "YOUR_GOOGLE_MAPS_API_KEY_HERE"

# Razorpay Payment Gateway Credentials (Get from dashboard.razorpay.com)
RAZORPAY_KEY_ID = "YOUR_RAZORPAY_KEY_ID_HERE"          # e.g., "rzp_test_1234567890"
RAZORPAY_KEY_SECRET = "YOUR_RAZORPAY_KEY_SECRET_HERE"  # e.g., "secret_abcdef12345"
PRO_PLAN_PRICE_INR = 499                               # One-time / Monthly Pro unlock price (₹)
FREE_TRIAL_MINUTES = 15                                # Strict 15-minute trial limit

# Optional: Free OpenRouteService Key for road isochrones
ORS_API_KEY = ""

# ==============================================================================
# 2. PAGE SETUP
# ==============================================================================
st.set_page_config(
    page_title="Business Buddy — Hyperlocal Site Selection & Sales Target SaaS",
    page_icon="🤝",
    layout="wide"
)

# ==============================================================================
# 3. DATABASE INITIALIZATION (USERS, IP/DEVICE LOCKS & SAVED ZONES)
# ==============================================================================
DB_FILE = "business_buddy_vault.db"

def init_db():
    conn = sqlite3.connect(DB_FILE)
    c = conn.cursor()
    # Table 1: Saved Location Scans
    c.execute("""
        CREATE TABLE IF NOT EXISTS saved_zones (
            zone_id TEXT PRIMARY KEY,
            user_email TEXT,
            zone_label TEXT,
            lat REAL,
            lon REAL,
            radius_km REAL,
            overall_buddy_score INTEGER,
            affluence_score INTEGER,
            retail_maturity_score INTEGER,
            demand_score INTEGER,
            competition_saturation INTEGER,
            total_pois INTEGER,
            food_outlets INTEGER,
            housing_clusters INTEGER,
            anchor_brands_count INTEGER,
            est_zone_daily_orders INTEGER,
            pred_m1_orders INTEGER,
            pred_m6_orders INTEGER,
            pred_m6_rev REAL,
            scanned_at TEXT
        )
    """)
    # Table 2: Trial Enforcement by Email, IP Address & Device Fingerprint Hash
    c.execute("""
        CREATE TABLE IF NOT EXISTS users_trial_ledger (
            email TEXT PRIMARY KEY,
            auth_provider TEXT,
            client_ip TEXT,
            device_hash TEXT,
            trial_start_epoch REAL,
            is_paid INTEGER DEFAULT 0,
            payment_id TEXT DEFAULT ''
        )
    """)
    conn.commit()
    conn.close()

init_db()

# ==============================================================================
# 4. CLIENT IP, DEVICE FINGERPRINT & 15-MIN TRIAL ENFORCEMENT ENGINE
# ==============================================================================
def get_client_ip_and_device_hash():
    """Extracts visitor IP and browser hardware/header fingerprint hash."""
    headers = {}
    try:
        headers = dict(st.context.headers)
    except Exception:
        pass

    # 1. Resolve Real Client IP from Proxy Headers or Public IP Reflector
    forwarded_for = headers.get("X-Forwarded-For") or headers.get("x-forwarded-for")
    real_ip = headers.get("X-Real-Ip") or headers.get("x-real-ip")
    if forwarded_for:
        client_ip = forwarded_for.split(",")[0].strip()
    elif real_ip:
        client_ip = real_ip.strip()
    else:
        try:
            client_ip = requests.get("https://api.ipify.org", timeout=2).text.strip()
        except Exception:
            client_ip = "127.0.0.1"

    # 2. Compute Hardware/Browser Fingerprint (Since browsers block raw MAC addresses)
    ua = headers.get("User-Agent") or headers.get("user-agent") or "unknown-ua"
    lang = headers.get("Accept-Language") or headers.get("accept-language") or "en"
    sec_ch = headers.get("Sec-Ch-Ua-Platform") or headers.get("sec-ch-ua-platform") or "os"
    raw_fingerprint = f"{client_ip}|{ua}|{lang}|{sec_ch}"
    device_hash = hashlib.sha256(raw_fingerprint.encode("utf-8")).hexdigest()[:20]

    return client_ip, device_hash


def register_or_verify_user(email, provider, client_ip, device_hash):
    """
    Checks if this Email, IP, or Device Hash has already started a trial.
    If IP or Device Hash already exists under a different email, inherits the OLDEST
    trial start timestamp so users cannot bypass the 15-minute limit with multiple emails!
    """
    now_epoch = time.time()
    conn = sqlite3.connect(DB_FILE)
    c = conn.cursor()

    # Check if ANY account has already used this IP or Device Hash
    c.execute("""
        SELECT MIN(trial_start_epoch), MAX(is_paid)
        FROM users_trial_ledger
        WHERE email = ? OR client_ip = ? OR device_hash = ?
    """, (email, client_ip, device_hash))
    row = c.fetchone()

    earliest_start = row[0] if (row and row[0] is not None) else now_epoch
    already_paid = int(row[1]) if (row and row[1] is not None) else 0

    # Check if exact email exists
    c.execute("SELECT email, is_paid, trial_start_epoch FROM users_trial_ledger WHERE email = ?", (email,))
    user_row = c.fetchone()

    if not user_row:
        c.execute("""
            INSERT INTO users_trial_ledger (email, auth_provider, client_ip, device_hash, trial_start_epoch, is_paid)
            VALUES (?, ?, ?, ?, ?, ?)
        """, (email, provider, client_ip, device_hash, earliest_start, already_paid))
        conn.commit()
        effective_start = earliest_start
        is_paid = already_paid
    else:
        # Enforce the earliest timestamp seen across their IP/Device
        effective_start = min(float(user_row[2]), float(earliest_start))
        is_paid = max(int(user_row[1]), already_paid)
        c.execute("""
            UPDATE users_trial_ledger
            SET trial_start_epoch = ?, client_ip = ?, device_hash = ?, is_paid = ?
            WHERE email = ?
        """, (effective_start, client_ip, device_hash, is_paid, email))
        conn.commit()

    conn.close()
    elapsed_seconds = now_epoch - effective_start
    remaining_seconds = max(0, int((FREE_TRIAL_MINUTES * 60) - elapsed_seconds))
    return is_paid == 1, remaining_seconds


def mark_user_paid(email, client_ip, device_hash, payment_id):
    conn = sqlite3.connect(DB_FILE)
    c = conn.cursor()
    c.execute("""
        UPDATE users_trial_ledger
        SET is_paid = 1, payment_id = ?
        WHERE email = ? OR client_ip = ? OR device_hash = ?
    """, (payment_id, email, client_ip, device_hash))
    conn.commit()
    conn.close()


# ==============================================================================
# 5. RAZORPAY PAYMENT LINK & ORDER VERIFICATION HELPERS
# ==============================================================================
def create_razorpay_payment_link(email, amount_inr, key_id, key_secret):
    """Creates a live hosted Razorpay Payment Link via REST API."""
    url = "https://api.razorpay.com/v1/payment_links"
    payload = {
        "amount": int(amount_inr * 100),  # In paise
        "currency": "INR",
        "description": "Business Buddy Pro — Unlimited Lifetime Access",
        "customer": {"email": email},
        "notify": {"email": True},
        "reminder_enable": True
    }
    resp = requests.post(url, auth=(key_id, key_secret), json=payload, timeout=10)
    return resp.status_code, resp.json()


def verify_razorpay_payment(payment_id, key_id, key_secret):
    """Verifies a Razorpay Payment ID (`pay_...`) directly against Razorpay servers."""
    url = f"https://api.razorpay.com/v1/payments/{payment_id.strip()}"
    resp = requests.get(url, auth=(key_id, key_secret), timeout=10)
    if resp.status_code == 200:
        data = resp.json()
        if data.get("status") in ["captured", "authorized"]:
            return True, "Payment Verified!"
        return False, f"Payment status is '{data.get('status')}'. Must be captured."
    return False, "Invalid Payment ID or Razorpay credentials."


# ==============================================================================
# 6. SOCIAL LOGIN GATEWAY PAGE
# ==============================================================================
if "auth_email" not in st.session_state:
    st.session_state.auth_email = None
    st.session_state.auth_provider = None

# Support Native Streamlit OIDC Login if configured in secrets.toml
if hasattr(st, "user") and getattr(st.user, "is_logged_in", False):
    st.session_state.auth_email = getattr(st.user, "email", "oidc_user@gmail.com")
    st.session_state.auth_provider = "Google OIDC"

if not st.session_state.auth_email:
    st.markdown("<h1 style='text-align:center;'>🤝 Welcome to Business Buddy</h1>", unsafe_allow_html=True)
    st.markdown("<p style='text-align:center; font-size:18px;'>Hyperlocal Hex-Grid, Affluence & Sales Target Intelligence Platform</p>", unsafe_allow_html=True)
    st.write("")

    _, login_col, _ = st.columns([1, 1.3, 1])
    with login_col:
        with st.container(border=True):
            st.subheader("🔐 Sign In to Start Your 15-Minute Free Trial")
            st.caption("Strict 1-Trial Policy: Limited to 15 minutes per User, IP Address, and Device Fingerprint.")

            # Option A: Native Google OAuth via Streamlit OIDC (if configured in .streamlit/secrets.toml)
            if st.button("🌐 Continue with Google (OAuth 2.0)", type="primary", use_container_width=True):
                if hasattr(st, "login"):
                    try:
                        st.login()
                    except Exception:
                        st.info("Tip: To use production Google OAuth redirect, add `[auth]` Google client credentials in `.streamlit/secrets.toml`, or use Instant Social Login below for testing.")
                else:
                    st.info("Configure `[auth]` in `.streamlit/secrets.toml` or sign in below.")

            st.divider()
            st.markdown("**Instant Social / Work Email Sign-In**")
            provider_choice = st.selectbox("Select Identity Provider", ["Google Workspace / Gmail", "LinkedIn", "GitHub"])
            email_input = st.text_input("Enter Your Email Address", placeholder="founder@company.com")

            if st.button("🚀 Start My 15-Minute Free Trial", use_container_width=True):
                if "@" in email_input and "." in email_input.split("@")[-1]:
                    st.session_state.auth_email = email_input.strip().lower()
                    st.session_state.auth_provider = provider_choice
                    st.rerun()
                else:
                    st.error("Please enter a valid email address.")
    st.stop()


# ==============================================================================
# 7. ENFORCE 15-MIN TRIAL & PAYWALL GATE
# ==============================================================================
client_ip, device_hash = get_client_ip_and_device_hash()
is_paid_user, remaining_secs = register_or_verify_user(
    st.session_state.auth_email,
    st.session_state.auth_provider,
    client_ip,
    device_hash
)

mins_left = remaining_secs // 60
secs_left = remaining_secs % 60

# Top Status Banner
top_c1, top_c2, top_c3, top_c4 = st.columns([2, 1.5, 1.5, 1])
top_c1.markdown(f"👤 **User:** `{st.session_state.auth_email}` ({st.session_state.auth_provider})")
top_c2.markdown(f"🌐 **IP / Device Lock:** `{client_ip}` (`{device_hash[:8]}...`)")

if is_paid_user:
    top_c3.success("💎 **PRO UNLIMITED ACTIVE**")
else:
    if remaining_secs > 0:
        top_c3.warning(f"⏳ **Free Trial Left:** `{mins_left:02d}m : {secs_left:02d}s`")
    else:
        top_c3.error("🔒 **Free Trial Expired (00:00)**")

if top_c4.button("Log Out", use_container_width=True):
    st.session_state.auth_email = None
    if hasattr(st, "logout"):
        try:
            st.logout()
        except Exception:
            pass
    st.rerun()

st.divider()

# IF TRIAL EXPIRED AND NOT PAID -> SHOW FULL-SCREEN PAYMENT GATEWAY PAYWALL
if not is_paid_user and remaining_secs <= 0:
    st.error("### ⏰ Your 15-Minute Free Trial Has Ended")
    st.markdown(
        f"Our system recorded that user **`{st.session_state.auth_email}`** "
        f"(or device/IP **`{client_ip}`**) has completed the 15-minute complimentary evaluation of **Business Buddy**."
    )

    p_col1, p_col2 = st.columns([1.2, 1])
    with p_col1:
        with st.container(border=True):
            st.subheader(f"💳 Unlock Business Buddy Pro — ₹{PRO_PLAN_PRICE_INR}")
            st.markdown("""
            * ✅ **Unlimited 9-Grid Hexagonal Deep Scans** across any city or sector
            * ✅ **Unlimited 2-Wheeler Delivery Isochrone Mapping**
            * ✅ **Full Competitor Order Velocity & CSV Exports**
            * ✅ **Permanent Multi-Location SQLite Vault Access**
            """)

            rzp_id = st.secrets.get("RAZORPAY_KEY_ID", RAZORPAY_KEY_ID)
            rzp_secret = st.secrets.get("RAZORPAY_KEY_SECRET", RAZORPAY_KEY_SECRET)

            if rzp_id != "YOUR_RAZORPAY_KEY_ID_HERE" and rzp_secret != "YOUR_RAZORPAY_KEY_SECRET_HERE":
                if st.button(f"⚡ Generate Razorpay Checkout Link (₹{PRO_PLAN_PRICE_INR})", type="primary", use_container_width=True):
                    code, rzp_data = create_razorpay_payment_link(
                        st.session_state.auth_email, PRO_PLAN_PRICE_INR, rzp_id, rzp_secret
                    )
                    if code in [200, 201] and rzp_data.get("short_url"):
                        st.success(f"**Click Here to Pay Securely via UPI / Card:** [Open Razorpay Checkout]({rzp_data['short_url']})")
                        st.caption(f"Reference Link ID: `{rzp_data.get('id')}` — Copy your `pay_...` ID after payment and verify on the right.")
                    else:
                        st.error(f"Razorpay Error: {rzp_data}")
            else:
                st.info("Configure `RAZORPAY_KEY_ID` and `RAZORPAY_KEY_SECRET` at the top of `app.py` to generate live UPI/Card payment links.")

    with p_col2:
        with st.container(border=True):
            st.subheader("✅ Verify Payment & Unlock Immediately")
            payment_id_input = st.text_input("Enter Razorpay Payment ID (`pay_...`) or Promo Code", placeholder="pay_P9x8123456789")
            if st.button("🔓 Verify & Unlock Pro Account", use_container_width=True):
                rzp_id = st.secrets.get("RAZORPAY_KEY_ID", RAZORPAY_KEY_ID)
                rzp_secret = st.secrets.get("RAZORPAY_KEY_SECRET", RAZORPAY_KEY_SECRET)

                # Admin / Founder Test Bypass Code for local testing: "FOUNDER_PRO_2026"
                if payment_id_input.strip() == "FOUNDER_PRO_2026":
                    mark_user_paid(st.session_state.auth_email, client_ip, device_hash, "ADMIN_BYPASS")
                    st.success("Founder Pro Override Activated! Reloading...")
                    time.sleep(1)
                    st.rerun()
                elif rzp_id != "YOUR_RAZORPAY_KEY_ID_HERE":
                    ok, msg = verify_razorpay_payment(payment_id_input, rzp_id, rzp_secret)
                    if ok:
                        mark_user_paid(st.session_state.auth_email, client_ip, device_hash, payment_id_input.strip())
                        st.success(msg)
                        time.sleep(1)
                        st.rerun()
                    else:
                        st.error(msg)
                else:
                    st.warning("Enter a valid Razorpay Payment ID (or use `FOUNDER_PRO_2026` to test unlocking locally).")

    st.stop()


# ==============================================================================
# 8. BUSINESS BUDDY TAXONOMY & ANCHOR BRAND DICTIONARY
# ==============================================================================
PREDEFINED_CATEGORIES = {
    "🍽️ Food & Beverage (QSR, Dining, Cloud Kitchens)": [
        "restaurant", "fast_food_restaurant", "meal_takeaway",
        "meal_delivery", "cafe", "bakery", "indian_restaurant", "coffee_shop"
    ],
    "🏘️ Residential & High-Density Housing": [
        "apartment_complex", "housing_complex", "condominium_complex",
        "apartment_building", "guest_house", "hostel"
    ],
    "💎 Affluence & Lifestyle Proxies (Gyms, Spas, Malls, Wealth)": [
        "gym", "fitness_center", "spa", "shopping_mall",
        "supermarket", "department_store", "jewelry_store", "bank"
    ],
    "🏢 Corporate, IT & Commercial Hubs": [
        "corporate_office", "coworking_space", "accounting",
        "insurance_agency", "real_estate_agency"
    ],
    "🏥 Healthcare & Hospitals": [
        "hospital", "medical_lab", "doctor", "dental_clinic", "pharmacy"
    ],
    "🎓 Education, Colleges & Hostels": [
        "university", "school", "secondary_school", "library"
    ]
}

ANCHOR_BRANDS = [
    "starbucks", "domino", "mcdonald", "kfc", "burger king", "subway",
    "haldiram", "bikanervala", "barbeque nation", "punjab grill", "chaayos",
    "third wave", "blue tokai", "cult.fit", "gold's gym", "anytime fitness",
    "apollo", "max hospital", "fortis", "reliance", "dmart", "zudio",
    "westside", "shoppers stop", "hdfc", "icici", "axis bank", "sbi",
    "tanishq", "lenskart", "nykaa", "decathlon", "pizza hut", "la pino"
]

PRICE_TIER_WEIGHTS = {
    "PRICE_LEVEL_FREE": 1,
    "PRICE_LEVEL_INEXPENSIVE": 1,
    "PRICE_LEVEL_MODERATE": 2.5,
    "PRICE_LEVEL_EXPENSIVE": 4.5,
    "PRICE_LEVEL_VERY_EXPENSIVE": 5.0
}

def save_zone_to_db(summary_dict):
    conn = sqlite3.connect(DB_FILE)
    c = conn.cursor()
    c.execute("""
        INSERT OR REPLACE INTO saved_zones VALUES (
            :zone_id, :user_email, :zone_label, :lat, :lon, :radius_km,
            :overall_buddy_score, :affluence_score, :retail_maturity_score,
            :demand_score, :competition_saturation, :total_pois,
            :food_outlets, :housing_clusters, :anchor_brands_count,
            :est_zone_daily_orders, :pred_m1_orders, :pred_m6_orders,
            :pred_m6_rev, :scanned_at
        )
    """, summary_dict)
    conn.commit()
    conn.close()

def load_saved_zones(user_email):
    conn = sqlite3.connect(DB_FILE)
    df = pd.read_sql_query(
        "SELECT * FROM saved_zones WHERE user_email = ? ORDER BY overall_buddy_score DESC",
        conn,
        params=(user_email,)
    )
    conn.close()
    return df

# ==============================================================================
# 9. GEOSPATIAL, ISOCHRONE & MICRO-GRID ENGINE
# ==============================================================================
def haversine_km(lat1, lon1, lat2, lon2):
    R = 6371.0
    dlat = math.radians(lat2 - lat1)
    dlon = math.radians(lon2 - lon1)
    a = (
        math.sin(dlat / 2) ** 2
        + math.cos(math.radians(lat1))
        * math.cos(math.radians(lat2))
        * math.sin(dlon / 2) ** 2
    )
    return R * 2 * math.atan2(math.sqrt(a), math.sqrt(1 - a))


def build_9_micro_sectors(lat, lon, radius_km):
    sub_radius_m = max(550.0, (radius_km * 1000.0) * 0.44)
    d_lat = (radius_km * 0.54) / 111.0
    d_lon = (radius_km * 0.54) / (111.0 * math.cos(math.radians(lat)))

    offsets = [
        ("Center Core", 0, 0),
        ("North Sector", d_lat, 0),
        ("North-East Sector", d_lat * 0.75, d_lon * 0.75),
        ("East Sector", 0, d_lon),
        ("South-East Sector", -d_lat * 0.75, d_lon * 0.75),
        ("South Sector", -d_lat, 0),
        ("South-West Sector", -d_lat * 0.75, -d_lon * 0.75),
        ("West Sector", 0, -d_lon),
        ("North-West Sector", d_lat * 0.75, -d_lon * 0.75),
    ]

    cells = []
    hex_r_lat = d_lat * 0.46
    hex_r_lon = d_lon * 0.46
    for name, o_lat, o_lon in offsets:
        c_lat = lat + o_lat
        c_lon = lon + o_lon
        hex_coords = []
        for angle_deg in range(0, 360, 60):
            rad = math.radians(angle_deg)
            hex_coords.append([
                c_lat + hex_r_lat * math.sin(rad),
                c_lon + hex_r_lon * math.cos(rad)
            ])
        cells.append({
            "cell_name": name,
            "lat": c_lat,
            "lon": c_lon,
            "sub_radius_m": sub_radius_m,
            "hex_polygon": hex_coords
        })
    return cells


@st.cache_data(ttl=3600, show_spinner=False)
def compute_road_isochrone(lat, lon, drive_minutes, radius_km, ors_key=""):
    if ors_key:
        try:
            url = "https://api.openrouteservice.org/v2/isochrones/driving-car"
            headers = {"Authorization": ors_key, "Content-Type": "application/json"}
            payload = {"locations": [[lon, lat]], "range": [drive_minutes * 60]}
            r = requests.post(url, json=payload, headers=headers, timeout=8)
            if r.status_code == 200:
                coords = r.json()["features"][0]["geometry"]["coordinates"][0]
                return [[pt[1], pt[0]] for pt in coords]
        except Exception:
            pass

    poly_points = []
    target_road_km = (drive_minutes / 60.0) * 24.0
    for angle in range(0, 360, 45):
        rad = math.radians(angle)
        d_lat = (radius_km / 111.0) * math.cos(rad)
        d_lon = (radius_km / (111.0 * math.cos(math.radians(lat)))) * math.sin(rad)
        dest_lat, dest_lon = lat + d_lat, lon + d_lon
        try:
            osrm_url = f"https://router.project-osrm.org/route/v1/driving/{lon},{lat};{dest_lon},{dest_lat}?overview=false"
            res = requests.get(osrm_url, timeout=3).json()
            if res.get("routes"):
                road_dist_km = res["routes"][0]["distance"] / 1000.0
                detour_ratio = min(1.0, radius_km / max(road_dist_km, 0.1))
                reach_scale = min(1.15, (target_road_km / max(radius_km, 0.5)) * detour_ratio)
                poly_points.append([lat + d_lat * reach_scale, lon + d_lon * reach_scale])
            else:
                poly_points.append([dest_lat * 0.85 + lat * 0.15, dest_lon * 0.85 + lon * 0.15])
        except Exception:
            poly_points.append([dest_lat, dest_lon])
    return poly_points


def query_nearby_node(api_key, cell_name, g_lat, g_lon, sub_radius_m, included_types, group_label):
    url = "https://places.googleapis.com/v1/places:searchNearby"
    headers = {
        "Content-Type": "application/json",
        "X-Goog-Api-Key": api_key,
        "X-Goog-FieldMask": (
            "places.id,places.displayName,places.types,"
            "places.primaryTypeDisplayName,places.formattedAddress,"
            "places.location,places.rating,places.userRatingCount,"
            "places.priceLevel,places.businessStatus"
        )
    }
    payload = {
        "includedTypes": included_types,
        "maxResultCount": 20,
        "locationRestriction": {
            "circle": {
                "center": {"latitude": g_lat, "longitude": g_lon},
                "radius": float(sub_radius_m)
            }
        }
    }
    resp = requests.post(url, json=payload, headers=headers, timeout=12)
    return resp.status_code, resp.json(), group_label, cell_name


def query_text_node(api_key, lat, lon, radius_km, text_query):
    url = "https://places.googleapis.com/v1/places:searchText"
    headers = {
        "Content-Type": "application/json",
        "X-Goog-Api-Key": api_key,
        "X-Goog-FieldMask": (
            "places.id,places.displayName,places.types,"
            "places.primaryTypeDisplayName,places.formattedAddress,"
            "places.location,places.rating,places.userRatingCount,"
            "places.priceLevel,places.businessStatus"
        )
    }
    payload = {
        "textQuery": text_query,
        "maxResultCount": 20,
        "locationBias": {
            "circle": {
                "center": {"latitude": lat, "longitude": lon},
                "radius": float(radius_km * 1000.0)
            }
        }
    }
    resp = requests.post(url, json=payload, headers=headers, timeout=12)
    return resp.status_code, resp.json(), f"Keyword: {text_query}", "Center Core"


@st.cache_data(ttl=1800, show_spinner=False)
def run_business_buddy_scan(
    lat,
    lon,
    radius_km,
    selected_groups,
    custom_keywords_str,
    review_conversion_pct,
    active_months_assumed,
    api_key
):
    cells = build_9_micro_sectors(lat, lon, radius_km)
    tasks = []
    records = []
    seen_ids = set()
    errors = []

    with ThreadPoolExecutor(max_workers=12) as executor:
        for grp in selected_groups:
            place_types = PREDEFINED_CATEGORIES.get(grp, [])
            if not place_types:
                continue
            for cell in cells:
                tasks.append(
                    executor.submit(
                        query_nearby_node,
                        api_key,
                        cell["cell_name"],
                        cell["lat"],
                        cell["lon"],
                        cell["sub_radius_m"],
                        place_types,
                        grp
                    )
                )

        custom_kws = [k.strip() for k in custom_keywords_str.split(",") if k.strip()]
        for kw in custom_kws:
            tasks.append(
                executor.submit(query_text_node, api_key, lat, lon, radius_km, kw)
            )

        for future in as_completed(tasks):
            try:
                status_code, data, group_label, cell_name = future.result()
                if status_code != 200:
                    err_msg = data.get("error", {}).get("message", "API Error")
                    if err_msg not in errors:
                        errors.append(f"HTTP {status_code}: {err_msg}")
                    continue

                for p in data.get("places", []):
                    pid = p.get("id")
                    if not pid or pid in seen_ids:
                        continue
                    p_lat = p.get("location", {}).get("latitude", 0.0)
                    p_lon = p.get("location", {}).get("longitude", 0.0)
                    dist = round(haversine_km(lat, lon, p_lat, p_lon), 2)

                    if dist <= radius_km:
                        seen_ids.add(pid)
                        name = p.get("displayName", {}).get("text", "Unnamed")
                        rating = p.get("rating", None)
                        reviews = int(p.get("userRatingCount", 0) or 0)
                        price_lvl = p.get("priceLevel", "N/A")

                        best_cell = min(
                            cells,
                            key=lambda c: haversine_km(p_lat, p_lon, c["lat"], c["lon"])
                        )["cell_name"]

                        name_lower = name.lower()
                        is_anchor = any(b in name_lower for b in ANCHOR_BRANDS)

                        conv_rate = max(0.01, review_conversion_pct / 100.0)
                        est_monthly_tx = (
                            int((reviews / max(1, active_months_assumed)) / conv_rate)
                            if reviews > 0
                            else 0
                        )
                        est_daily_tx = round(est_monthly_tx / 30.0, 1)

                        records.append({
                            "Place ID": pid,
                            "Business / Place Name": name,
                            "Micro-Sector": best_cell,
                            "Query Group": group_label,
                            "Primary Sub-Type": p.get("primaryTypeDisplayName", {}).get("text", "General POI"),
                            "Anchor Brand": "Yes 🌟" if is_anchor else "No",
                            "Rating (★)": float(rating) if rating is not None else None,
                            "Total Ratings": reviews,
                            "Est. Daily Orders / Footfall": est_daily_tx,
                            "Est. Monthly Orders / Footfall": est_monthly_tx,
                            "Price Tier": price_lvl,
                            "Price Weight": PRICE_TIER_WEIGHTS.get(price_lvl, 0),
                            "Full Address": p.get("formattedAddress", "Address unavailable"),
                            "Distance (km)": dist,
                            "Latitude": p_lat,
                            "Longitude": p_lon
                        })
            except Exception as e:
                if str(e) not in errors:
                    errors.append(str(e))

    df = pd.DataFrame(records)
    if not df.empty:
        df = df.sort_values(by=["Est. Monthly Orders / Footfall", "Distance (km)"], ascending=[False, True]).reset_index(drop=True)
    return df, cells, errors


# ==============================================================================
# 10. SIDEBAR CONTROLS & MAIN DASHBOARD
# ==============================================================================
if "selected_lat" not in st.session_state:
    st.session_state.selected_lat = 30.6924
    st.session_state.selected_lon = 76.8389

if "scan_data" not in st.session_state:
    st.session_state.scan_data = None

with st.sidebar:
    st.title("🤝 Business Buddy Controls")

    secret_gmaps = st.secrets.get("GOOGLE_MAPS_API_KEY", "") if hasattr(st, "secrets") else ""
    api_key_input = st.text_input(
        "Google Maps API Key (Optional Override)",
        value="",
        type="password"
    )
    active_api_key = (
        api_key_input.strip()
        or secret_gmaps
        or ("" if GOOGLE_MAPS_API_KEY == "YOUR_GOOGLE_MAPS_API_KEY_HERE" else GOOGLE_MAPS_API_KEY)
    )

    st.divider()
    st.subheader("1. Catchment & Isochrone Setup")
    zone_label = st.text_input("Location Name / Tag", value="Sector 16-17 Panchkula Audit")
    radius_km = st.slider("Outer Scan Radius (km)", min_value=1.5, max_value=7.0, value=3.0, step=0.5)
    drive_minutes = st.slider("2-Wheeler Delivery Isochrone (Mins)", min_value=5, max_value=25, value=12, step=1)
    show_hex_grid = st.checkbox("Show Hex Opportunity Heatmap", value=True)
    show_isochrone = st.checkbox("Show Road-Network Drive-Time Polygon", value=True)

    st.divider()
    st.subheader("2. Data Layers to Scan")
    selected_groups = st.multiselect(
        "Select Business Buddy Layers",
        options=list(PREDEFINED_CATEGORIES.keys()),
        default=list(PREDEFINED_CATEGORIES.keys())
    )
    custom_keywords = st.text_input(
        "Custom Keywords (comma-separated)",
        value="rajma chawal, kadhi, cloud kitchen, society"
    )

    st.divider()
    st.subheader("3. Order & Revenue Bounds")
    c_min, c_max = st.columns(2)
    min_base_orders = c_min.number_input("Min Daily Orders", min_value=1, max_value=500, value=25, step=5)
    max_cap_orders = c_max.number_input("Max Daily Orders", min_value=10, max_value=2000, value=100, step=10)
    target_aov = st.number_input("Target Combo AOV (₹)", min_value=50, max_value=5000, value=350, step=10)

    with st.expander("Review Velocity Calibration"):
        review_conversion_pct = st.slider("% Buyers Leaving Review", 1.0, 20.0, 8.0, 0.5)
        active_months_assumed = st.slider("Avg. Listing Age (Months)", 6, 60, 24, 6)

col_map, col_intel = st.columns([1.3, 1])

micro_df = pd.DataFrame()
if st.session_state.scan_data is not None:
    df_all, cells_meta = st.session_state.scan_data
    if not df_all.empty:
        cell_rows = []
        for c in cells_meta:
            c_name = c["cell_name"]
            sub = df_all[df_all["Micro-Sector"] == c_name]
            f_cnt = len(sub[sub["Query Group"].str.contains("Food|Keyword", case=False, na=False)])
            h_cnt = len(sub[sub["Query Group"].str.contains("Residential", case=False, na=False)])
            corp_cnt = len(sub[sub["Query Group"].str.contains("Corporate|Healthcare|Education|Affluence", case=False, na=False)])
            daily_ord = int(sub[sub["Query Group"].str.contains("Food|Keyword", case=False, na=False)]["Est. Daily Orders / Footfall"].sum())

            demand_generators = (h_cnt * 3.5) + (corp_cnt * 2.5) + min(40, daily_ord * 0.08)
            comp_penalty = f_cnt * 1.4
            opp_score = max(10, min(99, int(50 + demand_generators - comp_penalty)))

            cell_rows.append({
                "Micro-Sector": c_name,
                "Opportunity Score": opp_score,
                "Housing & Hubs": h_cnt + corp_cnt,
                "Food Competitors": f_cnt,
                "Est. Daily Orders": daily_ord,
                "hex_polygon": c["hex_polygon"],
                "lat": c["lat"],
                "lon": c["lon"]
            })
        micro_df = pd.DataFrame(cell_rows).sort_values(by="Opportunity Score", ascending=False)

with col_map:
    m = folium.Map(location=[st.session_state.selected_lat, st.session_state.selected_lon], zoom_start=14)

    if show_isochrone:
        iso_poly = compute_road_isochrone(
            st.session_state.selected_lat,
            st.session_state.selected_lon,
            drive_minutes,
            radius_km,
            ORS_API_KEY
        )
        folium.Polygon(
            locations=iso_poly,
            color="#7c3aed",
            weight=2,
            dash_array="5, 5",
            fill=True,
            fill_color="#c4b5fd",
            fill_opacity=0.18,
            tooltip=f"{drive_minutes}-Min 2-Wheeler Road Delivery Isochrone"
        ).add_to(m)

    if show_hex_grid and not micro_df.empty:
        for _, crow in micro_df.iterrows():
            score = crow["Opportunity Score"]
            hex_color = "#16a34a" if score >= 68 else ("#eab308" if score >= 48 else "#dc2626")
            folium.Polygon(
                locations=crow["hex_polygon"],
                color=hex_color,
                weight=2,
                fill=True,
                fill_color=hex_color,
                fill_opacity=0.28,
                tooltip=(
                    f"<b>{crow['Micro-Sector']}</b><br>"
                    f"White-Space Opportunity: <b>{score}/100</b><br>"
                    f"Demand Generators: {crow['Housing & Hubs']}<br>"
                    f"Food Competitors: {crow['Food Competitors']}<br>"
                    f"Est. Daily Orders: {crow['Est. Daily Orders']}/day"
                )
            ).add_to(m)

    folium.Circle(
        location=[st.session_state.selected_lat, st.session_state.selected_lon],
        radius=radius_km * 1000,
        color="#1e293b",
        weight=1.5,
        fill=False
    ).add_to(m)

    folium.Marker(
        [st.session_state.selected_lat, st.session_state.selected_lon],
        popup=f"Target Site: {zone_label}",
        icon=folium.Icon(color="darkred", icon="cutlery", prefix="fa")
    ).add_to(m)

    if st.session_state.scan_data is not None:
        df_plot, _ = st.session_state.scan_data
        for _, row in df_plot.head(140).iterrows():
            p_color = "#f59e0b" if row["Anchor Brand"] == "Yes 🌟" else (
                "#ef4444" if "Food" in row["Query Group"] or "Keyword" in row["Query Group"] else (
                    "#10b981" if "Residential" in row["Query Group"] else "#3b82f6"
                )
            )
            folium.CircleMarker(
                location=[row["Latitude"], row["Longitude"]],
                radius=6 if row["Anchor Brand"] == "Yes 🌟" else 4,
                color=p_color,
                fill=True,
                fill_opacity=0.85,
                tooltip=f"{row['Business / Place Name']} ({row['Primary Sub-Type']}) | ★ {row['Rating (★)'] or 'N/A'} | Est. Daily: {row['Est. Daily Orders / Footfall']}"
            ).add_to(m)

    map_output = st_folium(m, height=500, width="100%")

    if map_output and map_output.get("last_clicked"):
        c_lat = map_output["last_clicked"]["lat"]
        c_lon = map_output["last_clicked"]["lng"]
        if round(c_lat, 5) != round(st.session_state.selected_lat, 5) or round(c_lon, 5) != round(st.session_state.selected_lon, 5):
            st.session_state.selected_lat = c_lat
            st.session_state.selected_lon = c_lon
            st.rerun()

    b1, b2 = st.columns([1.6, 1])
    trigger_scan = b1.button("🚀 Run Business Buddy Deep Scan", type="primary", use_container_width=True)
    b2.caption(f"Pin: `{st.session_state.selected_lat:.4f}, {st.session_state.selected_lon:.4f}`")

if trigger_scan:
    if not active_api_key:
        st.error("Please configure `GOOGLE_MAPS_API_KEY` at the top of `app.py` or in the sidebar.")
    else:
        with st.spinner("Business Buddy is scanning 9 micro-sectors..."):
            df_res, cells_meta, errs = run_business_buddy_scan(
                st.session_state.selected_lat,
                st.session_state.selected_lon,
                radius_km,
                tuple(selected_groups),
                custom_keywords,
                review_conversion_pct,
                active_months_assumed,
                active_api_key
            )
            st.session_state.scan_data = (df_res, cells_meta)
            for e in errs:
                st.warning(f"API Notice: {e}")
            st.rerun()

with col_intel:
    st.subheader("📊 Business Buddy Site Scorecard & Indices")

    if st.session_state.scan_data is None or st.session_state.scan_data[0].empty:
        st.info("Click any location on the map and press **🚀 Run Business Buddy Deep Scan** to generate your 4-Pillar Site Scorecard, Hex Opportunity Ranking, and Sales Target Forecast.")
    else:
        df, _ = st.session_state.scan_data

        food_df = df[df["Query Group"].str.contains("Food|Keyword", case=False, na=False)]
        res_df = df[df["Query Group"].str.contains("Residential", case=False, na=False)]
        aff_df = df[df["Query Group"].str.contains("Affluence", case=False, na=False)]
        corp_df = df[df["Query Group"].str.contains("Corporate|Healthcare|Education", case=False, na=False)]
        anchors_df = df[df["Anchor Brand"] == "Yes 🌟"]

        priced_sub = df[df["Price Weight"] > 0]
        avg_price_weight = priced_sub["Price Weight"].mean() if not priced_sub.empty else 2.2
        lifestyle_density = len(aff_df)
        affluence_score = min(98, int((avg_price_weight / 4.5) * 55 + min(45, lifestyle_density * 1.6)))

        anchor_count = len(anchors_df)
        retail_maturity_score = min(98, int(35 + (anchor_count * 4.5) + min(30, len(df) * 0.12)))

        total_market_daily_orders = int(food_df["Est. Daily Orders / Footfall"].sum())
        demand_score = min(99, int(30 + (len(res_df) * 2.2) + (len(corp_df) * 1.8) + min(35, total_market_daily_orders * 0.015)))

        comp_saturation = min(98, int((len(food_df) / max(1.0, radius_km ** 2)) * 9.5))

        overall_buddy_score = int(
            (demand_score * 0.35)
            + (affluence_score * 0.30)
            + (retail_maturity_score * 0.20)
            + ((100 - comp_saturation) * 0.15)
        )

        g1, g2, g3, g4 = st.columns(4)
        g1.metric("Buddy Score", f"{overall_buddy_score}/100")
        g2.metric("Affluence Index", f"{affluence_score}/100")
        g3.metric("Retail Maturity", f"{retail_maturity_score}/100")
        g4.metric("Demand Score", f"{demand_score}/100")

        m1, m2, m3, m4 = st.columns(4)
        m1.metric("Total Mapped POIs", len(df))
        m2.metric("Food Outlets", len(food_df))
        m3.metric("Housing & Hostels", len(res_df))
        m4.metric("Anchor Brands 🌟", anchor_count)

        composite_multiplier = (overall_buddy_score / 100.0)
        pred_m1_daily = int(min_base_orders + (max_cap_orders - min_base_orders) * (composite_multiplier * 0.38))
        pred_m3_daily = int(min_base_orders + (max_cap_orders - min_base_orders) * (composite_multiplier * 0.72))
        pred_m6_daily = int(min_base_orders + (max_cap_orders - min_base_orders) * min(1.0, composite_multiplier * 1.08))

        st.markdown("#### 🎯 Predicted Order & Revenue Ramp")
        ramp_df = pd.DataFrame([
            {"Timeline": "Base Floor (Min)", "Daily Orders": f"{min_base_orders}/day", "Monthly Orders": f"{min_base_orders*30:,}", "Monthly Gross Sales": f"₹{min_base_orders*30*target_aov:,.0f}"},
            {"Timeline": "Month 1–2 (Launch)", "Daily Orders": f"{pred_m1_daily}/day", "Monthly Orders": f"{pred_m1_daily*30:,}", "Monthly Gross Sales": f"₹{pred_m1_daily*30*target_aov:,.0f}"},
            {"Timeline": "Month 3–4 (Growth)", "Daily Orders": f"{pred_m3_daily}/day", "Monthly Orders": f"{pred_m3_daily*30:,}", "Monthly Gross Sales": f"₹{pred_m3_daily*30*target_aov:,.0f}"},
            {"Timeline": "Month 6+ (Maturity)", "Daily Orders": f"{pred_m6_daily}/day", "Monthly Orders": f"{pred_m6_daily*30:,}", "Monthly Gross Sales": f"₹{pred_m6_daily*30*target_aov:,.0f}"},
        ])
        st.table(ramp_df)

        if st.button("💾 Save Location to Business Buddy Comparison Vault", use_container_width=True):
            save_zone_to_db({
                "zone_id": f"{st.session_state.auth_email}_{st.session_state.selected_lat:.4f}_{st.session_state.selected_lon:.4f}",
                "user_email": st.session_state.auth_email,
                "zone_label": zone_label,
                "lat": round(st.session_state.selected_lat, 4),
                "lon": round(st.session_state.selected_lon, 4),
                "radius_km": radius_km,
                "overall_buddy_score": overall_buddy_score,
                "affluence_score": affluence_score,
                "retail_maturity_score": retail_maturity_score,
                "demand_score": demand_score,
                "competition_saturation": comp_saturation,
                "total_pois": len(df),
                "food_outlets": len(food_df),
                "housing_clusters": len(res_df),
                "anchor_brands_count": anchor_count,
                "est_zone_daily_orders": total_market_daily_orders,
                "pred_m1_orders": pred_m1_daily,
                "pred_m6_orders": pred_m6_daily,
                "pred_m6_rev": float(pred_m6_daily * 30 * target_aov),
                "scanned_at": datetime.now().strftime("%Y-%m-%d %H:%M")
            })
            st.success(f"Saved **{zone_label}** to your Business Buddy comparison vault!")

st.divider()
tab_hex, tab_dir, tab_anchors, tab_vault = st.tabs([
    "🟩 Micro-Sector White-Space Ranking (9 Hex Zones)",
    "📋 Full Business & Order Velocity Directory",
    "🌟 Detected Anchor Brands",
    "🏆 Business Buddy Location Comparison Vault"
])

with tab_hex:
    if not micro_df.empty:
        st.dataframe(
            micro_df[["Micro-Sector", "Opportunity Score", "Housing & Hubs", "Food Competitors", "Est. Daily Orders"]],
            use_container_width=True
        )
    else:
        st.info("Run a scan to view micro-sector opportunity rankings.")

with tab_dir:
    if st.session_state.scan_data is not None and not st.session_state.scan_data[0].empty:
        full_df = st.session_state.scan_data[0]
        f_col1, f_col2 = st.columns([2, 1])
        cat_choice = f_col1.selectbox("Filter by Layer", ["All Layers"] + list(full_df["Query Group"].unique()))
        sub_df = full_df if cat_choice == "All Layers" else full_df[full_df["Query Group"] == cat_choice]

        f_col2.download_button(
            "⬇️ Export Filtered Directory (CSV)",
            data=sub_df.to_csv(index=False).encode("utf-8"),
            file_name=f"business_buddy_directory_{zone_label.replace(' ', '_')}.csv",
            mime="text/csv",
            use_container_width=True
        )
        st.dataframe(
            sub_df[[
                "Business / Place Name", "Micro-Sector", "Query Group",
                "Primary Sub-Type", "Anchor Brand", "Rating (★)",
                "Total Ratings", "Est. Daily Orders / Footfall",
                "Est. Monthly Orders / Footfall", "Price Tier",
                "Distance (km)", "Full Address"
            ]],
            use_container_width=True,
            height=420
        )
    else:
        st.info("Run a scan to populate the business directory.")

with tab_anchors:
    if st.session_state.scan_data is not None and not st.session_state.scan_data[0].empty:
        anc_df = st.session_state.scan_data[0]
        anc_df = anc_df[anc_df["Anchor Brand"] == "Yes 🌟"]
        if not anc_df.empty:
            st.dataframe(
                anc_df[["Business / Place Name", "Micro-Sector", "Primary Sub-Type", "Rating (★)", "Total Ratings", "Distance (km)", "Full Address"]],
                use_container_width=True
            )
        else:
            st.warning("No major national anchor brands detected in this circle.")
    else:
        st.info("Run a scan to detect national anchor brands.")

with tab_vault:
    vault_df = load_saved_zones(st.session_state.auth_email)
    if not vault_df.empty:
        st.dataframe(vault_df, use_container_width=True)
        st.download_button(
            "⬇️ Export Business Buddy Comparison Report (CSV)",
            data=vault_df.to_csv(index=False).encode("utf-8"),
            file_name="business_buddy_location_comparison.csv",
            mime="text/csv"
        )
    else:
        st.info("No saved locations yet.")