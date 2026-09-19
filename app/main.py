from fastapi import FastAPI, WebSocket, WebSocketDisconnect, HTTPException, Query, Depends, Header
from fastapi.middleware.cors import CORSMiddleware
from fastapi.staticfiles import StaticFiles
from pydantic import BaseModel, Field
from contextlib import asynccontextmanager
from pathlib import Path
from datetime import datetime, timezone
from collections import deque
import asyncio
import math
import random
import uuid
import hashlib
import hmac
import secrets
import os
import json
import tempfile
import httpx

@asynccontextmanager
async def lifespan(_app: FastAPI):
    await _startup()          # resolved at call time; defined further down
    yield
    save_state()              # flush on shutdown

app = FastAPI(title='HydroSignal Hyperlocal Outbreak Early Warning API', version='2.1.0',
              lifespan=lifespan)

app.add_middleware(
    CORSMiddleware,
    allow_origins=['*'],
    allow_credentials=False,
    allow_methods=['*'],
    allow_headers=['*'],
)

ROOT = Path(__file__).resolve().parents[2]
FRONTEND = ROOT / 'frontend'

# --- Master Coordinates & Districts (Approx 50-100km Radius Surveillance Zone) ---
CENTER_COORDS = {'lat': 16.515, 'lng': 80.645}

DISTRICTS = [
    {'id': 'north', 'name': 'North Ward & Basin', 'lat': 16.545, 'lng': 80.615, 'population': 84000},
    {'id': 'industrial', 'name': 'Industrial Belt & Canal', 'lat': 16.505, 'lng': 80.685, 'population': 62000},
    {'id': 'oldtown', 'name': 'Old Town & Central Market', 'lat': 16.518, 'lng': 80.622, 'population': 115000},
    {'id': 'harbor', 'name': 'Harbor East & Waterfront', 'lat': 16.485, 'lng': 80.672, 'population': 78000},
    {'id': 'green', 'name': 'Greenfield Agricultural Hub', 'lat': 16.582, 'lng': 80.635, 'population': 45000},
    {'id': 'docks', 'name': 'South Docks & Delta', 'lat': 16.445, 'lng': 80.655, 'population': 56000},
    {'id': 'riverbank', 'name': 'Krishna River Intake Point', 'lat': 16.512, 'lng': 80.601, 'population': 31000},
    {'id': 'eastsub', 'name': 'Eastern Sub-Basin (Outer 50km)', 'lat': 16.420, 'lng': 80.760, 'population': 39000},
]

# --- Authentication ---
# Passwords are never stored in the clear, and admin capability is never inferred
# from a username. This matters more than usual here: an admin session can publish
# a public health warning to every resident portal.
PBKDF2_ROUNDS = 120_000
SESSION_TTL_SECONDS = 12 * 3600

# Anyone may sign up as a resident; becoming an officer requires this code.
# Set HYDROSIGNAL_ADMIN_CODE in the environment for anything beyond local demos.
ADMIN_SIGNUP_CODE = os.environ.get('HYDROSIGNAL_ADMIN_CODE', 'hydrosignal-municipal-2026')

def hash_password(password: str, salt: str | None = None) -> str:
    salt = salt or secrets.token_hex(16)
    dk = hashlib.pbkdf2_hmac('sha256', password.encode(), bytes.fromhex(salt), PBKDF2_ROUNDS)
    return f"{salt}${dk.hex()}"

def verify_password(password: str, stored: str) -> bool:
    try:
        salt, expected = stored.split('$', 1)
        dk = hashlib.pbkdf2_hmac('sha256', password.encode(), bytes.fromhex(salt), PBKDF2_ROUNDS)
    except (ValueError, TypeError):
        return False
    return hmac.compare_digest(dk.hex(), expected)

USERS = {
    'demo_user': {
        'username': 'demo_user',
        'password_hash': hash_password('demo1234'),
        'role': 'user',
        'name': 'Community Resident',
        'area': 'oldtown'
    },
    'admin': {
        'username': 'admin',
        'password_hash': hash_password('admin1234'),
        'role': 'admin',
        'name': 'Municipal Health Director',
        'department': 'Municipal Public Health & Water Works'
    }
}

# token -> {username, role, name, issued_at}
SESSIONS: dict[str, dict] = {}

def issue_session(user: dict) -> str:
    token = secrets.token_urlsafe(32)
    SESSIONS[token] = {
        'username': user['username'],
        'role': user['role'],
        'name': user.get('name', user['username']),
        'issued_at': datetime.now(timezone.utc).timestamp(),
    }
    return token

def _purge_expired_sessions():
    cutoff = datetime.now(timezone.utc).timestamp() - SESSION_TTL_SECONDS
    for tok in [t for t, sdata in SESSIONS.items() if sdata['issued_at'] < cutoff]:
        SESSIONS.pop(tok, None)

def session_from_header(authorization: str | None) -> dict | None:
    if not authorization:
        return None
    token = authorization[7:].strip() if authorization.lower().startswith('bearer ') else authorization.strip()
    _purge_expired_sessions()
    return SESSIONS.get(token)

def current_session(authorization: str | None = Header(default=None)) -> dict | None:
    return session_from_header(authorization)

def require_auth(authorization: str | None = Header(default=None)) -> dict:
    sess = session_from_header(authorization)
    if not sess:
        raise HTTPException(401, 'Sign in required')
    return sess

def require_admin(authorization: str | None = Header(default=None)) -> dict:
    sess = require_auth(authorization)
    if sess['role'] != 'admin':
        raise HTTPException(403, 'Municipal officer privileges required')
    return sess

# --- Water Quality Stations ---
def calc_wqi(ph: float, tds: float, turb: float, cl: float) -> int:
    # WQI: Ideal pH is 7.0-8.0, TDS < 300, Turbidity < 1.0, Chlorine 0.2-0.6
    ph_score = max(0, 100 - abs(ph - 7.3) * 35)
    tds_score = max(0, 100 - (tds / 500) * 45 if tds <= 500 else max(0, 55 - (tds - 500) * 0.2))
    turb_score = max(0, 100 - (turb / 5.0) * 60 if turb <= 5.0 else max(0, 40 - (turb - 5.0) * 8))
    cl_score = 100 if (0.2 <= cl <= 0.6) else max(0, 100 - abs(cl - 0.4) * 120)
    wqi = round(0.30 * ph_score + 0.30 * tds_score + 0.25 * turb_score + 0.15 * cl_score)
    return min(100, max(0, wqi))

water_stations = [
    {
        'id': 'h3',
        'name': 'Pump Station H-3 Waterfront',
        'area': 'harbor',
        'lat': 16.488,
        'lng': 80.669,
        'ph': 7.2,
        'tds': 224,
        'turbidity': 1.4,
        'chlorine': 0.42,
        'temp': 27.2,
        'microbial': 'absent',
        'history_ph': [7.1, 7.2, 7.3, 7.2, 7.15, 7.2],
        'history_tds': [210, 218, 222, 220, 224, 224],
        'wqi': 88
    },
    {
        'id': 'ot',
        'name': 'Old Town Central Standpipe',
        'area': 'oldtown',
        'lat': 16.517,
        'lng': 80.623,
        'ph': 7.0,
        'tds': 255,
        'turbidity': 1.8,
        'chlorine': 0.35,
        'temp': 26.8,
        'microbial': 'absent',
        'history_ph': [6.9, 7.0, 7.05, 6.98, 7.0, 7.0],
        'history_tds': [245, 248, 250, 252, 255, 255],
        'wqi': 84
    },
    {
        'id': 'gf',
        'name': 'Greenfield Reservoir Well',
        'area': 'green',
        'lat': 16.580,
        'lng': 80.638,
        'ph': 6.9,
        'tds': 188,
        'turbidity': 0.9,
        'chlorine': 0.50,
        'temp': 25.9,
        'microbial': 'absent',
        'history_ph': [6.85, 6.9, 6.92, 6.9, 6.88, 6.9],
        'history_tds': [180, 182, 185, 186, 188, 188],
        'wqi': 92
    },
    {
        'id': 'dk',
        'name': 'South Docks Supply Trunk',
        'area': 'docks',
        'lat': 16.448,
        'lng': 80.658,
        'ph': 7.3,
        'tds': 238,
        'turbidity': 1.6,
        'chlorine': 0.38,
        'temp': 27.5,
        'microbial': 'absent',
        'history_ph': [7.25, 7.3, 7.32, 7.28, 7.3, 7.3],
        'history_tds': [230, 232, 235, 237, 238, 238],
        'wqi': 86
    },
    {
        'id': 'rb',
        'name': 'Krishna River Intake Canal Station',
        'area': 'riverbank',
        'lat': 16.513,
        'lng': 80.603,
        'ph': 7.4,
        'tds': 195,
        'turbidity': 2.1,
        'chlorine': 0.45,
        'temp': 26.5,
        'microbial': 'absent',
        'history_ph': [7.35, 7.4, 7.42, 7.38, 7.4, 7.4],
        'history_tds': [190, 192, 194, 195, 195, 195],
        'wqi': 89
    }
]

# Update initial WQIs
for s in water_stations:
    s['wqi'] = calc_wqi(s['ph'], s['tds'], s['turbidity'], s['chlorine'])

# --- Reports Store ---
# status: 'pending_approval' | 'approved' | 'rejected'
reports = [
    {
        'id': 'rep-seed-1',
        'type': 'illness',
        'title': 'Gastroenteritis Cluster Alert',
        'area': 'oldtown',
        'lat': 16.519,
        'lng': 80.624,
        'severity': 3,
        'note': '3 households with acute watery diarrhea and vomiting near Gandhi Road.',
        'status': 'approved',
        'submitter': 'Community Clinic Desk',
        'time': '2026-09-18T18:40:00Z',
        'approved_by': 'admin',
        'approved_at': '2026-09-18T19:00:00Z',
        'origin': 'seed'
    },
    {
        'id': 'rep-seed-2',
        'type': 'water',
        'title': 'Community Tap Turbidity & Foul Odor',
        'area': 'harbor',
        'lat': 16.486,
        'lng': 80.671,
        'severity': 2,
        'note': 'Murky brown water coming from municipal tap line near dock lane 4.',
        'status': 'approved',
        'submitter': 'Resident R. Naidu',
        'time': '2026-09-18T20:15:00Z',
        'approved_by': 'admin',
        'approved_at': '2026-09-18T20:30:00Z',
        'origin': 'seed'
    },
    {
        'id': 'rep-seed-3',
        'type': 'flood',
        'title': 'Monsoon Waterlogging Near Overhead Storage Tank',
        'area': 'harbor',
        'lat': 16.489,
        'lng': 80.675,
        'severity': 3,
        'note': 'Knee-deep standing water near public distribution tank foundation; potential seepage risk.',
        'status': 'approved',
        'submitter': 'Ward Sanitary Inspector',
        'time': '2026-09-18T22:10:00Z',
        'approved_by': 'admin',
        'approved_at': '2026-09-18T22:25:00Z',
        'origin': 'seed'
    },
    {
        'id': 'rep-seed-4',
        'type': 'sanit',
        'title': 'Open Drainage Overflow Next to Water Standpipe',
        'area': 'oldtown',
        'lat': 16.516,
        'lng': 80.620,
        'severity': 2,
        'note': 'Blocked storm drain spilling into tap recharge zone.',
        'status': 'approved',
        'submitter': 'Market Vendors Association',
        'time': '2026-09-18T23:00:00Z',
        'approved_by': 'admin',
        'approved_at': '2026-09-18T23:15:00Z',
        'origin': 'seed'
    },
    {
        'id': 'rep-seed-5',
        'type': 'water',
        'title': 'Rooftop Storage Tank Residue Complaint',
        'area': 'north',
        'lat': 16.542,
        'lng': 80.618,
        'severity': 2,
        'note': 'Yellowish sediment in apartment water tank, requires municipal testing.',
        'status': 'pending_approval',
        'submitter': 'Resident P. Varma',
        'time': '2026-09-19T00:15:00Z',
        'approved_by': None,
        'approved_at': None,
        'origin': 'seed'
    },
    {
        'id': 'rep-seed-6',
        'type': 'illness',
        'title': 'Enteric Fever Symptoms in 2 School Children',
        'area': 'industrial',
        'lat': 16.508,
        'lng': 80.681,
        'severity': 3,
        'note': 'Children drank water from unboiled cooler near industrial colony bus stop.',
        'status': 'pending_approval',
        'submitter': 'School Health Volunteer',
        'time': '2026-09-19T00:50:00Z',
        'approved_by': None,
        'approved_at': None,
        'origin': 'seed'
    }
]

# --- Alerts & Municipal Bulletins ---
alerts = [
    {
        'id': 'alt-1',
        'level': 'watch',
        'title': 'Monsoon Drainage Advisory — Harbor East & Old Town',
        'body': 'Heavy rainfall runoff observed. Water tanker sanitization squads deployed. Precautionary water boiling strongly advised for drinking purposes.',
        'regions': ['harbor', 'oldtown'],
        'evidence': ['Precipitation accumulation 64mm', 'Surface runoff near standpipes'],
        'action': 'Boil all drinking water for at least 1 minute. Report discoloration or strange odor immediately.',
        'time': '2026-09-18T21:00:00Z',
        'source': 'Municipal Health Department'
    }
]

# --- Durable State ---
# A uvicorn restart used to wipe every submitted report, approval and account.
# Snapshot to disk atomically so a demo survives a reload.
STATE_PATH = Path(os.environ.get('HYDROSIGNAL_STATE', ROOT / 'backend' / 'state.json'))
_state_dirty = False

def save_state():
    """Atomic write: serialise to a temp file in the same directory, then replace."""
    try:
        payload = {'version': 1, 'saved_at': now_iso(),
                   'reports': reports, 'alerts': alerts, 'users': USERS}
        STATE_PATH.parent.mkdir(parents=True, exist_ok=True)
        fd, tmp = tempfile.mkstemp(dir=str(STATE_PATH.parent), suffix='.tmp')
        with os.fdopen(fd, 'w', encoding='utf-8') as fh:
            json.dump(payload, fh, indent=1)
        os.replace(tmp, STATE_PATH)
    except Exception as exc:
        print(f'[hydrosignal] state save failed: {exc}')

def load_state():
    """Restore a previous snapshot over the seeds. Seeds stand in only on first run."""
    if not STATE_PATH.exists():
        return False
    try:
        with open(STATE_PATH, encoding='utf-8') as fh:
            payload = json.load(fh)
        if payload.get('reports'):
            reports[:] = payload['reports']
        if payload.get('alerts') is not None:
            alerts[:] = payload['alerts']
        for uname, u in (payload.get('users') or {}).items():
            # Never resurrect an account stored in the old plaintext format.
            if 'password_hash' in u:
                USERS[uname] = u
        return True
    except Exception as exc:
        print(f'[hydrosignal] state load failed, continuing with seed data: {exc}')
        return False

# --- Historical Clusters & Contamination Archive (Factor 7) ---
historical_clusters = [
    {
        'id': 'hist-2025-08',
        'title': 'Ward 7 Underground Sump Infiltration Outbreak',
        'period': 'August 14–22, 2025',
        'area': 'Old Town & Market Zone',
        'lat': 16.516,
        'lng': 80.621,
        'cases': 64,
        'primary_cause': 'Cracked sewage line leaking into drinking water supply pipe during flash monsoon.',
        'wqi_dip': 38,
        'pathogen_isolated': 'Vibrio cholerae (non-O1) & E. coli',
        'response_time': '18 hours to pipeline isolation',
        'actions_taken': 'Chlorine shock dosed at 5 ppm, 14,000 ORS sachets distributed, pipeline replaced with HDPE line within 72 hours.',
        'status': 'Resolved & Closed'
    },
    {
        'id': 'hist-2025-03',
        'title': 'Harbor Industrial Colony Storage Tank Contamination',
        'period': 'March 02–09, 2025',
        'area': 'Harbor East',
        'lat': 16.487,
        'lng': 80.674,
        'cases': 39,
        'primary_cause': 'Uncovered municipal overhead tank breached by bird droppings and algal bloom.',
        'wqi_dip': 44,
        'pathogen_isolated': 'Salmonella enterica',
        'response_time': '12 hours to tank drainage',
        'actions_taken': 'Tank emptied, power scrubbed with bleaching powder, sealed with UV-stabilized tamper-proof hatch.',
        'status': 'Resolved & Closed'
    },
    {
        'id': 'hist-2024-11',
        'title': 'Krishna River Intake High Turbidity Silt Runoff Event',
        'period': 'November 05–12, 2024',
        'area': 'Krishna River Intake Point',
        'lat': 16.512,
        'lng': 80.601,
        'cases': 18,
        'primary_cause': 'Upstream dam discharge caused raw water turbidity spike to 38 NTU, overwhelming alum coagulator.',
        'wqi_dip': 51,
        'pathogen_isolated': 'Cryptosporidium oocysts (low density)',
        'response_time': '6 hours to secondary filtration bypass',
        'actions_taken': 'Dual coagulant dosing activated, automated backwash frequency tripled, public advisory broadcast.',
        'status': 'Resolved & Closed'
    }
]

# --- Nearby Healthcare & 24/7 Pharmacy Directory (Factor 9) ---
def haversine(lat1, lon1, lat2, lon2):
    R = 6371.0 # km
    dlat = math.radians(lat2 - lat1)
    dlon = math.radians(lon2 - lon1)
    a = math.sin(dlat / 2)**2 + math.cos(math.radians(lat1)) * math.cos(math.radians(lat2)) * math.sin(dlon / 2)**2
    c = 2 * math.atan2(math.sqrt(a), math.sqrt(1 - a))
    return round(R * c, 2)

nearby_facilities = [
    {
        'id': 'hc-1',
        'name': 'District Government General Hospital & Emergency Unit',
        'type': 'Hospital',
        'lat': 16.510,
        'lng': 80.630,
        'phone': '+91 866 257 8899',
        'hours': '24/7 Emergency',
        'beds_available': 42,
        'ors_stock': 'Adequate (>2000 packs)',
        'iv_saline_stock': 'Available',
        'isolation_ward': 'Yes (15 beds)'
    },
    {
        'id': 'hc-2',
        'name': 'Urban Primary Health Centre — Old Town Ward',
        'type': 'PHC',
        'lat': 16.518,
        'lng': 80.625,
        'phone': '+91 866 244 1102',
        'hours': '08:00 – 20:00',
        'beds_available': 8,
        'ors_stock': 'Available (450 packs)',
        'iv_saline_stock': 'Limited',
        'isolation_ward': 'Day Care Only'
    },
    {
        'id': 'hc-3',
        'name': 'Harbor East Community Health Post',
        'type': 'Clinic',
        'lat': 16.489,
        'lng': 80.668,
        'phone': '+91 866 238 9011',
        'hours': '24/7 Casualty',
        'beds_available': 12,
        'ors_stock': 'High Priority (>800 packs)',
        'iv_saline_stock': 'Available',
        'isolation_ward': 'Yes (6 beds)'
    },
    {
        'id': 'ph-1',
        'name': 'Apollo 24/7 Pharmacy & Emergency Meds',
        'type': 'Pharmacy',
        'lat': 16.512,
        'lng': 80.635,
        'phone': '+91 866 248 7700',
        'hours': 'Open 24 Hours',
        'beds_available': None,
        'ors_stock': 'In Stock (Electrobion / WHO-ORS)',
        'water_purification_tablets': 'Available (Aquatabs 500+)',
        'chlorine_drops': 'Available'
    },
    {
        'id': 'ph-2',
        'name': 'MedPlus 24-Hour Municipal Square Chemist',
        'type': 'Pharmacy',
        'lat': 16.517,
        'lng': 80.619,
        'phone': '+91 866 241 3322',
        'hours': 'Open 24 Hours',
        'beds_available': None,
        'ors_stock': 'In Stock (Prolyte / ORS)',
        'water_purification_tablets': 'Available',
        'chlorine_drops': 'Available'
    },
    {
        'id': 'ph-3',
        'name': 'Harbor Dockland Day-Night Meds',
        'type': 'Pharmacy',
        'lat': 16.484,
        'lng': 80.672,
        'phone': '+91 866 232 4455',
        'hours': 'Open 24 Hours',
        'beds_available': None,
        'ors_stock': 'In Stock',
        'water_purification_tablets': 'Available',
        'chlorine_drops': 'Available'
    }
]

# --- WebSocket Hub ---
class Hub:
    def __init__(self):
        self.clients = set()

    async def broadcast(self, payload: dict):
        dead = []
        for ws in list(self.clients):
            try:
                await ws.send_json(payload)
            except Exception:
                dead.append(ws)
        for ws in dead:
            self.clients.discard(ws)

hub = Hub()

def now_iso():
    return datetime.now(timezone.utc).isoformat()

# --- Live Meteorological State ---
# Rainfall is an input to the model, so it lives server-side and is refreshed on a
# timer rather than being fetched per browser request.
weather_state = {
    'rain_24h_mm': 0.0,
    'current_rain_mm': 0.0,
    'surface_pressure_hpa': 1012.0,
    'source': 'awaiting first fetch',
    'fetched_at': None,
}

async def fetch_open_meteo(lat: float, lng: float) -> dict | None:
    try:
        async with httpx.AsyncClient(timeout=4.0) as client:
            url = (f"https://api.open-meteo.com/v1/forecast?latitude={lat}&longitude={lng}"
                   "&current=precipitation,rain,showers,surface_pressure"
                   "&hourly=precipitation,rain&forecast_days=1")
            resp = await client.get(url)
            if resp.status_code == 200:
                data = resp.json()
                current = data.get('current', {})
                hourly = data.get('hourly', {})
                rain_hourly = hourly.get('precipitation', [0.0])
                return {
                    'rain_24h_mm': round(sum(rain_hourly[:24]), 1),
                    'current_rain_mm': current.get('rain', 0.0),
                    'surface_pressure_hpa': current.get('surface_pressure', 1012),
                    'source': 'Open-Meteo Hyperlocal Live API',
                }
    except Exception:
        pass
    return None

async def refresh_weather_state():
    live = await fetch_open_meteo(CENTER_COORDS['lat'], CENTER_COORDS['lng'])
    if live is None:
        live = {'rain_24h_mm': 68.5, 'current_rain_mm': 12.4, 'surface_pressure_hpa': 1008.2,
                'source': 'HydroSignal Meteorological Station (simulated fallback)'}
    weather_state.update(live)
    weather_state['fetched_at'] = now_iso()
    return weather_state

# --- Risk & AI Prediction Computation ---
# Everything the model is built from, in one place, so the API can describe itself
# to the UI instead of the UI hard-coding a copy of these numbers.
BASELINE_POINTS = 12
SCORE_SCALING = 0.85
CLUSTER_BONUS = 15
LOW_WQI_BONUS = 10
MICROBIAL_BONUS = 25
LOW_WQI_THRESHOLD = 80

# A severe event in one district must not be averaged into invisibility across six.
ZONE_AVG_SHARE = 0.60
WORST_DISTRICT_SHARE = 0.40

# Rainfall only starts contributing once runoff becomes plausible.
RAIN_FREE_MM = 20.0
RAIN_POINTS_PER_MM = 1.2

FACTOR_SPECS = [
    {'key': 'illness', 'label': 'Community illness reports',
     'basis': 'Verified enteric/illness reports, severity x 8',
     'weight': 0.30},
    {'key': 'water', 'label': 'Water quality complaints',
     'basis': 'Verified taste/odour/discolouration reports, severity x 6',
     'weight': 0.20},
    {'key': 'station', 'label': 'Sensor telemetry penalty',
     'basis': 'Turbidity over 2.0 NTU x12, pH deviation from 7.2 x25, TDS over 250 ppm x0.15, chlorine deficit below 0.2 ppm x150',
     'weight': 0.20},
    {'key': 'rain', 'label': 'Hyperlocal rainfall (live)',
     'basis': f'Open-Meteo 24h accumulation above {RAIN_FREE_MM:.0f} mm x {RAIN_POINTS_PER_MM}',
     'weight': 0.10},
    {'key': 'flood', 'label': 'Flooding & waterlogging',
     'basis': 'Verified flood/waterlog reports, severity x 5',
     'weight': 0.10},
    {'key': 'sanit', 'label': 'Sanitation failures',
     'basis': 'Verified drainage/sewage reports, severity x 4',
     'weight': 0.10},
]

RISK_BANDS = [
    {'band': 'low', 'min': 0, 'max': 30},
    {'band': 'watch', 'min': 31, 'max': 60},
    {'band': 'elevated', 'min': 61, 'max': 80},
    {'band': 'high', 'min': 81, 'max': 100},
]

def band_for(score: int) -> str:
    return 'low' if score < 31 else 'watch' if score < 61 else 'elevated' if score < 81 else 'high'

def station_penalty(st: dict) -> dict:
    """Telemetry penalty broken into its parts so the UI can show which reading hurts."""
    turb = max(0.0, (st['turbidity'] - 2.0) * 12)
    ph = abs(st['ph'] - 7.2) * 25
    tds = max(0.0, (st['tds'] - 250) * 0.15)
    chlorine = max(0.0, (0.2 - st['chlorine']) * 150)
    return {
        'turbidity': round(turb, 2), 'ph': round(ph, 2),
        'tds': round(tds, 2), 'chlorine': round(chlorine, 2),
        'total': round(turb + ph + tds + chlorine, 2)
    }

def rain_points() -> float:
    return round(max(0.0, (weather_state['rain_24h_mm'] - RAIN_FREE_MM) * RAIN_POINTS_PER_MM), 2)

def compute_area_risk(area_id: str) -> dict:
    approved = [r for r in reports if r['area'] == area_id and r['status'] == 'approved']
    illness_pts = sum(r['severity'] * 8 for r in approved if r['type'] == 'illness')
    water_pts = sum(r['severity'] * 6 for r in approved if r['type'] == 'water')
    flood_pts = sum(r['severity'] * 5 for r in approved if r['type'] in ('flood', 'waterlog'))
    sanit_pts = sum(r['severity'] * 4 for r in approved if r['type'] == 'sanit')

    st = next((s for s in water_stations if s['area'] == area_id), None)
    breakdown = station_penalty(st) if st else {'turbidity': 0, 'ph': 0, 'tds': 0, 'chlorine': 0, 'total': 0}
    rain_pts = rain_points()

    raw_points = {'illness': illness_pts, 'water': water_pts, 'station': breakdown['total'],
                  'rain': rain_pts, 'flood': flood_pts, 'sanit': sanit_pts}
    weights = {f['key']: f['weight'] for f in FACTOR_SPECS}
    contributions = {k: round(v * weights[k], 2) for k, v in raw_points.items()}

    raw = round(BASELINE_POINTS + sum(contributions.values()), 2)
    composite = min(100, round(raw))
    driver = max(contributions.items(), key=lambda kv: kv[1])

    return {
        'area': area_id,
        'name': next((d['name'] for d in DISTRICTS if d['id'] == area_id), area_id),
        'population': next((d.get('population') for d in DISTRICTS if d['id'] == area_id), None),
        'score': composite,
        'score_uncapped': raw,
        'band': band_for(composite),
        'contributions': contributions,
        'raw_points': raw_points,
        'station_breakdown': breakdown,
        'station_name': st['name'] if st else None,
        'microbial': (st.get('microbial', 'absent') if st else 'absent'),
        'dominant_driver': driver[0] if driver[1] > 0 else None,
        'counts': {
            'illness': len([r for r in approved if r['type'] == 'illness']),
            'water': len([r for r in approved if r['type'] == 'water']),
            'flood': len([r for r in approved if r['type'] in ('flood', 'waterlog')]),
            'sanit': len([r for r in approved if r['type'] == 'sanit'])
        },
        'pending': len([r for r in reports if r['area'] == area_id and r['status'] == 'pending_approval'])
    }

def compute_system_prediction() -> dict:
    area_risks = {d['id']: compute_area_risk(d['id']) for d in DISTRICTS}
    districts = sorted(area_risks.values(), key=lambda r: r['score'], reverse=True)
    n_areas = len(area_risks)

    avg_score = round(sum(r['score'] for r in area_risks.values()) / n_areas, 2)
    worst = districts[0]

    # Blended headline: the zone as a whole, weighted against its worst district.
    blended_raw = ZONE_AVG_SHARE * avg_score + WORST_DISTRICT_SHARE * worst['score']
    overall = min(100, max(0, round(blended_raw)))
    score_band = band_for(overall)

    cluster_detected = any(r['counts']['illness'] >= 3 for r in area_risks.values())
    wqi_avg = round(sum(s['wqi'] for s in water_stations) / len(water_stations))
    microbial_stations = [s['name'] for s in water_stations if s.get('microbial', 'absent') != 'absent']

    # Per-factor contribution blended exactly as the score is, so the numbers add up.
    factors = []
    for spec in FACTOR_SPECS:
        k = spec['key']
        mean_contrib = sum(r['contributions'][k] for r in area_risks.values()) / n_areas
        contrib = round(ZONE_AVG_SHARE * mean_contrib + WORST_DISTRICT_SHARE * worst['contributions'][k], 2)
        mean_raw = round(sum(r['raw_points'][k] for r in area_risks.values()) / n_areas, 2)
        count = sum(r['counts'][k] for r in area_risks.values()) if k in ('illness', 'water', 'flood', 'sanit') else None
        factors.append({**spec, 'raw_points': mean_raw, 'worst_raw_points': worst['raw_points'][k],
                        'points': contrib, 'count': count})

    factor_total = round(sum(f['points'] for f in factors), 2)

    triggers = []
    if worst['score'] >= 60:
        triggers.append(f"Elevated localized signal in {worst['name']} (Score: {worst['score']})")
    if cluster_detected:
        triggers.append("Spatial illness clustering: 3+ concurrent enteric reports within 800m window")
    if microbial_stations:
        triggers.append(f"Microbial presence flagged at {', '.join(microbial_stations)}")
    if any(s['turbidity'] > 3.0 for s in water_stations):
        triggers.append("Water turbidity drift exceeding 3.0 NTU baseline at community pump station")
    if any(s['ph'] < 6.5 or s['ph'] > 8.5 for s in water_stations):
        triggers.append("Abnormal pH excursion detected outside operational range (6.5-8.5)")
    if any(s['chlorine'] < 0.2 for s in water_stations):
        triggers.append("Free chlorine residual below 0.2 ppm minimum at one or more nodes")
    if weather_state['rain_24h_mm'] > 60:
        triggers.append(f"Heavy 24h rainfall accumulation ({weather_state['rain_24h_mm']} mm) driving runoff into supply")
    if not triggers:
        triggers.append("Seasonal baseline conditions; baseline monitoring active across all water distribution trunks")

    modifier_points = ((CLUSTER_BONUS if cluster_detected else 0)
                       + (LOW_WQI_BONUS if wqi_avg < LOW_WQI_THRESHOLD else 0)
                       + (MICROBIAL_BONUS if microbial_stations else 0))
    probability = min(96, max(8, round(overall * SCORE_SCALING + modifier_points)))
    # The headline band describes the headline number. Deriving it from the raw score
    # instead produced 'LOW RISK' next to a 46% probability once modifiers applied.
    band = band_for(probability)

    actions = []
    if probability >= 65:
        actions.extend([
            'Immediate deployment of municipal sampling squad to verify microbial presence.',
            'Issue hyperlocal boil-water advisory via SMS and community broadcast.',
            'Pre-position oral rehydration salts (ORS) and IV fluids in nearest Primary Health Centres.',
            'Isolate and backwash affected water supply trunk / chlorinate overhead storage tanks.'
        ])
    elif probability >= 40:
        actions.extend([
            'Increase chlorine residual monitoring frequency to every 2 hours.',
            'Sanitation patrol to clear blocked storm drains and eliminate standing water.',
            'Daily case surveillance reporting from local pharmacies and clinics.'
        ])
    else:
        actions.extend([
            'Standard automated sensor telemetry monitoring.',
            'Routine bi-weekly microbiological water sampling.'
        ])

    return {
        'timestamp': now_iso(),
        'overall_risk_score': overall,
        'zone_average_score': avg_score,
        'worst_district_score': worst['score'],
        'worst_district': worst['area'],
        'worst_district_name': worst['name'],
        'aggregation': {'zone_average_share': ZONE_AVG_SHARE, 'worst_district_share': WORST_DISTRICT_SHARE},
        'risk_band': band,
        'score_band': score_band,
        'probability_percent': probability,
        'cluster_detected': cluster_detected,
        'highest_risk_area': worst['area'],
        'wqi_city_average': wqi_avg,
        'triggers': triggers,
        'recommended_actions': actions,
        # --- Model transparency: what the number is actually made of ---
        'factors': factors,
        'factor_total': factor_total,
        'baseline_points': BASELINE_POINTS,
        'modifiers': [
            {'key': 'cluster', 'label': 'Spatial illness clustering (3+ reports in one district)',
             'points': CLUSTER_BONUS, 'active': cluster_detected},
            {'key': 'microbial', 'label': 'Microbial presence confirmed at a station',
             'points': MICROBIAL_BONUS, 'active': bool(microbial_stations)},
            {'key': 'wqi', 'label': f'City average WQI below {LOW_WQI_THRESHOLD}',
             'points': LOW_WQI_BONUS, 'active': wqi_avg < LOW_WQI_THRESHOLD},
        ],
        'modifier_points': modifier_points,
        'score_scaling': SCORE_SCALING,
        'bands': RISK_BANDS,
        'districts': districts,
        'weather': dict(weather_state),
        'stations': [{
            'id': s['id'], 'name': s['name'], 'area': s['area'], 'wqi': s['wqi'],
            'ph': s['ph'], 'tds': s['tds'], 'turbidity': s['turbidity'],
            'chlorine': s['chlorine'], 'microbial': s.get('microbial', 'absent'),
            'penalty': station_penalty(s)
        } for s in water_stations],
        'thresholds': THRESHOLD_SPECS,
        'formula': 'score = 0.6 x zone average + 0.4 x worst district; probability = clamp(8..96, score x 0.85 + modifiers)',
        'pending_unverified': len([r for r in reports if r['status'] == 'pending_approval']),
        'disclaimer': 'AI early warning signal designed for municipal decision-support; not a laboratory microbiological confirmation.'
    }

# --- Rolling Telemetry: probability history & live signal log ---
probability_history = deque(maxlen=150)   # {t, probability, score, band}
signal_log = deque(maxlen=60)             # {t, kind, level, text}

def log_signal(kind: str, text: str, level: str = 'info'):
    signal_log.appendleft({'t': now_iso(), 'kind': kind, 'level': level, 'text': text})

def record_prediction_point(pred: dict):
    probability_history.append({
        't': pred['timestamp'],
        'probability': pred['probability_percent'],
        'score': pred['overall_risk_score'],
        'band': pred['risk_band'],
    })

# What the automatic watch is measuring, published so the UI can show live headroom
# instead of restating the numbers itself.
THRESHOLD_SPECS = [
    {'key': 'turbidity', 'label': 'Turbidity', 'unit': 'NTU', 'limit': 5.0, 'direction': 'max',
     'level': 'high', 'note': 'Above 5 NTU, chlorine cannot reliably reach pathogens'},
    {'key': 'chlorine', 'label': 'Free chlorine', 'unit': 'ppm', 'limit': 0.2, 'direction': 'min',
     'level': 'elevated', 'note': 'Below 0.2 ppm the network loses residual protection'},
    {'key': 'ph', 'label': 'pH (low)', 'unit': '', 'limit': 6.5, 'direction': 'min',
     'level': 'elevated', 'note': 'Disinfection efficiency degrades below 6.5'},
    {'key': 'ph_high', 'label': 'pH (high)', 'unit': '', 'limit': 8.5, 'direction': 'max',
     'level': 'elevated', 'note': 'Disinfection efficiency degrades above 8.5', 'field': 'ph'},
    {'key': 'tds', 'label': 'Dissolved solids', 'unit': 'ppm', 'limit': 500, 'direction': 'max',
     'level': 'elevated', 'note': 'Above 500 ppm suggests ingress or saline intrusion'},
]

# --- Automatic Contamination Warning Engine ---
# Thresholds follow WHO drinking-water guideline values rather than arbitrary numbers.
# Each rule has a separate `clear` predicate set inside the trip threshold (hysteresis),
# so a sensor hovering on the limit cannot flap the public warning on and off.
CONTAMINATION_RULES = [
    {
        'key': 'microbial', 'level': 'high',
        'trip': lambda s: s.get('microbial', 'absent') != 'absent',
        'clear': lambda s: s.get('microbial', 'absent') == 'absent',
        'title': lambda s: f"Microbial contamination detected — {s['name']}",
        'body': lambda s: f"Automated laboratory/sensor flag reports microbial presence at {s['name']}. This supply is unsafe to drink untreated.",
        'action': 'Do not drink tap water. Boil vigorously for at least 1 minute, or use sealed bottled water, until an all-clear is issued.'
    },
    {
        'key': 'turbidity', 'level': 'high',
        'trip': lambda s: s['turbidity'] > 5.0,
        'clear': lambda s: s['turbidity'] <= 4.0,
        'title': lambda s: f"Severe turbidity breach — {s['name']}",
        'body': lambda s: f"Turbidity at {s['name']} is {s['turbidity']} NTU, above the 5.0 NTU limit for drinking water. High turbidity shields pathogens from chlorine disinfection.",
        'action': 'Do not drink tap water untreated. Boil for 1 minute before drinking or cooking.'
    },
    {
        'key': 'chlorine', 'level': 'elevated',
        'trip': lambda s: s['chlorine'] < 0.2,
        'clear': lambda s: s['chlorine'] >= 0.25,
        'title': lambda s: f"Disinfection residual lost — {s['name']}",
        'body': lambda s: f"Free chlorine residual at {s['name']} has fallen to {s['chlorine']} ppm, below the 0.2 ppm minimum. The supply is no longer protected against recontamination in the pipe network.",
        'action': 'Boil drinking water as a precaution until residual disinfection is restored.'
    },
    {
        'key': 'ph', 'level': 'elevated',
        'trip': lambda s: s['ph'] < 6.5 or s['ph'] > 8.5,
        'clear': lambda s: 6.6 <= s['ph'] <= 8.4,
        'title': lambda s: f"pH excursion — {s['name']}",
        'body': lambda s: f"pH at {s['name']} is {s['ph']}, outside the 6.5–8.5 operational range. Chlorine disinfection efficiency degrades sharply outside this band.",
        'action': 'Avoid drinking untreated tap water from this zone until readings normalise.'
    },
    {
        'key': 'tds', 'level': 'elevated',
        'trip': lambda s: s['tds'] > 500,
        'clear': lambda s: s['tds'] <= 460,
        'title': lambda s: f"Dissolved solids above limit — {s['name']}",
        'body': lambda s: f"TDS at {s['name']} is {s['tds']} ppm, above the 500 ppm palatability limit, which can indicate ingress or saline intrusion.",
        'action': 'Use an alternate supply for drinking and cooking where available.'
    },
]

# (rule_key, station_id) -> alert id currently in force
active_auto_alerts: dict[tuple[str, str], str] = {}

def _auto_alert_from(rule, station) -> dict:
    return {
        'id': f"auto-{rule['key']}-{station['id']}-{uuid.uuid4().hex[:4]}",
        'level': rule['level'],
        'title': rule['title'](station),
        'body': rule['body'](station),
        'regions': [station['area']],
        'evidence': [
            f"Automated sensor threshold breach at {station['name']}",
            f"pH {station['ph']} · TDS {station['tds']} ppm · Turbidity {station['turbidity']} NTU · Chlorine {station['chlorine']} ppm"
        ],
        'action': rule['action'],
        'time': now_iso(),
        'source': 'HydroSignal Automated Contamination Watch',
        'automated': True,
        'unverified': True,   # no human officer has reviewed this
        'rule': rule['key'],
        'station_id': station['id']
    }

def evaluate_auto_warnings() -> list[dict]:
    """Trip or stand down automatic contamination warnings. Returns broadcast payloads."""
    events = []
    for station in water_stations:
        for rule in CONTAMINATION_RULES:
            state_key = (rule['key'], station['id'])
            in_force = state_key in active_auto_alerts

            if not in_force and rule['trip'](station):
                alert = _auto_alert_from(rule, station)
                alerts.insert(0, alert)
                del alerts[25:]
                active_auto_alerts[state_key] = alert['id']
                log_signal('threshold', f"{rule['key'].upper()} threshold breached at {station['name']} — automatic {rule['level']} warning issued", rule['level'])
                events.append({'event': 'new_bulletin', 'alert': alert, 'automated': True})

            elif in_force and rule['clear'](station):
                alert_id = active_auto_alerts.pop(state_key)
                alerts[:] = [a for a in alerts if a.get('id') != alert_id]
                log_signal('threshold', f"{rule['key'].upper()} at {station['name']} returned inside safe limits — warning stood down", 'clear')
                events.append({
                    'event': 'alert_cleared',
                    'alert_id': alert_id,
                    'message': f"All clear — {rule['key']} at {station['name']} back within safe limits."
                })
    return events

# --- Pydantic Schemas ---
class UserAuth(BaseModel):
    username: str
    password: str

class UserRegister(BaseModel):
    username: str
    password: str
    role: str = 'user' # 'user' or 'admin'
    name: str = ''
    area: str = 'oldtown'
    department: str = ''
    admin_code: str = ''   # required to self-register as a municipal officer

class ProblemReportSubmit(BaseModel):
    type: str = Field(pattern='^(illness|water|flood|waterlog|sanit)$')
    title: str
    note: str
    area: str
    lat: float | None = None
    lng: float | None = None
    severity: int = Field(default=2, ge=1, le=5)
    submitter_name: str | None = 'Community Resident'

class AdminBulletinCreate(BaseModel):
    title: str
    body: str
    level: str = 'watch' # 'watch' | 'elevated' | 'high'
    regions: list[str] = []
    evidence: list[str] = []
    action: str = ''

# --- REST Endpoints ---

@app.get('/api/health')
def health():
    return {'status': 'healthy', 'service': 'HydroSignal Early Warning API', 'version': '2.0.0', 'time': now_iso()}

# Auth Endpoints
@app.post('/api/auth/register')
def register(body: UserRegister):
    uname = body.username.strip().lower()
    if not uname or len(body.password) < 6:
        raise HTTPException(400, 'Username required and password must be at least 6 characters')
    if uname in USERS:
        raise HTTPException(400, 'Username already exists')

    role = 'user'
    if body.role == 'admin':
        # Officer accounts publish public health warnings; they are not self-serve.
        if not hmac.compare_digest(body.admin_code, ADMIN_SIGNUP_CODE):
            raise HTTPException(403, 'A valid municipal authorisation code is required for officer accounts')
        role = 'admin'

    USERS[uname] = {
        'username': uname,
        'password_hash': hash_password(body.password),
        'role': role,
        'name': body.name or uname.title(),
        'area': body.area,
        'department': body.department
    }
    save_state()
    token = issue_session(USERS[uname])
    return {'ok': True, 'username': uname, 'role': role,
            'name': USERS[uname]['name'], 'token': token}

@app.post('/api/auth/login')
def login(body: UserAuth):
    uname = body.username.strip().lower()
    user = USERS.get(uname)

    if user is None:
        # Demo convenience: an unknown username signs in as a RESIDENT and the account
        # is created. It never yields officer access — that used to be granted to any
        # username containing "admin", which is how anyone could broadcast a warning.
        if len(body.password) < 4:
            raise HTTPException(401, 'Invalid credentials')
        USERS[uname] = {
            'username': uname,
            'password_hash': hash_password(body.password),
            'role': 'user',
            'name': uname.title(),
            'area': 'oldtown'
        }
        save_state()
        user = USERS[uname]
    elif not verify_password(body.password, user.get('password_hash', '')):
        raise HTTPException(401, 'Invalid credentials')

    token = issue_session(user)
    return {
        'ok': True,
        'username': user['username'],
        'role': user['role'],
        'name': user.get('name', uname),
        'department': user.get('department', ''),
        'token': token
    }

@app.get('/api/auth/me')
def whoami(sess: dict = Depends(require_auth)):
    """The client validates its stored session here rather than trusting localStorage,
    where the role was previously just an editable string."""
    return {'ok': True, 'username': sess['username'], 'role': sess['role'], 'name': sess['name']}

@app.post('/api/auth/logout')
def logout(authorization: str | None = Header(default=None)):
    if authorization:
        token = authorization[7:].strip() if authorization.lower().startswith('bearer ') else authorization.strip()
        SESSIONS.pop(token, None)
    return {'ok': True}

# Weather / Environmental Hyperlocal Free API (Open-Meteo Integration)
@app.get('/api/weather/hyperlocal')
async def get_weather(lat: float = CENTER_COORDS['lat'], lng: float = CENTER_COORDS['lng']):
    # Serve the same rainfall the risk model is using, so the UI and the score agree.
    if weather_state['fetched_at'] is None:
        await refresh_weather_state()

    rain_sum_24h = weather_state['rain_24h_mm']
    flood_risk = 'Low'
    if rain_sum_24h > 60:
        flood_risk = 'Severe Waterlogging Hazard'
    elif rain_sum_24h > 25:
        flood_risk = 'Moderate Drainage Stress'

    return {
        'ok': True,
        'source': weather_state['source'],
        'lat': lat,
        'lng': lng,
        'current_rain_mm': weather_state['current_rain_mm'],
        'rain_24h_sum_mm': rain_sum_24h,
        'flood_risk_level': flood_risk,
        'surface_pressure_hpa': weather_state['surface_pressure_hpa'],
        'feeds_model': True,
        'model_points': rain_points(),
        'fetched_at': weather_state['fetched_at'],
        'timestamp': now_iso()
    }

# Water Quality Endpoints (Factor 6)
@app.get('/api/water/stations')
def get_water_stations():
    for s in water_stations:
        s['wqi'] = calc_wqi(s['ph'], s['tds'], s['turbidity'], s['chlorine'])
    return {
        'stations': water_stations,
        'city_wqi': round(sum(s['wqi'] for s in water_stations) / len(water_stations)),
        'timestamp': now_iso()
    }

@app.get('/api/water/trends')
def get_water_trends():
    # Return aggregated time-series for graph plotting
    timestamps = [f"T-{5-i}h" for i in range(6)]
    avg_ph = [round(sum(s['history_ph'][i] for s in water_stations) / len(water_stations), 2) for i in range(6)]
    avg_tds = [round(sum(s['history_tds'][i] for s in water_stations) / len(water_stations)) for i in range(6)]
    return {
        'timestamps': timestamps,
        'avg_ph': avg_ph,
        'avg_tds': avg_tds,
        'safe_ph_min': 6.5,
        'safe_ph_max': 8.5,
        'safe_tds_max': 500
    }

# Reports Management (Factors 4 & 5)
@app.post('/api/reports/submit')
async def submit_report(body: ProblemReportSubmit):
    d = next((d for d in DISTRICTS if d['id'] == body.area), None)
    lat = body.lat or (d['lat'] + random.uniform(-0.005, 0.005) if d else CENTER_COORDS['lat'])
    lng = body.lng or (d['lng'] + random.uniform(-0.005, 0.005) if d else CENTER_COORDS['lng'])

    new_report = {
        'id': f"rep-{uuid.uuid4().hex[:8]}",
        'type': body.type,
        'title': body.title,
        'note': body.note,
        'area': body.area,
        'lat': round(lat, 5),
        'lng': round(lng, 5),
        'severity': body.severity,
        'status': 'pending_approval',  # Crucial requirement: not shown publicly until admin verifies
        'submitter': body.submitter_name or 'Community Resident',
        'time': now_iso(),
        'approved_by': None,
        'approved_at': None,
        'origin': 'community'
    }
    reports.insert(0, new_report)
    save_state()
    log_signal('report', f"New {body.type} report filed in {body.area.title()} (severity {body.severity}/5) — awaiting verification")

    # Broadcast to admin desks via WebSocket
    await hub.broadcast({
        'event': 'new_pending_report',
        'report': new_report,
        'message': f"New {body.type.upper()} report from {body.area.title()} awaiting verification"
    })

    return {
        'ok': True,
        'report': new_report,
        'message': 'Report submitted successfully. It has been routed to the Municipal Health Desk for verification before being displayed.'
    }

@app.get('/api/reports/approved')
def get_approved_reports(category: str | None = None):
    # Public view only sees approved reports
    res = [r for r in reports if r['status'] == 'approved']
    # Newest verification first, so a report the admin just approved leads the feed
    res.sort(key=lambda r: r.get('approved_at') or r.get('time') or '', reverse=True)
    if category and category != 'all':
        if category == 'community':
            res = [r for r in res if r.get('origin') == 'community']
        else:
            res = [r for r in res if r['type'] == category]
    return {'reports': res, 'total': len(res),
            'community_total': len([r for r in res if r.get('origin') == 'community'])}

@app.get('/api/admin/reports/pending')
def get_pending_reports(sess: dict = Depends(require_admin)):
    res = [r for r in reports if r['status'] == 'pending_approval']
    return {'pending_reports': res, 'total': len(res)}

@app.get('/api/admin/reports/all')
def get_all_reports(sess: dict = Depends(require_admin)):
    return {'reports': reports, 'total': len(reports)}

@app.post('/api/admin/reports/{report_id}/approve')
async def approve_report(report_id: str, sess: dict = Depends(require_admin)):
    admin_user = sess['username']
    r = next((x for x in reports if x['id'] == report_id), None)
    if not r:
        raise HTTPException(404, 'Report not found')
    r['status'] = 'approved'
    r['approved_by'] = admin_user
    r['approved_at'] = now_iso()
    save_state()
    log_signal('report', f"Report verified and published: {r['title']} ({r['area'].title()}, severity {r['severity']}/5)", 'watch')

    prediction = compute_system_prediction()
    map_data = get_map_snapshot()

    # Broadcast approval to all connected users so map & public feed immediately update
    await hub.broadcast({
        'event': 'report_approved',
        'report': r,
        'prediction': prediction,
        'map': map_data
    })

    return {'ok': True, 'report': r, 'message': 'Report verified and published to public surveillance map.'}

@app.post('/api/admin/reports/{report_id}/reject')
async def reject_report(report_id: str, sess: dict = Depends(require_admin)):
    r = next((x for x in reports if x['id'] == report_id), None)
    if not r:
        raise HTTPException(404, 'Report not found')
    r['status'] = 'rejected'
    r['approved_at'] = now_iso()
    save_state()

    await hub.broadcast({
        'event': 'report_rejected',
        'report_id': report_id
    })

    return {'ok': True, 'message': 'Report rejected/dismissed.'}

@app.post('/api/admin/bulletins')
async def create_bulletin(body: AdminBulletinCreate, sess: dict = Depends(require_admin)):
    new_alert = {
        'id': f"alt-{uuid.uuid4().hex[:6]}",
        'level': body.level,
        'title': body.title,
        'body': body.body,
        'regions': body.regions,
        'evidence': body.evidence,
        'action': body.action,
        'time': now_iso(),
        'source': 'Municipal Corporation & Health Directorate',
        'issued_by': sess['username']
    }
    alerts.insert(0, new_alert)
    del alerts[25:]
    save_state()

    await hub.broadcast({
        'event': 'new_bulletin',
        'alert': new_alert
    })

    return {'ok': True, 'alert': new_alert}

@app.get('/api/alerts')
def get_alerts():
    return {'alerts': alerts}

@app.post('/api/admin/simulate/contamination')
async def simulate_contamination(station_id: str | None = None, rule: str = 'turbidity', restore: bool = False,
                                 sess: dict = Depends(require_admin)):
    """Demo hook: force a station across (or back inside) a contamination threshold
    so the automatic warning path can be exercised without waiting for sensor drift."""
    st = next((s for s in water_stations if s['id'] == station_id), None) if station_id else water_stations[0]
    if not st:
        raise HTTPException(404, 'Station not found')

    breach = {'turbidity': ('turbidity', 9.4), 'ph': ('ph', 5.9), 'chlorine': ('chlorine', 0.05),
              'tds': ('tds', 585), 'microbial': ('microbial', 'E. coli detected')}
    safe = {'turbidity': ('turbidity', 1.4), 'ph': ('ph', 7.2), 'chlorine': ('chlorine', 0.45),
            'tds': ('tds', 230), 'microbial': ('microbial', 'absent')}

    table = safe if restore else breach
    if rule not in table:
        raise HTTPException(400, f'Unknown rule: {rule}')

    field, value = table[rule]
    st[field] = value
    st['wqi'] = calc_wqi(st['ph'], st['tds'], st['turbidity'], st['chlorine'])

    log_signal('simulation', f"Manual scenario: {rule} {'restored' if restore else 'forced to breach'} at {st['name']}",
               'clear' if restore else 'high')

    for ev in evaluate_auto_warnings():
        await hub.broadcast(ev)

    prediction = compute_system_prediction()
    record_prediction_point(prediction)
    await hub.broadcast({'event': 'sensor_tick', 'water': water_stations,
                         'prediction': {**prediction,
                                        'history': list(probability_history)[-60:],
                                        'signals': list(signal_log)[:25]},
                         'timestamp': now_iso()})

    return {'ok': True, 'station': st['name'], 'rule': rule, 'restored': restore,
            'active_auto_alerts': len(active_auto_alerts)}

# AI Outbreak Prediction Endpoint
@app.get('/api/outbreak/predict')
def get_ai_prediction():
    pred = compute_system_prediction()
    return {**pred, 'history': list(probability_history)[-60:], 'signals': list(signal_log)[:25]}

@app.get('/api/outbreak/history')
def get_prediction_history(limit: int = 60):
    return {'history': list(probability_history)[-limit:]}

@app.get('/api/outbreak/signals')
def get_signal_log(limit: int = 25):
    return {'signals': list(signal_log)[:limit]}

# Historical Clusters & Contamination Archive (Factor 7)
@app.get('/api/clusters/history')
def get_historical_clusters():
    return {'clusters': historical_clusters, 'total': len(historical_clusters)}

# Nearby Healthcare & Pharmacies Directory (Factor 9)
@app.get('/api/healthcare/nearby')
def get_nearby_healthcare(lat: float = CENTER_COORDS['lat'], lng: float = CENTER_COORDS['lng'], radius_km: float = 100.0):
    results = []
    for f in nearby_facilities:
        dist = haversine(lat, lng, f['lat'], f['lng'])
        if dist <= radius_km:
            results.append({**f, 'distance_km': dist})
    results.sort(key=lambda x: x['distance_km'])
    return {'facilities': results, 'user_lat': lat, 'user_lng': lng, 'radius_km': radius_km}

# Map Snapshot Payload
def get_map_snapshot():
    # Only send approved reports to public map
    approved_reports = [r for r in reports if r['status'] == 'approved']
    markers = []
    for r in approved_reports[-120:]:
        markers.append({
            'id': r['id'],
            'type': r['type'],
            'title': r['title'],
            'area': r['area'],
            'lat': r['lat'],
            'lng': r['lng'],
            'severity': r['severity'],
            'note': r['note'],
            'time': r['time']
        })

    # Add water stations as markers
    for s in water_stations:
        markers.append({
            'id': f"station-{s['id']}",
            'type': 'water_station',
            'title': s['name'],
            'area': s['area'],
            'lat': s['lat'],
            'lng': s['lng'],
            'severity': 3 if s['turbidity'] > 3.0 or s['ph'] < 6.5 or s['ph'] > 8.5 else 1,
            'ph': s['ph'],
            'tds': s['tds'],
            'turbidity': s['turbidity'],
            'wqi': s['wqi'],
            'time': now_iso()
        })

    # Add healthcare facilities as map markers
    for h in nearby_facilities:
        markers.append({
            'id': h['id'],
            'type': 'healthcare' if h['type'] in ('Hospital', 'PHC', 'Clinic') else 'pharmacy',
            'title': h['name'],
            'lat': h['lat'],
            'lng': h['lng'],
            'phone': h['phone'],
            'hours': h['hours'],
            'ors': h.get('ors_stock', 'In Stock'),
            'time': now_iso()
        })

    # Calculate thermal clusters (heatmap points: lat, lng, intensity 0-1)
    heat_points = []
    for r in approved_reports:
        weight = 0.4 + (r['severity'] / 5.0) * 0.6
        heat_points.append([r['lat'], r['lng'], weight])
    for s in water_stations:
        if s['wqi'] < 80:
            heat_points.append([s['lat'], s['lng'], (100 - s['wqi']) / 100.0])

    return {
        'center': CENTER_COORDS,
        'default_radius_km': 50,
        'max_radius_km': 100,
        'markers': markers,
        'heat_points': heat_points,
        'districts': DISTRICTS
    }

@app.get('/api/monitoring/map')
def monitoring_map():
    return get_map_snapshot()

# WebSocket for Real-time Monitoring
@app.websocket('/ws/monitor')
async def websocket_monitor(ws: WebSocket):
    await ws.accept()
    hub.clients.add(ws)
    try:
        # Initial snapshot
        await ws.send_json({
            'event': 'snapshot',
            'prediction': {**compute_system_prediction(),
                           'history': list(probability_history)[-60:],
                           'signals': list(signal_log)[:25]},
            'map': get_map_snapshot(),
            'water': water_stations,
            'alerts': alerts[:15],
            'pending_count': len([r for r in reports if r['status'] == 'pending_approval'])
        })
        while True:
            await ws.receive_text()
    except WebSocketDisconnect:
        hub.clients.discard(ws)
    except Exception:
        hub.clients.discard(ws)

# Realtime Sensor & Event Simulator
async def background_simulator():
    tick = 0
    last_band = None
    while True:
        await asyncio.sleep(4)
        tick += 1
        try:
            # Rainfall is a live external input; refresh it every ~5 minutes.
            if tick % 75 == 1:
                before = weather_state['rain_24h_mm']
                await refresh_weather_state()
                if abs(weather_state['rain_24h_mm'] - before) >= 1.0:
                    log_signal('weather', f"24h rainfall updated to {weather_state['rain_24h_mm']} mm ({weather_state['source']})")
            # Small realistic drift in water sensors
            for s in water_stations:
                s['turbidity'] = round(max(0.4, min(24.0, s['turbidity'] + random.uniform(-0.06, 0.06))), 2)
                s['ph'] = round(max(6.2, min(8.8, s['ph'] + random.uniform(-0.02, 0.02))), 2)
                s['tds'] = round(max(140, min(650, s['tds'] + random.uniform(-1.5, 1.5))))
                s['wqi'] = calc_wqi(s['ph'], s['tds'], s['turbidity'], s['chlorine'])
                # Shift historical trend
                s['history_ph'].append(s['ph'])
                s['history_tds'].append(s['tds'])
                if len(s['history_ph']) > 12:
                    s['history_ph'].pop(0)
                    s['history_tds'].pop(0)

            # Automatic contamination warnings are evaluated every tick, whether or
            # not anyone is connected, so the alert list is correct when they arrive.
            auto_events = evaluate_auto_warnings()

            prediction = compute_system_prediction()
            record_prediction_point(prediction)

            if last_band is not None and prediction['risk_band'] != last_band:
                log_signal('band',
                           f"Risk band moved {last_band.upper()} to {prediction['risk_band'].upper()} "
                           f"({prediction['probability_percent']}% probability)",
                           prediction['risk_band'])
            last_band = prediction['risk_band']

            if hub.clients:
                await hub.broadcast({
                    'event': 'sensor_tick',
                    'water': water_stations,
                    'prediction': {**prediction,
                                   'history': list(probability_history)[-60:],
                                   'signals': list(signal_log)[:25]},
                    'timestamp': now_iso()
                })
                for ev in auto_events:
                    await hub.broadcast(ev)
        except Exception:
            pass

async def _startup():
    restored = load_state()
    await refresh_weather_state()
    record_prediction_point(compute_system_prediction())
    log_signal('system',
               'Surveillance engine online — telemetry, rainfall and report feeds connected'
               + (' · previous state restored' if restored else ''))
    asyncio.create_task(background_simulator())


# Mount Frontend
app.mount('/', StaticFiles(directory=str(FRONTEND), html=True), name='frontend')
