"""
Tipset-optimeraren – fotbollskuponger (Svenska Spel, Expekt) och V85 (ATG)
=========================================================================

Streamlit-app som bygger ett matematiskt optimerat M-system utifrån en budget.
Kuponger och odds kan hämtas live för Stryktipset, Europatipset och Topptipset.

Algoritmens enda mål är att MAXIMERA VINSTCHANSEN (sannolikhet & säkerhet):
    * De mest spelsäkra matcherna spikas.
    * De mest svårförutsägbara matcherna helgarderas.
    * Övriga matcher halvgarderas med de två mest sannolika tecknen.
Inga rensare / reduceringar används – utdelning jagas aldrig.

Kör:  streamlit run app.py
"""

from __future__ import annotations

import hashlib
import hmac
import html
import json
import os
import re
import time
import unicodedata
import urllib.error
import urllib.parse
import urllib.request
from dataclasses import dataclass
from difflib import SequenceMatcher
from datetime import datetime, timedelta
from pathlib import Path
from typing import Any

try:  # Python 3.11+
    import tomllib
except ImportError:  # äldre Python: Streamlits egen inläsning används
    tomllib = None  # type: ignore[assignment]

import numpy as np
import pandas as pd
import streamlit as st

# ---------------------------------------------------------------------------
# Konstanter
# ---------------------------------------------------------------------------

SIGNS: tuple[str, str, str] = ("1", "X", "2")
ODDS_COLS: list[str] = ["Odds 1", "Odds X", "Odds 2"]
TEAM_COLS: list[str] = ["Hemmalag", "Bortalag"]
# Svenska folkets streckfördelning (% av alla spelade rader per tecken).
FOLK_COLS: list[str] = ["Folket 1 %", "Folket X %", "Folket 2 %"]

TYPE_SPIK = "Spik"
TYPE_HALV = "Halv"
TYPE_HEL = "Hel"

# Förinställd mock-kupong (hemmalag, bortalag, odds 1, odds X, odds 2).
# De 8 första används för 8-matcherskupongen, alla 13 för 13-matcherskupongen.
MOCK_MATCHES: list[tuple[str, str, float, float, float]] = [
    ("Arsenal", "Everton", 1.40, 4.80, 8.00),
    ("Liverpool", "Aston Villa", 1.65, 4.10, 4.80),
    ("Brentford", "Fulham", 2.45, 3.40, 2.90),
    ("Bayern München", "Mainz", 1.22, 6.75, 12.00),
    ("Real Sociedad", "Villarreal", 2.60, 3.20, 2.75),
    ("Inter", "Lazio", 1.75, 3.70, 4.60),
    ("Lyon", "Lens", 2.20, 3.40, 3.25),
    ("Ajax", "Twente", 1.95, 3.70, 3.60),
    ("Leeds", "Sunderland", 2.10, 3.40, 3.50),
    ("Hammarby", "AIK", 2.30, 3.40, 3.00),
    ("Benfica", "Braga", 1.70, 3.90, 4.70),
    ("Celtic", "Hearts", 1.33, 5.25, 8.50),
    ("PSV", "Feyenoord", 1.85, 3.90, 3.80),
]


# Svenska Spels (odokumenterade) draw-endpoints.
# Endast FOTBOLLSspel med 1X2-format hämtas. Hockeyspel (Powerplay) och spel med
# andra format (Måltipset, Bomben, Matchen) ingår medvetet inte – de passar inte
# M-systemlogiken. "topptipsetfamily" kan innehålla flera omgångar samtidigt
# (t.ex. Topptipset, Topptipset Europa, Topptipset Extra).
API_BASE = "https://api.spela.svenskaspel.se/draw/1"
API_PRODUCTS: dict[str, str] = {
    "stryktipset": "Stryktipset",
    "europatipset": "Europatipset",
    "topptipsetfamily": "Topptipset",
}
API_TIMEOUT_S = 10

# Expekt-Tipset körs på PoolX-plattformen, som saknar öppet API. Kupongen klistras
# därför in av användaren och oddsen hämtas från Svenska Spels öppna omgångar.
EXPEKT_URL = "https://www.expekt.se/sports/expekt-tipset"
EXPEKT_GAMES: dict[str, tuple[str, int]] = {
    "fotboll13": ("Fotboll 13 (lördag)", 13),
    "fotboll12": ("Fotboll 12 (söndag)", 12),
    "fotboll8": ("Fotboll 8 (flera gånger i veckan)", 8),
}

# Sporter som utesluts om en omgång/match uttryckligen anger sport.
NON_FOOTBALL_KEYWORDS: tuple[str, ...] = (
    "hockey", "ishockey", "bandy", "handboll", "handball", "basket", "tennis",
    "innebandy", "floorball", "trav", "golf",
)
SPORT_FIELDS: tuple[str, ...] = ("sport", "sportName", "sportType", "sportTypeName")
# Fält där Svenska Spel kan lägga odds, i prioritetsordning (aktuella först).
ODDS_FIELDS: tuple[str, ...] = ("odds", "startOdds", "favouriteOdds")
# Fält där Svenska Spel kan lägga Svenska folkets streckfördelning.
FOLK_FIELDS: tuple[str, ...] = ("svenskaFolket", "distribution", "betDistribution")

# ESPN:s öppna (odokumenterade) data-API används för lagform – ingen nyckel krävs.
# Ligor som Svenska Spels fotbollskuponger brukar innehålla. Ligor som inte svarar hoppas över.
ESPN_BASE = "https://site.api.espn.com/apis/site/v2/sports/soccer"
ESPN_LEAGUES: dict[str, str] = {
    "eng.1": "Premier League", "eng.2": "Championship", "eng.3": "League One", "eng.4": "League Two",
    "esp.1": "La Liga", "esp.2": "LaLiga 2", "ger.1": "Bundesliga", "ger.2": "2. Bundesliga",
    "ita.1": "Serie A", "ita.2": "Serie B", "fra.1": "Ligue 1", "fra.2": "Ligue 2",
    "ned.1": "Eredivisie", "por.1": "Primeira Liga", "bel.1": "Jupiler Pro League",
    "sco.1": "Scottish Premiership", "tur.1": "Süper Lig", "swe.1": "Allsvenskan",
    "swe.2": "Superettan", "nor.1": "Eliteserien", "den.1": "Superligaen", "usa.1": "MLS",
}
FORM_MATCHES = 5
ESPN_ODDS_DAYS = 10            # hur många dagar framåt ESPN-odds hämtas
ESPN_ODDS_CACHE_TTL_S = 30 * 60
FORM_CACHE_TTL_S = 6 * 3600
TEAM_INDEX_TTL_S = 24 * 3600
NAME_MATCH_THRESHOLD = 0.72  # lägsta namnlikhet (0–1) för att räkna som samma lag
FORM_COLORS: dict[str, str] = {"V": "#2e7d32", "O": "#757575", "F": "#c62828"}

# Skadeläge. Fantasy Premier Leagues öppna API täcker alla PL-lag (ingen nyckel).
FPL_URL = "https://fantasy.premierleague.com/api/bootstrap-static/"
FPL_STATUS: dict[str, str] = {"i": "skadad", "d": "tveksam", "s": "avstängd"}
FPL_ALIASES: dict[str, list[str]] = {  # FPL:s kortnamn -> vanliga fullständiga namn
    "Spurs": ["Tottenham", "Tottenham Hotspur"],
    "Man Utd": ["Manchester United", "Manchester U"],
    "Man City": ["Manchester City", "Manchester C"],
    "Nott'm Forest": ["Nottingham Forest", "Nottingham"],
    "Wolves": ["Wolverhampton", "Wolverhampton Wanderers"],
    "Newcastle": ["Newcastle United"],
    "West Ham": ["West Ham United"],
    "Brighton": ["Brighton & Hove Albion", "Brighton and Hove Albion"],
}
FPL_MATCH_THRESHOLD = 0.80
INJURY_CACHE_TTL_S = 3600
INJURY_COLS: tuple[str, str] = ("Skador hemma", "Skador borta")
# Hittar appen inga skador länkas SportsGamblers skadelista (endast länk – ingen hämtning,
# enligt deras villkor). Sajten har en sida per liga där varje lag har en egen sektion.
SG_BASE = "https://www.sportsgambler.com/injuries/football/"
SG_LEAGUES: dict[str, str] = {  # ESPN-liga -> SportsGambler-slug
    "eng.1": "england-premier-league", "eng.2": "england-championship",
    "esp.1": "spain-la-liga", "esp.2": "spain-la-liga-2",
    "ger.1": "germany-bundesliga", "ger.2": "germany-2-bundesliga",
    "ita.1": "italy-serie-a", "ita.2": "italy-serie-b", "fra.1": "france-ligue-1",
    "ned.1": "netherlands-eredivisie", "por.1": "portugal-primeira-liga",
    "bel.1": "belgium-first-division-a", "sco.1": "scottish-premiership",
    "tur.1": "turkey-super-lig", "swe.1": "sweden-allsvenskan", "nor.1": "norway-eliteserien",
    "den.1": "denmark-superliga", "usa.1": "usa-mls",
}

# V85 (trav) via ATG:s racinginfo-API (odokumenterat, ingen nyckel).
ATG_BASE = "https://www.atg.se/services/racinginfo/v1/api"
V85_TYPE = "V85"
V85_MAX_ROWS = 5000
V85_STAKES: dict[str, float] = {  # insats per rad
    "50 öre (ordinarie)": 0.50, "35 öre (70 %)": 0.35, "25 öre (50 %)": 0.25, "15 öre (30 %)": 0.15,
}
ATG_LIST_TTL_S = 10 * 60
ATG_GAME_TTL_S = 2 * 60

# Google Gemini (AI-analys). Nyckel skapas i Google AI Studio.
GEMINI_ENDPOINT = "https://generativelanguage.googleapis.com/v1beta/models/{model}:generateContent"
# Första = standard. De tre första har gratisnivå i API:t (okt 2026); 2.5 kräver tidigare användning.
GEMINI_MODELS: list[str] = [
    "gemini-3.5-flash-lite",
    "gemini-3-flash-preview",
    "gemini-3.1-flash-lite",
    "gemini-2.5-flash",
]
GEMINI_TIMEOUT_S = 60
GEMINI_SYSTEM_PROMPT = (
    "Du är en saklig analytiker av M-system på Svenska Spels fotbollskuponger (Stryktipset, "
    "Europatipset, Topptipset). Systemets mål är att maximera chansen till alla rätt, inte att "
    "jaga hög utdelning. Svara på svenska i högst cirka 180 ord, med korta punkter under rubrikerna "
    "**Sammanfattning**, **Svagaste punkter** och **Förslag**. Utgå från siffrorna du får: peka ut "
    "matcherna med lägst täckt sannolikhet, spikar som är riskabla, och om garderingar kan flyttas "
    "för högre vinstchans till samma kostnad. Kommentera lagform, skadeläge och Svenska folkets "
    "fördelning bara om de tillför något – särskilt viktiga skador på spikade lag. Hitta inte på "
    "fakta om lag, skador eller nyheter utöver underlaget. Lova aldrig vinst."
)


# ---------------------------------------------------------------------------
# Hämtning av verkliga kuponger från Svenska Spel
# ---------------------------------------------------------------------------

class FetchError(Exception):
    """Fel vid hämtning eller tolkning av en kupong från Svenska Spel."""


def fetch_draws(product: str) -> list[dict[str, Any]]:
    """Hämtar öppna omgångar för en produkt. Kastar FetchError vid problem."""
    url = f"{API_BASE}/{product}/draws"
    request = urllib.request.Request(
        url,
        headers={"Accept": "application/json", "User-Agent": "Mozilla/5.0 (Tipset-optimeraren)"},
    )
    try:
        with urllib.request.urlopen(request, timeout=API_TIMEOUT_S) as response:
            payload = json.load(response)
    except urllib.error.HTTPError as exc:
        raise FetchError(f"Svenska Spel svarade med HTTP {exc.code} ({url}).") from exc
    except (urllib.error.URLError, TimeoutError) as exc:
        raise FetchError(f"Kunde inte nå Svenska Spel: {exc}") from exc
    except json.JSONDecodeError as exc:
        raise FetchError("Svaret från Svenska Spel var inte giltig JSON.") from exc

    if isinstance(payload, dict):
        draws = payload.get("draws")
        if draws is None and isinstance(payload.get("draw"), dict):
            draws = [payload["draw"]]
    else:
        draws = payload
    if not isinstance(draws, list):
        keys = ", ".join(payload.keys()) if isinstance(payload, dict) else type(payload).__name__
        raise FetchError(f"Oväntat svarsformat (toppnivå: {keys}).")
    return [d for d in draws if isinstance(d, dict)]


def _draw_events(draw: dict[str, Any]) -> list[dict[str, Any]]:
    """Matcherna i en omgång, sorterade i kupongordning."""
    events = draw.get("drawEvents") or draw.get("events") or []
    return sorted(
        (e for e in events if isinstance(e, dict)),
        key=lambda e: e.get("eventNumber", 0),
    )


def _parse_odds_value(value: Any) -> float:
    """Tolkar ett odds som kan vara '1,45', '1.45', 1.45 eller saknas."""
    if value is None or value == "":
        return float("nan")
    try:
        return float(str(value).replace(",", "."))
    except ValueError:
        return float("nan")


def _event_odds(event: dict[str, Any]) -> tuple[float, float, float]:
    """Första kompletta 1X2-oddsen enligt ODDS_FIELDS, annars NaN."""
    for field in ODDS_FIELDS:
        block = event.get(field)
        if isinstance(block, dict):
            odds = tuple(_parse_odds_value(block.get(k)) for k in ("one", "x", "two"))
            if all(not np.isnan(o) for o in odds):
                return odds  # type: ignore[return-value]
    return (float("nan"),) * 3  # type: ignore[return-value]


def _event_teams(event: dict[str, Any]) -> tuple[str, str]:
    """Hemma- och bortalag ur participants, annars ur eventDescription ('A - B')."""
    participants = (event.get("match") or {}).get("participants") or event.get("participants") or []
    home = next((p.get("name") for p in participants if p.get("type") == "home"), None)
    away = next((p.get("name") for p in participants if p.get("type") == "away"), None)
    if home and away:
        return str(home), str(away)

    description = str(event.get("eventDescription") or event.get("description") or "")
    for sep in (" - ", " – ", "-"):
        if sep in description:
            left, right = description.split(sep, 1)
            return left.strip(), right.strip()
    return description or f"Match {event.get('eventNumber', '?')}", ""


def _event_folk(event: dict[str, Any]) -> tuple[float, float, float]:
    """Svenska folkets fördelning i procent (1, X, 2), annars NaN."""
    for field in FOLK_FIELDS:
        block = event.get(field)
        if isinstance(block, dict):
            folk = tuple(_parse_odds_value(block.get(k)) for k in ("one", "x", "two"))
            if all(not np.isnan(v) for v in folk):
                return folk  # type: ignore[return-value]
    return (float("nan"),) * 3  # type: ignore[return-value]


def draw_to_coupon(draw: dict[str, Any]) -> tuple[pd.DataFrame, list[int]]:
    """
    Omvandlar en omgång till kupong-DataFrame.
    Returnerar även matchnummer (1-baserade) där odds saknas, så att användaren
    kan fylla i dem manuellt.
    """
    rows: list[tuple[Any, ...]] = []
    missing: list[int] = []
    for i, event in enumerate(_draw_events(draw), start=1):
        home, away = _event_teams(event)
        odds = _event_odds(event)
        if any(np.isnan(o) for o in odds):
            missing.append(i)
        rows.append((home, away, *odds, *_event_folk(event)))
    return pd.DataFrame(rows, columns=TEAM_COLS + ODDS_COLS + FOLK_COLS), missing


def draw_label(draw: dict[str, Any]) -> str:
    """Läsbar etikett för en omgång, t.ex. 'Topptipset omg. 2431 – stänger 2026-10-25 15:59'."""
    name = draw.get("productName") or "Omgång"
    number = draw.get("drawNumber", "?")
    close = str(draw.get("regCloseTime") or draw.get("closeTime") or "")
    close_txt = close[:16].replace("T", " ") if close else "okänd stängning"
    return f"{name} omg. {number} – stänger {close_txt}"


def _sport_names(obj: dict[str, Any]) -> list[str]:
    """Sportangivelser (som text) i ett objekt och dess eventuella 'match'/'sportEvent'."""
    found: list[str] = []
    for container in (obj, obj.get("match") or {}, obj.get("sportEvent") or {}):
        if not isinstance(container, dict):
            continue
        for field in SPORT_FIELDS:
            value = container.get(field)
            if isinstance(value, dict):
                value = value.get("name") or value.get("description")
            if isinstance(value, str) and value.strip():
                found.append(value.lower())
    return found


def is_football_draw(draw: dict[str, Any]) -> bool:
    """
    Sant om omgången är fotboll med 1X2-matcher.

    Produkterna i API_PRODUCTS är fotbollsspel, men som extra skydd utesluts en
    omgång om omgången eller någon match uttryckligen anger en annan sport,
    eller om matcherna saknar 1X2-oddsstruktur helt.
    """
    events = _draw_events(draw)
    if not events:
        return False
    for obj in (draw, *events):
        if any(kw in name for name in _sport_names(obj) for kw in NON_FOOTBALL_KEYWORDS):
            return False
    # Minst en match måste ha ett 1X2-oddsblock (även om värdena ännu är tomma).
    return any(
        isinstance(e.get(f), dict) and {"one", "x", "two"} <= set(e[f])
        for e in events for f in ODDS_FIELDS
    )


def fetch_all_football_draws(
    products: dict[str, str] | None = None,
) -> tuple[list[dict[str, Any]], list[str]]:
    """
    Hämtar alla öppna fotbollsomgångar från valda produkter (standard: alla i API_PRODUCTS).
    Ett fel i en produkt stoppar inte de andra. Returnerar (omgångar, felmeddelanden).
    """
    draws: list[dict[str, Any]] = []
    errors: list[str] = []
    seen: set[tuple[str, Any]] = set()

    for product, display_name in (products or API_PRODUCTS).items():
        try:
            product_draws = fetch_draws(product)
        except FetchError as exc:
            errors.append(f"{display_name}: {exc}")
            continue
        for draw in product_draws:
            draw.setdefault("productName", display_name)
            ident = (str(draw.get("productName")), draw.get("drawNumber"))
            if ident in seen or not is_football_draw(draw):
                continue
            seen.add(ident)
            draws.append(draw)

    # Sortera på stängningstid så att närmast stängande omgång kommer först.
    draws.sort(key=lambda d: str(d.get("regCloseTime") or d.get("closeTime") or "9999"))
    return draws, errors


# ---------------------------------------------------------------------------
# Lagform via ESPN:s öppna data-API (ingen nyckel krävs)
# ---------------------------------------------------------------------------

def _get_json(url: str) -> Any:
    """Enkel GET som returnerar JSON eller kastar FetchError."""
    request = urllib.request.Request(
        url, headers={"Accept": "application/json", "User-Agent": "Mozilla/5.0 (Tipset-optimeraren)"}
    )
    try:
        with urllib.request.urlopen(request, timeout=API_TIMEOUT_S) as response:
            return json.load(response)
    except urllib.error.HTTPError as exc:
        raise FetchError(f"HTTP {exc.code} från {urllib.parse.urlparse(url).netloc}.") from exc
    except (urllib.error.URLError, TimeoutError) as exc:
        raise FetchError(f"Kunde inte nå {urllib.parse.urlparse(url).netloc}: {exc}") from exc
    except json.JSONDecodeError as exc:
        raise FetchError("Svaret var inte giltig JSON.") from exc


def _normalize_name(name: str) -> str:
    """'Bayern München' -> 'bayern munchen' (gemener, utan accenter och skiljetecken)."""
    ascii_name = unicodedata.normalize("NFKD", name).encode("ascii", "ignore").decode()
    return re.sub(r"\s+", " ", re.sub(r"[^A-Za-z0-9 ]", " ", ascii_name)).strip().lower()


def name_similarity(query: str, candidate: str) -> float:
    """
    Hur väl ett kupongnamn matchar ett ESPN-namn (0–1).
    Klarar förkortningar som 'Manchester U' -> 'Manchester United' och
    'Inter' -> 'Internazionale' genom att jämföra ordens början.
    """
    q, c = _normalize_name(query), _normalize_name(candidate)
    if not q or not c:
        return 0.0
    if q == c:
        return 1.0
    score = SequenceMatcher(None, q, c).ratio()
    q_tokens, c_tokens = q.split(), c.split()
    if all(any(ct.startswith(qt) for ct in c_tokens) for qt in q_tokens):
        score = max(score, 0.92 if len(q_tokens) == len(c_tokens) else 0.86)
    # Initialförkortningar: 'PSG' -> 'Paris Saint Germain', 'Paris SG' -> 'Paris Saint Germain'.
    initials = {
        "".join(t[0] for t in c_tokens[i:j])
        for i in range(len(c_tokens)) for j in range(i + 2, len(c_tokens) + 1)
    }
    if len(q_tokens) <= len(c_tokens) and all(
        any(ct.startswith(qt) for ct in c_tokens) or (len(qt) >= 2 and qt in initials) for qt in q_tokens
    ):
        score = max(score, 0.86)
    return score


@st.cache_data(ttl=TEAM_INDEX_TTL_S, show_spinner=False)
def espn_team_index() -> list[dict[str, Any]]:
    """Alla lag i ESPN_LEAGUES (hämtas en gång per dygn). Ligor som inte svarar hoppas över."""
    index: list[dict[str, Any]] = []
    for slug, league_name in ESPN_LEAGUES.items():
        try:
            payload = _get_json(f"{ESPN_BASE}/{slug}/teams")
            teams = payload["sports"][0]["leagues"][0]["teams"]
        except (FetchError, KeyError, IndexError, TypeError):
            continue
        for wrapper in teams:
            team = wrapper.get("team") or {}
            names = {
                str(team.get(k)) for k in ("displayName", "shortDisplayName", "name", "location", "nickname")
                if team.get(k)
            }
            logos = team.get("logos") or []
            index.append(
                {
                    "id": str(team.get("id")),
                    "league": slug,
                    "league_name": league_name,
                    "display": team.get("displayName", "?"),
                    "names": sorted(names),
                    "logo": logos[0].get("href") if logos else None,
                }
            )
    if not index:
        raise FetchError("Kunde inte hämta några lag från ESPN.")
    return index


def find_espn_team(name: str, index: list[dict[str, Any]]) -> dict[str, Any] | None:
    """Bästa namnträff i lagindexet, eller None om ingen är tillräckligt lik."""
    best, best_score = None, 0.0
    for team in index:
        score = max(name_similarity(name, n) for n in team["names"])
        if score > best_score:
            best, best_score = team, score
    return best if best_score >= NAME_MATCH_THRESHOLD else None


def _completed_events(league: str, team_id: str, season: int | None = None) -> tuple[list[dict[str, Any]], int | None]:
    """Färdigspelade matcher ur lagets spelschema, samt säsongsår."""
    url = f"{ESPN_BASE}/{league}/teams/{team_id}/schedule"
    if season is not None:
        url += f"?season={season}"
    payload = _get_json(url)
    events = [
        e for e in payload.get("events") or []
        if ((e.get("competitions") or [{}])[0].get("status") or {}).get("type", {}).get("completed")
    ]
    year = (payload.get("season") or {}).get("year")
    return events, int(year) if isinstance(year, (int, float, str)) and str(year).isdigit() else None


def _score_value(competitor: dict[str, Any]) -> int | None:
    """ESPN-mål kan vara ett objekt ({'value': 2.0}) eller en sträng ('2')."""
    score = competitor.get("score")
    if isinstance(score, dict):
        score = score.get("value", score.get("displayValue"))
    try:
        return int(float(score))
    except (TypeError, ValueError):
        return None


def summarize_form(team: dict[str, Any], events: list[dict[str, Any]]) -> dict[str, Any]:
    """
    Sammanfattar lagets senaste FORM_MATCHES matcher.
    Resultat: V = vinst, O = oavgjort, F = förlust. Listan är äldst -> senast.
    """
    results: list[dict[str, Any]] = []
    for event in events:
        competitors = (event.get("competitions") or [{}])[0].get("competitors") or []
        me = next((c for c in competitors if str((c.get("team") or {}).get("id")) == team["id"]), None)
        other = next((c for c in competitors if c is not me), None)
        if not me or not other:
            continue
        gf, ga = _score_value(me), _score_value(other)
        if gf is None or ga is None:
            continue
        results.append(
            {
                "date": str(event.get("date", ""))[:10],
                "venue": "H" if me.get("homeAway") == "home" else "B",
                "opponent": (other.get("team") or {}).get("displayName", "?"),
                "gf": gf,
                "ga": ga,
                "result": "V" if gf > ga else ("O" if gf == ga else "F"),
            }
        )
    results = sorted(results, key=lambda r: r["date"])[-FORM_MATCHES:]
    return {
        "name": team["display"],
        "league_name": team["league_name"],
        "logo": team["logo"],
        "results": results,
        "points": sum(3 if r["result"] == "V" else 1 if r["result"] == "O" else 0 for r in results),
        "gf": sum(r["gf"] for r in results),
        "ga": sum(r["ga"] for r in results),
    }


@st.cache_data(ttl=FORM_CACHE_TTL_S, show_spinner=False)
def fetch_team_form(name: str) -> dict[str, Any]:
    """
    Slår upp laget i ESPN:s lagindex och hämtar dess senaste ligamatcher.
    Har säsongen färre än FORM_MATCHES spelade matcher (t.ex. precis efter
    säsongsstart) fylls det på med förra säsongen.
    """
    team = find_espn_team(name, espn_team_index())
    if team is None:
        raise FetchError(f"Hittade inget lag som liknar \"{name}\" i ligorna som stöds.")
    events, season = _completed_events(team["league"], team["id"])
    if len(events) < FORM_MATCHES and season:
        try:
            older, _ = _completed_events(team["league"], team["id"], season - 1)
            events = older + events
        except FetchError:
            pass
    return summarize_form(team, events)


def form_badges_html(results: list[dict[str, Any]]) -> str:
    """Färgade V/O/F-brickor med matchdetaljer som tooltip."""
    if not results:
        return "<span style='opacity:.6'>Inga spelade matcher hittades</span>"
    badges = []
    for r in results:
        tip = html.escape(f"{r['date']} ({r['venue']}) mot {r['opponent']}: {r['gf']}–{r['ga']}", quote=True)
        badges.append(
            f"<span title='{tip}' style='display:inline-block;width:24px;height:24px;"
            f"line-height:24px;margin-right:4px;border-radius:5px;text-align:center;"
            f"font-weight:700;color:white;background:{FORM_COLORS[r['result']]}'>{r['result']}</span>"
        )
    return "".join(badges)


# ---------------------------------------------------------------------------
# AI-analys via Google Gemini
# ---------------------------------------------------------------------------

def _secret_file_candidates() -> list[Path]:
    """Möjliga platser för secrets.toml: mappen med app.py, terminalens mapp, hemmappen."""
    paths = [
        Path(__file__).resolve().parent / ".streamlit" / "secrets.toml",
        Path.cwd() / ".streamlit" / "secrets.toml",
        Path.home() / ".streamlit" / "secrets.toml",
    ]
    return list(dict.fromkeys(paths))  # unika, i ordning


def get_secret(name: str) -> tuple[str, str]:
    """
    Läser en hemlighet. Returnerar (värde, källa) när den hittas, annars
    ("", förklaring till varför den saknas) så att felet kan visas i appen.
    Ordning: miljövariabel -> secrets.toml bredvid app.py -> i terminalens mapp -> i hemmappen.
    """
    if os.environ.get(name, "").strip():
        return os.environ[name].strip(), f"miljövariabeln {name}"

    if tomllib is None:  # Python < 3.11
        try:
            value = str(st.secrets.get(name, "")).strip()
            return (value, "secrets.toml") if value else ("", "ingen nyckel i secrets.toml")
        except Exception:
            return "", "ingen secrets.toml hittades"

    problems: list[str] = []
    for path in _secret_file_candidates():
        if not path.exists():
            txt_variant = path.with_name("secrets.toml.txt")
            if txt_variant.exists():
                problems.append(f"{txt_variant} slutar på .txt – döp om den till secrets.toml")
            continue
        try:
            # utf-8-sig tål den BOM som Anteckningar ibland lägger till
            data = tomllib.loads(path.read_text(encoding="utf-8-sig"))
        except (OSError, UnicodeDecodeError, tomllib.TOMLDecodeError) as exc:
            problems.append(f"{path} kunde inte läsas ({exc}). Spara filen som UTF-8 med raden {name} = \"din-nyckel\"")
            continue
        value = str(data.get(name, "")).strip()
        if value:
            return value, str(path)
        found = ", ".join(data) or "inget"
        problems.append(f"{path} saknar {name} (hittade: {found})")

    try:  # på en server (t.ex. Streamlit Community Cloud) finns hemligheterna i st.secrets
        value = str(st.secrets.get(name, "")).strip()
        if value:
            return value, "serverns secrets"
    except Exception:
        pass
    if not problems:
        problems.append("ingen secrets.toml hittades. Letade i: " + "; ".join(map(str, _secret_file_candidates())))
    return "", " · ".join(problems)


def gemini_request(body: dict[str, Any], api_key: str, model: str, extra_hint: str = "") -> dict[str, Any]:
    """POST till Gemini generateContent. Returnerar hela JSON-svaret eller kastar FetchError."""
    request = urllib.request.Request(
        GEMINI_ENDPOINT.format(model=urllib.parse.quote(model)),
        data=json.dumps(body).encode("utf-8"),
        headers={"Content-Type": "application/json", "x-goog-api-key": api_key},
        method="POST",
    )
    try:
        with urllib.request.urlopen(request, timeout=GEMINI_TIMEOUT_S) as response:
            return json.load(response)
    except urllib.error.HTTPError as exc:
        try:
            detail = json.load(exc).get("error", {}).get("message", "")
        except Exception:
            detail = ""
        hints = {400: "Kontrollera nyckeln och modellnamnet.", 403: "Nyckeln saknar behörighet.",
                 404: "Modellen finns inte – välj en annan i sidomenyn.", 429: "Kvoten är slut – vänta en stund."}
        hint = extra_hint if extra_hint and exc.code in (400, 403, 429) else hints.get(exc.code, "")
        raise FetchError(f"Gemini svarade med HTTP {exc.code}. {hint} {detail}".strip()) from exc
    except (urllib.error.URLError, TimeoutError) as exc:
        raise FetchError(f"Kunde inte nå Gemini: {exc}") from exc
    except json.JSONDecodeError as exc:
        raise FetchError("Svaret från Gemini var inte giltig JSON.") from exc


def _candidate_text(candidate: dict[str, Any]) -> str:
    """Svarstexten ur ett Gemini-svar (utan 'tankar'). Kastar FetchError om den är tom."""
    if not candidate:
        raise FetchError("Gemini gav inget svar.")
    parts = (candidate.get("content") or {}).get("parts") or []
    text = "".join(p.get("text", "") for p in parts if not p.get("thought"))
    if not text.strip():
        raise FetchError(f"Gemini gav ett tomt svar (finishReason: {candidate.get('finishReason', '?')}).")
    return text.strip()


def call_gemini(prompt: str, api_key: str, model: str) -> str:
    """Skickar prompten till Gemini med analys-instruktionerna och returnerar svarstexten."""
    body = {
        "systemInstruction": {"parts": [{"text": GEMINI_SYSTEM_PROMPT}]},
        "contents": [{"role": "user", "parts": [{"text": prompt}]}],
        "generationConfig": {"temperature": 0.4},
    }
    payload = gemini_request(body, api_key, model)
    candidates = payload.get("candidates") or []
    if not candidates:
        reason = (payload.get("promptFeedback") or {}).get("blockReason", "okänd orsak")
        raise FetchError(f"Gemini gav inget svar ({reason}).")
    return _candidate_text(candidates[0])


def build_analysis_prompt(
    coupon: pd.DataFrame,
    probs: pd.DataFrame,
    selection: np.ndarray,
    system_name: str,
    row_price: int,
    budget: int,
    forms: dict[str, str],
    injuries: pd.DataFrame | None = None,
) -> str:
    """Beskriver systemet match för match som underlag till Gemini."""
    p_matrix = probs[["p1", "pX", "p2"]].to_numpy()
    rows, chance, covered = evaluate_selection(p_matrix, selection)
    lines = [
        f"System: {system_name}",
        f"Rader: {rows} · Kostnad: {rows * row_price} kr (radpris {row_price} kr) · Budget: {budget} kr",
        f"Beräknad chans till alla rätt: {chance:.2%} (antar oberoende matcher)",
        "",
        "Nr | Match | Odds 1/X/2 | Marginalfri sannolikhet 1/X/2 (%) | Svenska folket 1/X/2 (%) | "
        "Valda tecken | Täckt sannolikhet (%) | Form hemma / borta (senaste 5 ligamatcher, äldst→senast) | "
        "Skador/avstängningar hemma / borta",
    ]
    for i, row in coupon.reset_index(drop=True).iterrows():
        home, away = str(row["Hemmalag"]), str(row["Bortalag"])
        folk = "/".join("–" if pd.isna(row.get(c)) else f"{row[c]:.0f}" for c in FOLK_COLS)
        chosen = "".join(s for s, on in zip(SIGNS, selection[i]) if on)
        form = f"{forms.get(home, '?')} / {forms.get(away, '?')}" if forms else "ej hämtad"
        injury = "ej hämtat"
        if injuries is not None and i < len(injuries):
            inj_home, inj_away = (str(injuries.iloc[i][c] or "").strip() for c in INJURY_COLS)
            if inj_home or inj_away:
                injury = f"{inj_home or '?'} / {inj_away or '?'}"
        lines.append(
            f"{i + 1} | {home} – {away} | "
            + "/".join(f"{row[c]:.2f}" for c in ODDS_COLS) + " | "
            + "/".join(f"{p * 100:.0f}" for p in p_matrix[i]) + f" | {folk} | {chosen} | "
            + f"{covered[i] * 100:.0f} | {form} | {injury}"
        )
    lines += ["", "Ge en kort analys av systemet enligt instruktionerna."]
    return "\n".join(lines)


def render_ai_tab(
    coupon: pd.DataFrame,
    probs: pd.DataFrame,
    assigned: pd.DataFrame,
    own_selection: np.ndarray | None,
    coupon_key: str,
    row_price: int,
    budget: int,
    api_key: str,
    model: str,
    injuries: pd.DataFrame | None = None,
) -> None:
    """Flik där Gemini ger en kort, saklig analys av valt system."""
    if not api_key:
        st.info(
            "Lägg in din Gemini-nyckel från Google AI Studio i sidomenyn under *AI-analys*. "
            "Vill du slippa klistra in den varje gång: skapa filen `.streamlit/secrets.toml` "
            "bredvid `app.py` med raden `GEMINI_API_KEY = \"din-nyckel\"`."
        )
        return

    options = ["Mitt eget system", "Optimerat system"] if own_selection is not None else ["Optimerat system"]
    if own_selection is None:
        st.caption("Ditt eget system saknar tecken i någon match – analysen gäller därför det optimerade systemet.")
    choice = st.radio("Vad ska analyseras?", options, horizontal=True)
    selection = own_selection if choice == "Mitt eget system" else selection_from_assigned(assigned)

    # Ta med lagform om den redan är hämtad (cachad – kostar inga nya anrop).
    forms: dict[str, str] = {}
    if st.session_state.get(f"form_requested_{coupon_key}"):
        for team in pd.concat([coupon["Hemmalag"], coupon["Bortalag"]]).astype(str):
            try:
                forms[team] = "".join(r["result"] for r in fetch_team_form(team)["results"]) or "?"
            except FetchError:
                forms[team] = "?"
    else:
        st.caption("Tips: hämta form och skadeläge i fliken 📈 Form & skador först, så tar analysen hänsyn till dem.")

    prompt = build_analysis_prompt(coupon, probs, selection, choice, row_price, budget, forms, injuries)
    answer_key = "ai_answer_" + hashlib.sha256(f"{model}\n{prompt}".encode()).hexdigest()

    if st.button("🤖 Analysera med Gemini", type="primary"):
        with st.spinner(f"Frågar {model} …"):
            try:
                st.session_state[answer_key] = call_gemini(prompt, api_key, model)
            except FetchError as exc:
                st.error(str(exc))

    if answer_key in st.session_state:
        with st.container(border=True):
            st.markdown(st.session_state[answer_key])
        st.caption(
            f"Genererat av {model}. AI kan ha fel och ingen analys kan garantera vinst – "
            "spela bara för pengar du har råd att förlora."
        )
    with st.expander("Visa vad som skickas till Gemini"):
        st.code(prompt, language="text")


# ---------------------------------------------------------------------------
# Skadeläge: Fantasy Premier League (PL-lag) + Gemini med Google-sökning (övriga)
# ---------------------------------------------------------------------------

def _team_aliases(name: str) -> list[str]:
    """Kupongnamnet plus ESPN:s namn på laget (om det hittas), för säkrare namnmatchning."""
    names = [name]
    try:
        espn = find_espn_team(name, espn_team_index())
    except FetchError:
        espn = None
    if espn:
        names += espn["names"]
    return names


def _espn_league(name: str) -> str | None:
    """ESPN-ligan som laget hittades i (t.ex. 'eng.1'), annars None."""
    try:
        espn = find_espn_team(name, espn_team_index())
    except FetchError:
        return None
    return espn["league"] if espn else None


def sportsgambler_link(name: str) -> tuple[str, str]:
    """
    Länk till SportsGamblers skadelista för lagets liga, eller till översikten
    om laget/ligan inte hittas. Returnerar (url, länktext).
    """
    league = _espn_league(name)
    if league in SG_LEAGUES:
        return SG_BASE + SG_LEAGUES[league] + "/", f"Se {name} i {ESPN_LEAGUES[league]} på SportsGambler"
    return SG_BASE, "Se skadelistor för alla ligor på SportsGambler"


@st.cache_data(ttl=INJURY_CACHE_TTL_S, show_spinner=False)
def fetch_fpl_injuries() -> list[dict[str, Any]]:
    """
    Skador och avstängningar för alla Premier League-lag från Fantasy Premier Leagues
    öppna API. Returnerar [{'names': [...], 'players': ['Saka (skadad: Hamstring ...)', ...]}].
    """
    data = _get_json(FPL_URL)
    teams: dict[int, dict[str, Any]] = {}
    for t in data.get("teams") or []:
        names = [str(t.get("name", "")), str(t.get("short_name", ""))]
        names += FPL_ALIASES.get(str(t.get("name", "")), [])
        teams[t.get("id")] = {"names": [n for n in names if n], "players": []}
    for p in data.get("elements") or []:
        status = p.get("status")
        team = teams.get(p.get("team"))
        if status not in FPL_STATUS or team is None:
            continue
        label = FPL_STATUS[status]
        chance = p.get("chance_of_playing_next_round")
        if status == "d" and chance is not None:
            label += f" {chance} %"
        news = str(p.get("news") or "").strip()
        team["players"].append(f"{p.get('web_name', '?')} ({label}{': ' + news if news else ''})")
    if not teams:
        raise FetchError("Fantasy Premier League gav inga lag.")
    return list(teams.values())


def find_fpl_team(name: str, fpl_teams: list[dict[str, Any]]) -> dict[str, Any] | None:
    """Matchar ett kupongnamn mot ett PL-lag. Lag som ESPN placerar i annan liga hoppas över."""
    league = _espn_league(name)
    if league is not None and league != "eng.1":
        return None
    aliases = _team_aliases(name)
    best, best_score = None, 0.0
    for team in fpl_teams:
        score = max(
            max(name_similarity(a, n), name_similarity(n, a)) for a in aliases for n in team["names"]
        )
        if score > best_score:
            best, best_score = team, score
    return best if best_score >= FPL_MATCH_THRESHOLD else None


def search_injuries_with_gemini(
    matches: list[tuple[int, str, str]], api_key: str, model: str
) -> tuple[dict[int, tuple[str, str]], str, list[tuple[str, str]], str]:
    """
    Låter Gemini söka på Google efter skadeläget inför matcherna.
    Returnerar (tolkade rader {nr: (hemma, borta)}, råtext, källor [(titel, url)], sökförslag-HTML).
    """
    lines = "\n".join(f"{nr}. {home} – {away}" for nr, home, away in matches)
    prompt = (
        f"Dagens datum: {datetime.now():%Y-%m-%d}. Sök på webben efter aktuellt skadeläge och "
        "avstängningar inför lagens nästa match i följande fotbollsmatcher:\n"
        f"{lines}\n\n"
        "Svara ENDAST med en rad per match, i exakt detta format:\n"
        "NR | hemmalagets skadade/avstängda spelare | bortalagets skadade/avstängda spelare\n"
        "Skriv spelarnamn med kort status inom parentes, t.ex. 'Saka (skadad), Rice (avstängd)'. "
        "Skriv 'Inga kända' om du inte hittar något aktuellt. Ta bara med uppgifter som finns i "
        "sökresultaten – hitta aldrig på spelare. Ingen annan text."
    )
    body = {
        "contents": [{"role": "user", "parts": [{"text": prompt}]}],
        "tools": [{"google_search": {}}],
        "generationConfig": {"temperature": 0.2},
    }
    payload = gemini_request(
        body, api_key, model,
        extra_hint="Google-sökning via API:t ingår normalt inte i gratisnivån – aktivera betalning i "
                   "Google AI Studio, eller skriv in skadorna själv i tabellen.",
    )
    candidate = (payload.get("candidates") or [{}])[0]
    text = _candidate_text(candidate)

    parsed: dict[int, tuple[str, str]] = {}
    for raw in text.splitlines():
        m = re.match(r"^\W*(\d+)\W*\|\s*(.*?)\s*\|\s*(.*?)\s*$", raw.replace("*", ""))
        if m:
            parsed[int(m.group(1))] = (m.group(2).strip(), m.group(3).strip())

    meta = candidate.get("groundingMetadata") or {}
    sources: list[tuple[str, str]] = []
    for chunk in meta.get("groundingChunks") or []:
        web = chunk.get("web") or {}
        if web.get("uri") and (web.get("title"), web["uri"]) not in sources:
            sources.append((str(web.get("title") or web["uri"]), str(web["uri"])))
    suggestions = str((meta.get("searchEntryPoint") or {}).get("renderedContent") or "")
    return parsed, text, sources, suggestions


def fetch_injury_notes(
    coupon: pd.DataFrame, api_key: str, model: str
) -> tuple[pd.DataFrame, list[str], dict[str, Any]]:
    """
    Bygger tabellen med skadeläge per match.
    PL-lag fylls från Fantasy Premier League; övriga söks med Gemini (om nyckel finns).
    Returnerar (tabell, meddelanden, Gemini-info för visning av källor).
    """
    coupon = coupon.reset_index(drop=True)
    notes = pd.DataFrame(
        {
            "Nr": np.arange(1, len(coupon) + 1),
            "Match": coupon["Hemmalag"].astype(str) + " – " + coupon["Bortalag"].astype(str),
            INJURY_COLS[0]: "",
            INJURY_COLS[1]: "",
            "Källa": "",
            "SportsGambler": "",
        }
    )
    messages: list[str] = []
    gemini_info: dict[str, Any] = {}

    try:
        fpl_teams = fetch_fpl_injuries()
    except FetchError as exc:
        fpl_teams = []
        messages.append(f"Fantasy Premier League: {exc}")

    remaining: list[tuple[int, str, str]] = []
    for i, row in coupon.iterrows():
        home, away = str(row["Hemmalag"]), str(row["Bortalag"])
        fpl_home, fpl_away = find_fpl_team(home, fpl_teams), find_fpl_team(away, fpl_teams)
        if fpl_home and fpl_away:
            notes.at[i, INJURY_COLS[0]] = ", ".join(fpl_home["players"]) or "Inga kända"
            notes.at[i, INJURY_COLS[1]] = ", ".join(fpl_away["players"]) or "Inga kända"
            notes.at[i, "Källa"] = "Fantasy Premier League"
        else:
            remaining.append((i + 1, home, away))

    if remaining and api_key:
        try:
            parsed, raw, sources, suggestions = search_injuries_with_gemini(remaining, api_key, model)
            for nr, _, _ in remaining:
                if nr in parsed:
                    notes.at[nr - 1, INJURY_COLS[0]], notes.at[nr - 1, INJURY_COLS[1]] = parsed[nr]
                    notes.at[nr - 1, "Källa"] = "Google-sökning (Gemini)"
            if not parsed:
                messages.append("Gemini svarade men i oväntat format – se råsvaret nedan.")
            gemini_info = {"raw": raw, "sources": sources, "suggestions": suggestions}
        except FetchError as exc:
            messages.append(f"Gemini/Google-sökning: {exc}")
    elif remaining:
        messages.append(
            f"{len(remaining)} match(er) utanför Premier League saknar automatisk källa – lägg in "
            "Gemini-nyckeln i sidomenyn för Google-sökning, eller använd SportsGambler-länkarna."
        )

    # Där inget hittades: länka till SportsGambler (lagets liga, annars översikten).
    for i, row in coupon.iterrows():
        for col, team in ((INJURY_COLS[0], str(row["Hemmalag"])), (INJURY_COLS[1], str(row["Bortalag"]))):
            if not str(notes.at[i, col]).strip() and not notes.at[i, "SportsGambler"]:
                notes.at[i, "SportsGambler"] = sportsgambler_link(team)[0]
    return notes, messages, gemini_info


# ---------------------------------------------------------------------------
# Expekt-Tipset (PoolX) – inklistrad kupong + odds från Svenska Spel
# ---------------------------------------------------------------------------

Triple = tuple[float, float, float]


def parse_matches_with_odds(text: str) -> list[tuple[str, str, Triple | None, Triple | None]]:
    """
    Tolkar Expekt-matcher med fördelning och odds i formatet
        'Sevilla – Osasuna (53% - 28% - 19%) (1,83 - 3,50 - 4,60) Sepsi – U Craiova (15% - 23% - 62%) (Inga odds)'
    En parentes med %-tecken = PoolX-fördelningen (1 - X - 2), en parentes med tal utan % = odds.
    Båda är valfria och kan stå i valfri ordning; 'Inga odds' ger None. Matcherna kan stå
    på samma rad eller på olika rader. Returnerar [(hemma, borta, odds, fördelning)],
    eller [] om texten inte följer formatet.
    """
    pattern = re.compile(
        r"(?P<home>[^()\n]+?)\s+(?:-|–|—|vs\.?)\s+(?P<away>[^()\n]+?)\s*(?P<groups>(?:\([^)]*\)\s*){1,2})",
        re.IGNORECASE,
    )
    result: list[tuple[str, str, Triple | None, Triple | None]] = []
    for m in pattern.finditer(text):
        home = re.sub(r"^\s*\d{1,2}\s*[.):]\s*", "", m.group("home")).strip(" \t,;|·")
        away = m.group("away").strip(" \t,;|·")
        odds: Triple | None = None
        folk: Triple | None = None
        for group in re.findall(r"\(([^)]*)\)", m.group("groups")):
            numbers = [float(n.replace(",", ".")) for n in re.findall(r"\d+(?:[.,]\d+)?", group)]
            if len(numbers) != 3:
                continue  # t.ex. "Inga odds"
            if "%" in group:
                folk = tuple(numbers)  # type: ignore[assignment]
            elif all(n > 1.0 for n in numbers):
                odds = tuple(numbers)  # type: ignore[assignment]
        if home and away:
            result.append((home, away, odds, folk))
    return result


def parse_pasted_matches(text: str) -> list[tuple[str, str]]:
    """
    Tolkar matcher som klistrats in från Expekt.
    1) Rader med avdelare: 'Arsenal - Everton', '3. Arsenal – Everton 1,45', 'Arsenal vs Everton'.
    2) Annars: lagnamn på varannan rad (hemma, borta, hemma, borta …).
    Rader utan lagnamn (tider, odds, procent, '1', 'X', '2') hoppas över.
    """
    separator = re.compile(r"\s+(?:-|–|—|vs\.?|v\.?)\s+", re.IGNORECASE)

    def clean(part: str) -> str:
        part = re.sub(r"^\s*\d{1,2}\s*[.):]?\s+", "", part)          # radnummer
        part = re.sub(r"(\s+[\d.,%]+)+\s*$", "", part)                # odds/procent i slutet
        return part.strip(" \t|·")

    def is_team(part: str) -> bool:
        letters = re.sub(r"[^A-Za-zÀ-ÿ]", "", part)
        return len(letters) >= 2 and part.strip().upper() not in {"1X2", "X2", "1X", "12"}

    lines = [ln.strip() for ln in text.splitlines() if ln.strip()]
    pairs: list[tuple[str, str]] = []
    for line in lines:
        parts = separator.split(line, maxsplit=1)
        if len(parts) == 2:
            home, away = clean(parts[0]), clean(parts[1])
            if is_team(home) and is_team(away):
                pairs.append((home, away))
    if pairs:
        return pairs

    teams = [clean(ln) for ln in lines]
    # Hoppa över tider/datum ("lör 15:00", "1 nov") som annars kan tas för lagnamn.
    teams = [
        t for t in teams
        if is_team(t)
        and not re.search(r"\d{1,2}[:.]\d{2}", t)
        and not re.fullmatch(r"(?i)(mån|tis|ons|tor|fre|lör|sön|idag|imorgon)\w*\.?(\s+\d.*)?", t)
    ]
    return [(teams[i], teams[i + 1]) for i in range(0, len(teams) - 1, 2)]


def svenska_spel_odds_lookup(draws: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """Alla matcher med odds ur Svenska Spels öppna omgångar: [{'home_names','away_names','odds','source'}]."""
    events: list[dict[str, Any]] = []
    for draw in draws:
        coupon, _ = draw_to_coupon(draw)
        for _, row in coupon.iterrows():
            odds = tuple(float(row[c]) for c in ODDS_COLS)
            if any(np.isnan(o) for o in odds):
                continue
            events.append(
                {"home_names": [str(row["Hemmalag"])], "away_names": [str(row["Bortalag"])],
                 "odds": odds, "source": "Svenska Spel"}
            )
    return events


def to_decimal_odds(value: Any) -> float:
    """
    Omvandlar ESPN-odds till decimalodds. Klarar amerikanska (+275, -150, 'EVEN'),
    bråk ('11/4') och decimal ('3.75'). Returnerar NaN om värdet inte går att tolka.
    """
    if value is None or isinstance(value, bool):
        return float("nan")
    text = str(value).strip().upper().replace(",", ".")
    if text in {"EVEN", "EV", "PK"}:
        return 2.0
    try:
        if "/" in text:
            num, den = text.split("/", 1)
            return 1.0 + float(num) / float(den)
        number = float(text.replace("+", ""))
    except ValueError:
        return float("nan")
    if not text.startswith(("+", "-")) and 1.0 < number < 50.0:
        return number                              # redan decimalodds
    if number >= 100:
        return 1.0 + number / 100.0                # amerikanska, plus
    if number <= -100:
        return 1.0 + 100.0 / abs(number)           # amerikanska, minus
    return float("nan")


def _plausible(odds: tuple[float, float, float]) -> bool:
    """Rimliga 1X2-odds: alla > 1 och spelbolagets återbetalning inom normalt intervall."""
    if any(np.isnan(o) or o <= 1.0 for o in odds):
        return False
    return 0.95 <= sum(1.0 / o for o in odds) <= 1.30


def espn_competition_odds(competition: dict[str, Any]) -> tuple[tuple[float, float, float], str] | None:
    """1X2-odds ur en ESPN-match, oavsett vilket av ESPN:s två oddsformat som används."""
    for block in competition.get("odds") or []:
        provider = str((block.get("provider") or {}).get("name") or "ESPN")
        # Format A: homeTeamOdds / drawOdds / awayTeamOdds med moneyLine
        odds = tuple(
            to_decimal_odds((block.get(key) or {}).get("moneyLine"))
            for key in ("homeTeamOdds", "drawOdds", "awayTeamOdds")
        )
        if _plausible(odds):  # type: ignore[arg-type]
            return odds, provider  # type: ignore[return-value]
        # Format B: moneyline.{home,draw,away}.{close,current,open}.odds
        moneyline = block.get("moneyline") or {}

        def _side(side: str) -> float:
            side_block = moneyline.get(side) or {}
            for stage in ("close", "current", "open"):
                value = (side_block.get(stage) or {}).get("odds")
                if value is not None:
                    return to_decimal_odds(value)
            return float("nan")

        odds = (_side("home"), _side("draw"), _side("away"))
        if _plausible(odds):
            return odds, provider
    return None


@st.cache_data(ttl=ESPN_ODDS_CACHE_TTL_S, show_spinner=False)
def fetch_espn_odds_events() -> tuple[list[dict[str, Any]], int]:
    """
    Kommande matcher med 1X2-odds från ESPN i alla ligor i ESPN_LEAGUES.
    Returnerar (matcher, antal ligor som inte svarade).
    """
    start = datetime.now()
    dates = f"{start:%Y%m%d}-{start + timedelta(days=ESPN_ODDS_DAYS):%Y%m%d}"
    events: list[dict[str, Any]] = []
    failed = 0
    for slug, league_name in ESPN_LEAGUES.items():
        try:
            payload = _get_json(f"{ESPN_BASE}/{slug}/scoreboard?dates={dates}&limit=300")
        except FetchError:
            failed += 1
            continue
        for event in payload.get("events") or []:
            competition = (event.get("competitions") or [{}])[0]
            if ((competition.get("status") or {}).get("type") or {}).get("completed"):
                continue
            found = espn_competition_odds(competition)
            if not found:
                continue
            sides: dict[str, list[str]] = {}
            for competitor in competition.get("competitors") or []:
                team = competitor.get("team") or {}
                sides[competitor.get("homeAway", "")] = [
                    str(team[k]) for k in ("displayName", "shortDisplayName", "name", "location") if team.get(k)
                ]
            if sides.get("home") and sides.get("away"):
                odds, provider = found
                events.append(
                    {"home_names": sides["home"], "away_names": sides["away"], "odds": odds,
                     "source": f"ESPN ({provider}, {league_name})"}
                )
    return events, failed


def _pair_score(a: str, b: str) -> float:
    """Symmetrisk namnlikhet."""
    return max(name_similarity(a, b), name_similarity(b, a))


def match_odds(home: str, away: str, events: list[dict[str, Any]]) -> dict[str, Any] | None:
    """Hittar samma match bland oddskällans matcher (båda lagen måste likna)."""
    best, best_score = None, 0.0
    for ev in events:
        score = min(
            max(_pair_score(home, n) for n in ev["home_names"]),
            max(_pair_score(away, n) for n in ev["away_names"]),
        )
        if score > best_score:
            best, best_score = ev, score
    return best if best_score >= NAME_MATCH_THRESHOLD else None


def build_expekt_coupon(
    pairs: list[tuple[str, str]],
    *sources: list[dict[str, Any]],
    manual_odds: list[tuple[float, float, float] | None] | None = None,
    manual_folk: list[tuple[float, float, float] | None] | None = None,
) -> tuple[pd.DataFrame, list[int], list[str]]:
    """
    Kupong av inklistrade matcher. Egna inskrivna odds har företräde; därefter provas
    oddskällorna i ordning (Svenska Spel först, sedan ESPN).
    Returnerar (kupong, nr som saknar odds, källa per match).
    """
    rows: list[tuple[Any, ...]] = []
    missing: list[int] = []
    origins: list[str] = []
    for i, (home, away) in enumerate(pairs, start=1):
        own = manual_odds[i - 1] if manual_odds and i - 1 < len(manual_odds) else None
        hit = (
            {"odds": own, "source": "Egna odds"} if own
            else next((h for events in sources if events for h in [match_odds(home, away, events)] if h), None)
        )
        odds = hit["odds"] if hit else (float("nan"),) * 3
        if hit is None:
            missing.append(i)
        origins.append(hit["source"] if hit else "")
        folk = manual_folk[i - 1] if manual_folk and i - 1 < len(manual_folk) else None
        rows.append((home, away, *odds, *(folk or (float("nan"),) * 3)))
    return pd.DataFrame(rows, columns=TEAM_COLS + ODDS_COLS + FOLK_COLS), missing, origins


# ---------------------------------------------------------------------------
# V85 (trav) – data från ATG
# ---------------------------------------------------------------------------
# V85 ersatte V75 i oktober 2025 (8 avdelningar, 50 öre/rad, max 5 000 rader/kupong).
# ATG:s regler förbjuder egna statistiskt genererade system på V85, därför finns
# ingen automatisk optimerare här – användaren väljer hästarna själv och appen
# räknar rader, kostnad och chans.

def _atg_get(path: str) -> Any:
    """GET mot ATG:s racinginfo-API."""
    return _get_json(f"{ATG_BASE}/{path}")


@st.cache_data(ttl=ATG_LIST_TTL_S, show_spinner=False)
def fetch_v85_games() -> list[dict[str, str]]:
    """Kommande V85-omgångar: [{'id', 'label'}]. Provar products-listan, annars kalendern."""
    found: dict[str, dict[str, str]] = {}

    def _add(entry: dict[str, Any]) -> None:
        game_id = str(entry.get("id") or "")
        if not game_id.upper().startswith("V85"):
            return
        start = str(entry.get("startTime") or entry.get("scheduledStartTime") or "")
        tracks = entry.get("tracks") or []
        track_names = ", ".join(str(t.get("name")) for t in tracks if isinstance(t, dict) and t.get("name"))
        date_txt = start[:16].replace("T", " ") if start else game_id.split("_")[1] if "_" in game_id else ""
        found[game_id] = {"id": game_id, "label": f"V85 {date_txt}" + (f" · {track_names}" if track_names else "")}

    try:
        payload = _atg_get(f"products/{V85_TYPE}")
        for key in ("upcoming", "upcomingGames", "games", "current"):
            for entry in payload.get(key) or []:
                if isinstance(entry, dict):
                    _add(entry)
    except FetchError:
        pass

    if not found:  # reserv: dagskalendern en vecka framåt
        for offset in range(8):
            day = (datetime.now() + timedelta(days=offset)).strftime("%Y-%m-%d")
            try:
                payload = _atg_get(f"calendar/day/{day}")
            except FetchError:
                continue
            for entry in (payload.get("games") or {}).get(V85_TYPE) or []:
                if isinstance(entry, dict):
                    _add(entry)
    if not found:
        raise FetchError("Hittade ingen kommande V85-omgång hos ATG.")
    return sorted(found.values(), key=lambda g: g["id"])


@st.cache_data(ttl=ATG_GAME_TTL_S, show_spinner=False)
def fetch_v85_game(game_id: str) -> dict[str, Any]:
    """Hela V85-omgången (lopp, hästar, V85-%, odds) från ATG."""
    payload = _atg_get(f"games/{urllib.parse.quote(game_id)}")
    if not isinstance(payload, dict) or not payload.get("races"):
        raise FetchError("ATG:s svar innehöll inga lopp.")
    return payload


def _pool_value(pools: dict[str, Any], name: str, field: str) -> float:
    """Värde ur en pool, oavsett skiftläge på poolnamnet ('V85'/'v85')."""
    for key, pool in (pools or {}).items():
        if str(key).lower() == name.lower() and isinstance(pool, dict):
            value = pool.get(field)
            if isinstance(value, (int, float)) and not isinstance(value, bool):
                return float(value)
    return float("nan")


def _person_name(person: Any) -> str:
    if not isinstance(person, dict):
        return ""
    full = " ".join(str(person.get(k) or "") for k in ("firstName", "lastName")).strip()
    return full or str(person.get("name") or person.get("shortName") or "")


def parse_v85_race(race: dict[str, Any], game_type: str = V85_TYPE) -> tuple[dict[str, str], pd.DataFrame]:
    """
    Ett lopp -> (loppinfo, hästtabell). Tabellen har kolumnerna
    Nr, Häst, Kusk, V85 %, Odds, Struken, p_streck, p_odds.
    V85-% normaliseras till 100 % och oddsen tolkas oavsett om ATG lagrar dem ×100.
    """
    info = {
        "name": str(race.get("name") or ""),
        "track": str((race.get("track") or {}).get("name") or ""),
        "start": str(race.get("startTime") or race.get("scheduledStartTime") or "")[11:16],
        "distance": str(race.get("distance") or ""),
        "method": {"auto": "autostart", "volte": "voltstart"}.get(str(race.get("startMethod") or ""), str(race.get("startMethod") or "")),
    }
    rows = []
    for start in race.get("starts") or []:
        if not isinstance(start, dict):
            continue
        horse = start.get("horse") or {}
        pools = start.get("pools") or {}
        rows.append(
            {
                "Nr": int(start.get("number") or 0),
                "Häst": str(horse.get("name") or "?"),
                "Kusk": _person_name(start.get("driver")),
                "streck_raw": _pool_value(pools, game_type, "betDistribution"),
                "odds_raw": _pool_value(pools, "vinnare", "odds"),
                "Struken": bool(start.get("scratched") or horse.get("scratched")),
            }
        )
    df = pd.DataFrame(rows, columns=["Nr", "Häst", "Kusk", "streck_raw", "odds_raw", "Struken"])
    active = ~df["Struken"]

    streck = df["streck_raw"].where(active)
    total = streck.sum(skipna=True)
    df["V85 %"] = streck / total * 100 if total > 0 else np.nan

    odds = df["odds_raw"].where(active & (df["odds_raw"] > 0))
    if odds.notna().any() and (odds.dropna() >= 100).all():
        odds = odds / 100  # ATG lagrar ofta odds ×100 (345 = 3,45)
    df["Odds"] = odds

    df["p_streck"] = (df["V85 %"] / 100).fillna(0.0)
    if odds.notna().sum() == active.sum() and active.any():
        inv = (1 / odds).fillna(0.0)
        df["p_odds"] = inv / inv.sum()
    else:
        df["p_odds"] = np.nan
    return info, df.drop(columns=["streck_raw", "odds_raw"]).sort_values("Nr").reset_index(drop=True)


def v85_probabilities(df: pd.DataFrame, model: str) -> tuple[np.ndarray, str]:
    """Sannolikhet per häst enligt vald modell, med reserv om data saknas. Returnerar (p, använd modell)."""
    active = ~df["Struken"].to_numpy()
    if model == "odds" and df["p_odds"].notna().all():
        return df["p_odds"].to_numpy(dtype=float), "odds"
    if df["p_streck"].sum() > 0:
        return df["p_streck"].to_numpy(dtype=float), "V85 %"
    equal = active / max(active.sum(), 1)
    return equal.astype(float), "lika"


def evaluate_v85(selections: list[np.ndarray], probabilities: list[np.ndarray]) -> tuple[int, float, list[float]]:
    """Rader = produkten av valda hästar per avdelning; chans = produkten av täckt sannolikhet."""
    counts = [int(sel.sum()) for sel in selections]
    covered = [float((p * sel).sum()) for sel, p in zip(selections, probabilities)]
    rows = int(np.prod(counts)) if counts else 0
    return rows, float(np.prod(covered)) if covered else 0.0, covered


def render_v85_tab() -> None:
    """Flik för V85: hämta omgång, välj hästar per avdelning, se rader, kostnad och chans."""
    st.subheader("🐎 V85")
    st.info(
        "**Bygg ditt eget V85-system.** ATG:s spelregler förbjuder att spela egna *statistiskt "
        "genererade* system på V85. Därför räknar den här fliken bara på hästarna **du** väljer – "
        "rader, kostnad och chans. Den föreslår inga system automatiskt."
    )

    c1, c2, c3 = st.columns([2, 3, 3])
    if c1.button("🔄 Hämta V85-omgångar", type="primary", use_container_width=True):
        fetch_v85_games.clear()
        fetch_v85_game.clear()
        st.session_state["v85_requested"] = True
    if not st.session_state.get("v85_requested"):
        st.caption("Tryck på knappen för att hämta veckans V85 från ATG.")
        return

    try:
        with st.spinner("Hämtar V85 från ATG …"):
            games = fetch_v85_games()
    except FetchError as exc:
        st.error(f"Kunde inte hämta V85: {exc}")
        return
    labels = {g["id"]: g["label"] for g in games}
    game_id = c2.selectbox("Omgång", list(labels), format_func=lambda gid: labels[gid])
    stake_label = c3.selectbox("Insats per rad", list(V85_STAKES), help="Ordinarie radpris är 50 öre. Reducerad insats ger lägre utdelning.")
    row_price = V85_STAKES[stake_label]

    try:
        with st.spinner("Hämtar lopp och hästar …"):
            game = fetch_v85_game(game_id)
    except FetchError as exc:
        st.error(f"Kunde inte hämta omgången: {exc}")
        return

    races = [r for r in game.get("races") or [] if isinstance(r, dict)]
    game_type = str(game.get("type") or V85_TYPE)
    parsed = [parse_v85_race(r, game_type) for r in races]

    m1, m2 = st.columns([3, 2])
    model_label = m1.radio(
        "Sannolikhet per häst baseras på", ["Vinnarodds", "V85-procent (streck)"], horizontal=True,
        help="Vinnarodds speglar spelarnas pengar i vinnarspelet; V85-% visar hur V85-spelarna fördelar sina rader.",
    )
    model = "odds" if model_label == "Vinnarodds" else "streck"
    version_key = f"v85_version_{game_id}"
    if m2.button("🧹 Rensa alla val", use_container_width=True):
        st.session_state[version_key] = st.session_state.get(version_key, 0) + 1
    version = st.session_state.get(version_key, 0)

    summary_area = st.container()  # fylls efter valen nedan
    tabs = st.tabs([f"Avd {i}" for i in range(1, len(parsed) + 1)])
    selections: list[np.ndarray] = []
    probabilities: list[np.ndarray] = []
    used_models: set[str] = set()
    scratched_picked: list[str] = []

    for avd, (tab, (info, df)) in enumerate(zip(tabs, parsed), start=1):
        p, used = v85_probabilities(df, model)
        used_models.add(used)
        with tab:
            details = " · ".join(x for x in (info["track"], info["start"], f"{info['distance']} m" if info["distance"] else "", info["method"]) if x)
            st.markdown(f"**{info['name'] or f'Avdelning {avd}'}**  \n<small>{html.escape(details)}</small>", unsafe_allow_html=True)
            editor_df = pd.DataFrame(
                {
                    "Välj": False,
                    "Nr": df["Nr"],
                    "Häst": df["Häst"] + np.where(df["Struken"], " (struken)", ""),
                    "Kusk": df["Kusk"],
                    "V85 %": df["V85 %"],
                    "Odds": df["Odds"],
                    "Chans %": p * 100,
                }
            )
            edited = st.data_editor(
                editor_df,
                key=f"v85_editor_{game_id}_{avd}_{version}",
                hide_index=True,
                use_container_width=True,
                num_rows="fixed",
                disabled=["Nr", "Häst", "Kusk", "V85 %", "Odds", "Chans %"],
                column_config={
                    "Välj": st.column_config.CheckboxColumn("Välj", width="small"),
                    "Nr": st.column_config.NumberColumn("Nr", width="small"),
                    "V85 %": st.column_config.NumberColumn("V85 %", format="%.1f"),
                    "Odds": st.column_config.NumberColumn("Odds", format="%.2f"),
                    "Chans %": st.column_config.ProgressColumn("Chans %", min_value=0, max_value=100, format="%.1f"),
                },
            )
            sel = edited["Välj"].fillna(False).to_numpy(dtype=bool)
            if (sel & df["Struken"].to_numpy()).any():
                scratched_picked.append(f"avd {avd}")
            sel = sel & ~df["Struken"].to_numpy()
        selections.append(sel)
        probabilities.append(p)

    # --- Sammanfattning ------------------------------------------------------
    with summary_area:
        counts = [int(s.sum()) for s in selections]
        empty = [str(i) for i, c in enumerate(counts, start=1) if c == 0]
        if empty:
            st.warning("Välj minst en häst i avdelning " + ", ".join(empty) + ".")
        rows, chance, covered = evaluate_v85(selections, probabilities)
        cost = rows * row_price
        s1, s2, s3, s4 = st.columns(4)
        s1.metric("Rader", f"{rows:,}".replace(",", " "), " · ".join(map(str, counts)), delta_color="off")
        s2.metric("Kostnad", f"{cost:,.2f} kr".replace(",", " ").replace(".", ","))
        s3.metric("Chans till 8 rätt", f"{chance:.2%}" if not empty else "–")
        s4.metric("Motsvarar", f"1 på {1 / chance:,.0f}".replace(",", " ") if chance > 0 and not empty else "–")
        if rows > V85_MAX_ROWS:
            st.error(f"Systemet har {rows} rader – ATG tillåter högst {V85_MAX_ROWS} rader per kupong.")
        if scratched_picked:
            st.caption("Strukna hästar räknas inte med (" + ", ".join(scratched_picked) + ").")
        if "lika" in used_models or (model == "odds" and "V85 %" in used_models):
            st.caption("⚠️ Vinnarodds saknas i vissa lopp – där används V85-% (eller lika chans om även den saknas).")
        if not empty:
            st.dataframe(
                pd.DataFrame(
                    {"Avd": range(1, len(counts) + 1), "Valda hästar": counts,
                     "Täckt chans": [c * 100 for c in covered]}
                ),
                hide_index=True, use_container_width=True,
                column_config={"Täckt chans": st.column_config.ProgressColumn("Täckt chans (%)", min_value=0, max_value=100, format="%.1f")},
            )
        st.caption(
            "Chansen räknas som produkten av täckt sannolikhet per avdelning och antar att loppen är "
            "oberoende. Data från ATG (odds och V85-% uppdateras fram till start)."
        )

    with st.expander("Felsökning: rådata från ATG"):
        if races:
            first = (races[0].get("starts") or [{}])[0]
            st.write("Nycklar i första starten:", sorted(first.keys()) if isinstance(first, dict) else first)
            st.json({k: first.get(k) for k in ("number", "horse", "driver", "pools", "scratched")} if isinstance(first, dict) else {})


# ---------------------------------------------------------------------------
# Datamodell
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class SystemConfig:
    """Ett M-systems struktur."""

    hel: int    # H – antal helgarderingar (3 tecken)
    halv: int   # h – antal halvgarderingar (2 tecken)
    spik: int   # S – antal spikar (1 tecken)
    rows: int   # R = 3^H * 2^h * 1^S

    @property
    def label(self) -> str:
        return f"{self.hel} Hel, {self.halv} Halv, {self.spik} Spikar"


# ---------------------------------------------------------------------------
# Kärnmatematik
# ---------------------------------------------------------------------------

def mock_coupon(n_matches: int) -> pd.DataFrame:
    """
    Returnerar en förifylld kupong med `n_matches` matcher.
    Folkets fördelning är påhittad (favoriter något överstreckade) – bara exempeldata.
    """
    df = pd.DataFrame(MOCK_MATCHES[:n_matches], columns=TEAM_COLS + ODDS_COLS)
    implied = 1.0 / df[ODDS_COLS].to_numpy(dtype=float)
    skewed = implied**1.4
    df[FOLK_COLS] = np.round(skewed / skewed.sum(axis=1, keepdims=True) * 100)
    return df


def validate_coupon(df: pd.DataFrame) -> list[str]:
    """Kontrollerar att alla odds är giltiga decimalodds (> 1.0). Returnerar felmeddelanden."""
    errors: list[str] = []
    odds = df[ODDS_COLS].apply(pd.to_numeric, errors="coerce")
    for i, row in odds.iterrows():
        bad = [c for c in ODDS_COLS if pd.isna(row[c]) or row[c] <= 1.0]
        if bad:
            errors.append(f"Match {i + 1}: ogiltiga odds i {', '.join(bad)} (måste vara > 1.00).")
    return errors


def compute_probabilities(df: pd.DataFrame) -> pd.DataFrame:
    """
    Beräknar marginalfria sannolikheter och klassificerar varje match.

        Margin = 1/odds_1 + 1/odds_X + 1/odds_2
        p_i    = (1/odds_i) / Margin

        best_sign         = tecknet med högst p  (max_prob)
        uncertainty_index = 1.0 - (p_bästa - p_näst_bästa)
    """
    odds = df[ODDS_COLS].to_numpy(dtype=float)           # (N, 3)
    implied = 1.0 / odds                                  # implicerade sannolikheter
    margin = implied.sum(axis=1, keepdims=True)           # spelbolagets återbetalningsfaktor
    probs = implied / margin                              # marginalfria sannolikheter

    sorted_probs = np.sort(probs, axis=1)[:, ::-1]        # fallande per match
    best_idx = probs.argmax(axis=1)

    out = df.copy()
    out["p1"], out["pX"], out["p2"] = probs[:, 0], probs[:, 1], probs[:, 2]
    out["margin"] = margin.ravel()
    out["best_sign"] = np.array(SIGNS)[best_idx]
    out["max_prob"] = sorted_probs[:, 0]
    out["uncertainty_index"] = 1.0 - (sorted_probs[:, 0] - sorted_probs[:, 1])
    return out


def find_optimal_system(n_matches: int, max_rows: int) -> SystemConfig:
    """
    Itererar över alla (H, h, S) med H + h + S = N och väljer den konfiguration
    som ger flest rader R = 3^H * 2^h utan att överstiga `max_rows`.

    Eftersom 2 och 3 är primtal ger varje (H, h) ett unikt R – det finns alltså
    aldrig två olika konfigurationer med samma radantal.
    """
    if max_rows < 1:
        raise ValueError("Budgeten räcker inte till en enda rad.")

    best = SystemConfig(hel=0, halv=0, spik=n_matches, rows=1)  # helspikat system
    for hel in range(n_matches + 1):
        for halv in range(n_matches - hel + 1):
            rows = 3**hel * 2**halv
            if rows > max_rows:
                break  # fler halvgarderingar ger bara ännu fler rader
            if rows > best.rows:
                best = SystemConfig(hel=hel, halv=halv, spik=n_matches - hel - halv, rows=rows)
    return best


def _half_cover_signs(p_row: np.ndarray) -> str:
    """De två mest sannolika tecknen i kupongordning (t.ex. '1X', 'X2', '12')."""
    top_two = sorted(np.argsort(p_row)[::-1][:2])
    return "".join(SIGNS[i] for i in top_two)


def assign_signs(prob_df: pd.DataFrame, config: SystemConfig) -> pd.DataFrame:
    """
    Fördelar spikar, helgarderingar och halvgarderingar.

    Steg A: Sortera alla matcher på max_prob (fallande) -> de S översta spikas med best_sign.
    Steg B: Sortera resterande på uncertainty_index (fallande) -> de H översta helgarderas.
    Steg C: Övriga h matcher halvgarderas med sina två mest sannolika tecken.
    """
    df = prob_df.copy()
    # mergesort = stabil sortering, så lika värden behåller kupongordningen
    spik_idx = df.sort_values("max_prob", ascending=False, kind="mergesort").index[: config.spik]
    rest = df.drop(index=spik_idx)
    hel_idx = rest.sort_values("uncertainty_index", ascending=False, kind="mergesort").index[: config.hel]
    halv_idx = rest.index.difference(hel_idx)

    probs = df[["p1", "pX", "p2"]].to_numpy()
    pos = {idx: k for k, idx in enumerate(df.index)}

    df["Typ"] = ""
    df["Valt Tecken"] = ""
    df["Täckt sannolikhet"] = 0.0

    for idx in spik_idx:
        df.at[idx, "Typ"] = TYPE_SPIK
        df.at[idx, "Valt Tecken"] = df.at[idx, "best_sign"]
        df.at[idx, "Täckt sannolikhet"] = df.at[idx, "max_prob"]

    for idx in hel_idx:
        df.at[idx, "Typ"] = TYPE_HEL
        df.at[idx, "Valt Tecken"] = "1X2"
        df.at[idx, "Täckt sannolikhet"] = 1.0

    for idx in halv_idx:
        p_row = probs[pos[idx]]
        df.at[idx, "Typ"] = TYPE_HALV
        df.at[idx, "Valt Tecken"] = _half_cover_signs(p_row)
        df.at[idx, "Täckt sannolikhet"] = float(np.sort(p_row)[-2:].sum())

    return df


def selection_from_assigned(assigned: pd.DataFrame) -> np.ndarray:
    """Omvandlar optimerarens 'Valt Tecken' (t.ex. '1X') till en bool-matris (N, 3)."""
    return np.array(
        [[sign in str(chosen) for sign in SIGNS] for chosen in assigned["Valt Tecken"]],
        dtype=bool,
    )


def evaluate_selection(p_matrix: np.ndarray, selection: np.ndarray) -> tuple[int, float, np.ndarray]:
    """
    Utvärderar ett egenbyggt system.

        Rader     = produkten av antal valda tecken per match
        Täckt p   = summan av sannolikheterna för valda tecken per match
        Vinstchans = produkten av täckt p (antar oberoende matcher)

    Returnerar (rader, vinstchans, täckt sannolikhet per match).
    """
    rows = int(np.prod(selection.sum(axis=1)))
    covered = (p_matrix * selection).sum(axis=1)
    return rows, float(np.prod(covered)), covered


def build_result_table(assigned: pd.DataFrame) -> pd.DataFrame:
    """Tar fram den presentationsklara kupongen i ursprunglig matchordning."""
    return pd.DataFrame(
        {
            "Nr": np.arange(1, len(assigned) + 1),
            "Match": assigned["Hemmalag"].astype(str) + " – " + assigned["Bortalag"].astype(str),
            "Valt Tecken": assigned["Valt Tecken"],
            "Typ (Spik/Halv/Hel)": assigned["Typ"],
            "Huvudfavoritens Sannolikhet (%)": assigned["max_prob"] * 100,
            "Osäkerhetsindex": assigned["uncertainty_index"],
        }
    )


def style_result(df: pd.DataFrame) -> "pd.io.formats.style.Styler":
    """Färgkodar typen av gardering och formaterar siffrorna."""
    colors = {
        TYPE_SPIK: "background-color: #1b5e20; color: white; font-weight: 600;",
        TYPE_HALV: "background-color: #f9a825; color: black; font-weight: 600;",
        TYPE_HEL: "background-color: #b71c1c; color: white; font-weight: 600;",
    }
    return (
        df.style
        .map(lambda v: colors.get(v, ""), subset=["Typ (Spik/Halv/Hel)"])
        .map(lambda _: "font-weight: 700; text-align: center;", subset=["Valt Tecken"])
        .format({"Huvudfavoritens Sannolikhet (%)": "{:.1f}", "Osäkerhetsindex": "{:.3f}"})
    )


# ---------------------------------------------------------------------------
# Användargränssnitt
# ---------------------------------------------------------------------------

def _odds_folk_text(odds: float, folk: float) -> str:
    """Kompakt cell: '1.85 · 45 %' (streck om data saknas)."""
    odds_txt = f"{odds:.2f}" if not np.isnan(odds) else "–"
    folk_txt = f"{folk:.0f} %" if not np.isnan(folk) else "–"
    return f"{odds_txt}  ·  {folk_txt}"


def render_manual_builder(
    coupon: pd.DataFrame,
    probs: pd.DataFrame,
    assigned: pd.DataFrame,
    match_labels: pd.Series,
    coupon_key: str,
    row_price: int,
    budget: int,
    opt_rows: int,
    opt_chance: float,
) -> np.ndarray | None:
    """
    Användaren kryssar själv 1/X/2 per match. Odds och Svenska folkets
    fördelning visas bredvid varje tecken, och rader, kostnad och vinstchans
    räknas om direkt – jämfört med det optimerade systemet.
    """
    st.caption(
        "Kryssa de tecken du tror på. Bredvid varje tecken står **odds · % av Svenska folket**. "
        "Allt räknas om direkt."
    )

    n = len(probs)
    p_matrix = probs[["p1", "pX", "p2"]].to_numpy()
    odds = coupon[ODDS_COLS].to_numpy(dtype=float)
    folk = coupon[FOLK_COLS].to_numpy(dtype=float) if set(FOLK_COLS) <= set(coupon) else np.full((n, 3), np.nan)
    base_key = f"manual_base_{coupon_key}"
    version_key = f"manual_version_{coupon_key}"

    # Startläge: kopia av det optimerade systemet (sparas per kupong).
    base: np.ndarray | None = st.session_state.get(base_key)
    if base is None or base.shape != (n, 3):
        base = selection_from_assigned(assigned)
        st.session_state[base_key] = base

    def _reset(new_base: np.ndarray) -> None:
        st.session_state[base_key] = new_base
        st.session_state[version_key] = st.session_state.get(version_key, 0) + 1

    b1, b2, b3, _ = st.columns([2, 2, 2, 2])
    if b1.button("📋 Kopiera optimerat system", use_container_width=True):
        _reset(selection_from_assigned(assigned))
    if b2.button("⭐ Endast favoriter", use_container_width=True):
        _reset(p_matrix == p_matrix.max(axis=1, keepdims=True))
    if b3.button("🧹 Rensa alla", use_container_width=True):
        _reset(np.zeros((n, 3), dtype=bool))
    base = st.session_state[base_key]

    info_cols = {s: f"{s}: odds · folket" for s in SIGNS}
    data: dict[str, Any] = {"Nr": np.arange(1, n + 1), "Match": match_labels.to_numpy()}
    for k, s in enumerate(SIGNS):
        data[s] = base[:, k]
        data[info_cols[s]] = [_odds_folk_text(odds[i, k], folk[i, k]) for i in range(n)]
    editor_df = pd.DataFrame(data)

    edited = st.data_editor(
        editor_df,
        key=f"manual_editor_{coupon_key}_{st.session_state.get(version_key, 0)}",
        num_rows="fixed",
        hide_index=True,
        use_container_width=True,
        disabled=["Nr", "Match", *info_cols.values()],
        column_config={
            "Nr": st.column_config.NumberColumn("Nr", width="small"),
            **{s: st.column_config.CheckboxColumn(s, width="small") for s in SIGNS},
            **{c: st.column_config.TextColumn(c, width="small") for c in info_cols.values()},
        },
    )

    selection = edited[list(SIGNS)].fillna(False).to_numpy(dtype=bool)
    empty = [i + 1 for i, row in enumerate(selection) if not row.any()]
    if empty:
        st.warning("Välj minst ett tecken i match " + ", ".join(map(str, empty)) + ".")
        return None

    rows, chance, covered = evaluate_selection(p_matrix, selection)
    cost = rows * row_price
    counts = selection.sum(axis=1)
    layout = f"{int((counts == 3).sum())} Hel, {int((counts == 2).sum())} Halv, {int((counts == 1).sum())} Spikar"
    # Andel av Svenska folkets rader som ditt system täcker (om fördelning finns).
    folk_cover = (folk / 100 * selection).sum(axis=1)
    folk_share = float(np.prod(folk_cover)) if not np.isnan(folk_cover).any() else None

    m1, m2, m3, m4 = st.columns(4)
    m1.metric("Rader", f"{rows:,}".replace(",", " "), layout, delta_color="off")
    m2.metric(
        "Kostnad", f"{cost:,} kr".replace(",", " "),
        f"{cost - budget:+,} kr mot budget".replace(",", " "), delta_color="inverse",
    )
    m3.metric(
        "Vinstchans (alla rätt)", f"{chance:.2%}",
        f"{(chance - opt_chance) * 100:+.2f} %-enheter mot optimerat",
    )
    m4.metric(
        "Motsvarar", f"1 på {1 / chance:,.0f}".replace(",", " ") if chance > 0 else "–",
        f"Folket täcks till {folk_share:.2%}" if folk_share is not None else None,
        delta_color="off",
    )

    if cost > budget:
        st.warning(f"Systemet kostar {cost - budget} kr mer än din budget på {budget} kr.")
    if rows == opt_rows and chance < opt_chance - 1e-12:
        st.info(
            "Samma antal rader som det optimerade systemet men lägre vinstchans – "
            "prova att flytta garderingar till de jämnare matcherna."
        )

    st.dataframe(
        pd.DataFrame(
            {
                "Nr": np.arange(1, n + 1),
                "Match": match_labels.to_numpy(),
                "Dina tecken": ["".join(s for s, on in zip(SIGNS, row) if on) for row in selection],
                "Täckt sannolikhet": covered * 100,
            }
        ),
        hide_index=True,
        use_container_width=True,
        column_config={
            "Täckt sannolikhet": st.column_config.ProgressColumn(
                "Täckt sannolikhet (%)", min_value=0, max_value=100, format="%.1f %%",
            )
        },
    )

    return selection

def render_form_tab(
    coupon: pd.DataFrame, coupon_key: str, gemini_key: str, gemini_model: str
) -> pd.DataFrame | None:
    """
    Flik med lagens form (ESPN) och skadeläge (Fantasy Premier League + Gemini/Google).
    Returnerar den (redigerbara) skadetabellen så att AI-analysen kan använda den.
    """
    form_key = f"form_requested_{coupon_key}"
    inj_base_key = f"injury_base_{coupon_key}"
    inj_version_key = f"injury_version_{coupon_key}"
    inj_msg_key = f"injury_messages_{coupon_key}"
    inj_gemini_key = f"injury_gemini_{coupon_key}"

    b1, b2, _ = st.columns([2, 2, 4])
    if b1.button("📈 Hämta lagform", type="primary", use_container_width=True):
        st.session_state[form_key] = True
    if b2.button("🩹 Hämta skadeläge", type="primary", use_container_width=True):
        with st.spinner("Hämtar skadeläge …"):
            notes, messages, gemini_info = fetch_injury_notes(coupon, gemini_key, gemini_model)
        st.session_state[inj_base_key] = notes
        st.session_state[inj_msg_key] = messages
        st.session_state[inj_gemini_key] = gemini_info
        st.session_state[inj_version_key] = st.session_state.get(inj_version_key, 0) + 1
    st.caption(
        f"**Form:** senaste {FORM_MATCHES} ligamatcherna per lag (ESPN), äldst → senast – håll musen "
        "över en bricka för att se matchen. **Skador:** Premier League-lag från Fantasy Premier League, "
        "övriga via Google-sökning i Gemini. Du kan alltid skriva in eller rätta skadorna själv."
    )

    cards_area = st.container()  # fylls efter skadetabellen, så korten visar redigerade värden

    # --- Skadetabell (redigerbar) -------------------------------------------
    notes: pd.DataFrame | None = st.session_state.get(inj_base_key)
    if notes is None or len(notes) != len(coupon):
        notes = pd.DataFrame(
            {
                "Nr": np.arange(1, len(coupon) + 1),
                "Match": (coupon["Hemmalag"].astype(str) + " – " + coupon["Bortalag"].astype(str)).to_numpy(),
                INJURY_COLS[0]: "",
                INJURY_COLS[1]: "",
                "Källa": "",
                "SportsGambler": "",
            }
        )
    st.markdown("##### 🩹 Skador & avstängningar")
    for msg in st.session_state.get(inj_msg_key, []):
        st.warning(msg)
    edited_notes = st.data_editor(
        notes,
        key=f"injury_editor_{coupon_key}_{st.session_state.get(inj_version_key, 0)}",
        num_rows="fixed",
        hide_index=True,
        use_container_width=True,
        disabled=["Nr", "Match", "Källa", "SportsGambler"],
        column_config={
            "Nr": st.column_config.NumberColumn("Nr", width="small"),
            **{c: st.column_config.TextColumn(c, width="large") for c in INJURY_COLS},
            "Källa": st.column_config.TextColumn("Källa", width="small"),
            "SportsGambler": st.column_config.LinkColumn(
                "Ej hittat?", display_text="Öppna SportsGambler", width="small",
                help="Visas där appen inte hittade skadeläget själv.",
            ),
        },
    )
    gemini_info: dict[str, Any] = st.session_state.get(inj_gemini_key) or {}
    if gemini_info:
        with st.expander("Källor för Google-sökningen"):
            for title, url in gemini_info.get("sources", []):
                st.markdown(f"- [{title}]({url})")
            if gemini_info.get("suggestions"):
                st.html(gemini_info["suggestions"])  # Googles sökförslag (krav vid Google-sökning)
            st.caption("Råsvar från Gemini:")
            st.code(gemini_info.get("raw", ""), language="text")
        st.caption("Skadeuppgifter från sökningar kan vara inaktuella eller felaktiga – dubbelkolla viktiga spelare.")

    # --- Matchkort med form + skador ----------------------------------------
    injuries_fetched = inj_base_key in st.session_state

    def _injury_html(text: str, align: str, team: str) -> str:
        text = str(text or "").strip()
        style = f"text-align:{align};margin-top:6px;font-size:0.85em"
        if text:
            return f"<div style='{style}'>🩹 {html.escape(text)}</div>"
        if not injuries_fetched:
            return ""
        url, label = sportsgambler_link(team)
        return (
            f"<div style='{style}'>🩹 <i>Hittade inga skadeuppgifter.</i> "
            f"<a href='{html.escape(url, quote=True)}' target='_blank' rel='noopener'>{html.escape(label)} ↗</a></div>"
        )

    def _team_block(container: Any, name: str, align: str, injuries: str) -> None:
        if not st.session_state.get(form_key):
            container.markdown(
                f"<div style='text-align:{align}'><b>{html.escape(name)}</b>{_injury_html(injuries, align, name)}</div>",
                unsafe_allow_html=True,
            )
            return
        try:
            form = fetch_team_form(name)
        except FetchError as exc:
            container.markdown(
                f"<div style='text-align:{align}'><b>{html.escape(name)}</b><br>"
                f"<small>⚠️ {html.escape(str(exc))}</small>{_injury_html(injuries, align, name)}</div>",
                unsafe_allow_html=True,
            )
            return
        record = f"{form['points']} p av {3 * len(form['results'])} · mål {form['gf']}–{form['ga']}"
        logo = (
            f"<img src='{html.escape(form['logo'], quote=True)}' height='22' "
            "style='vertical-align:middle;margin:0 6px'>" if form["logo"] else ""
        )
        matched = html.escape(f"{form['name']} · {form['league_name']}")
        container.markdown(
            f"<div style='text-align:{align}'>{logo}<b>{html.escape(name)}</b>"
            f"<div style='margin:6px 0'>{form_badges_html(form['results'])}</div>"
            f"<small style='opacity:.75'>{record}<br>{matched}</small>"
            f"{_injury_html(injuries, align, name)}</div>",
            unsafe_allow_html=True,
        )

    if not st.session_state.get(form_key) and not injuries_fetched:
        with cards_area.expander("Ligor som stöds för lagform"):
            st.write(", ".join(ESPN_LEAGUES.values()))
        return edited_notes

    with cards_area, st.spinner("Hämtar lagform från ESPN …"):
        for i, row in coupon.reset_index(drop=True).iterrows():
            with st.container(border=True):
                left, mid, right = st.columns([5, 1, 5])
                _team_block(left, str(row["Hemmalag"]), "left", edited_notes.iloc[i][INJURY_COLS[0]])
                mid.markdown(
                    f"<div style='text-align:center;padding-top:14px;opacity:.6'>{i + 1}<br>vs</div>",
                    unsafe_allow_html=True,
                )
                _team_block(right, str(row["Bortalag"]), "right", edited_notes.iloc[i][INJURY_COLS[1]])
        if st.session_state.get(form_key):
            st.caption(
                "Lagen matchas på namn. Under varje lag står vilket lag och vilken liga som hittades. "
                "Blev det fel lag: skriv ett tydligare namn i kupongtabellen (t.ex. 'Man Utd' → 'Manchester United')."
            )
    return edited_notes


def _truthy(value: str) -> bool:
    return str(value).strip().lower() in {"1", "true", "ja", "yes", "on"}


def render_access_control() -> bool:
    """
    Avgör om AI-funktionerna (Gemini) får användas i den här sessionen.
      * AI_DISABLED = true      -> AI är avstängt för alla (publik app utan AI).
      * ADMIN_PASSWORD satt      -> AI kräver master-inloggning.
      * inget av dem satt        -> lokalt läge: AI är öppet (som tidigare).
    """
    if _truthy(get_secret("AI_DISABLED")[0]):
        return False
    password = get_secret("ADMIN_PASSWORD")[0]
    if not password:
        st.sidebar.caption(
            "🔓 Lokalt läge – AI är öppet. Sätt `ADMIN_PASSWORD` i secrets.toml innan appen läggs på en server."
        )
        return True

    if st.session_state.get("is_admin"):
        st.sidebar.success("🔑 Inloggad som master")
        if st.sidebar.button("Logga ut"):
            st.session_state["is_admin"] = False
            st.rerun()
        return True

    with st.sidebar.expander("🔒 Master-inloggning"):
        with st.form("admin_login", clear_on_submit=True):
            attempt = st.text_input("Lösenord", type="password")
            submitted = st.form_submit_button("Logga in")
        if submitted:
            if hmac.compare_digest(attempt.encode("utf-8"), password.encode("utf-8")):
                st.session_state["is_admin"] = True
                st.session_state.pop("login_failures", None)
                st.rerun()
            failures = st.session_state.get("login_failures", 0) + 1
            st.session_state["login_failures"] = failures
            time.sleep(min(2**failures, 30))  # bromsar gissningsförsök
            st.error("Fel lösenord.")
    return False


def render_sidebar() -> tuple[int, int, int, list[str], str, str, bool]:
    """
    Returnerar (maxbudget, radpris, antal matcher i exempelkupong, valda produkter,
    Gemini-nyckel, Gemini-modell, om AI är tillåtet).
    """
    st.sidebar.header("⚙️ Fotboll – inställningar")
    budget = st.sidebar.slider("Maxbudget (kr)", min_value=10, max_value=1000, value=100, step=1)
    row_price = st.sidebar.selectbox(
        "Radpris (kr)", [1, 2, 5, 10], index=0,
        help="Insats per rad. Standard är 1 kr/rad.",
    )

    st.sidebar.subheader("Svenska Spel – hämtning (endast fotboll)")
    products = st.sidebar.multiselect(
        "Spelformer att hämta",
        options=list(API_PRODUCTS),
        default=list(API_PRODUCTS),
        format_func=lambda p: API_PRODUCTS[p],
        help="Endast fotbollsspel med 1X2. Topptipset inkluderar t.ex. Topptipset Europa och Extra.",
    )

    st.sidebar.subheader("Exempelkupong")
    mock_choice = st.sidebar.radio(
        "Antal matcher (används när ingen omgång är hämtad)",
        ["8 matcher", "13 matcher"],
    )
    mock_n = 8 if mock_choice.startswith("8") else 13

    st.sidebar.subheader("AI-analys (Gemini)")
    ai_allowed = render_access_control()
    gemini_key, gemini_model = "", GEMINI_MODELS[0]
    if ai_allowed:
        secret_value, secret_source = get_secret("GEMINI_API_KEY")
        gemini_key = st.sidebar.text_input(
            "Gemini-nyckel",
            value=secret_value,
            type="password",
            help="Nyckel från Google AI Studio. Kan sparas i .streamlit/secrets.toml som GEMINI_API_KEY.",
        ).strip()
        if secret_value:
            st.sidebar.caption(f"🔑 Hämtad från {secret_source}")
        else:
            st.sidebar.caption(f"⚠️ Nyckeln lästes inte in automatiskt: {secret_source}")
        gemini_model = st.sidebar.selectbox("Modell", GEMINI_MODELS, index=0)

    st.sidebar.caption(
        "Algoritmen maximerar sannolikheten att få alla rätt – "
        "den jagar aldrig utdelning och använder inga rensare."
    )
    return budget, int(row_price), mock_n, products, gemini_key, gemini_model, ai_allowed


def render_coupon_source(mock_n: int, products: list[str]) -> tuple[pd.DataFrame, str]:
    """
    Knappar för att hämta alla öppna fotbollsomgångar eller återgå till exempelkupongen.
    Returnerar (kupongdata, nyckel för data_editor). Antalet matcher = antal rader i kupongen.
    """
    col_fetch, col_reset, _ = st.columns([2, 2, 4])
    fetch_clicked = col_fetch.button(
        "🔄 Hämta aktuella omgångar & odds", type="primary",
        use_container_width=True, disabled=not products,
    )
    if fetch_clicked:
        with st.spinner("Hämtar fotbollsomgångar från Svenska Spel …"):
            selected = {p: API_PRODUCTS[p] for p in products}
            draws, fetch_errors = fetch_all_football_draws(selected)
        for msg in fetch_errors:
            st.warning(msg)
        if draws:
            st.session_state["draws"] = draws
            st.session_state["fetch_id"] = st.session_state.get("fetch_id", 0) + 1
            st.session_state["fetched_at"] = datetime.now().strftime("%H:%M:%S")
        else:
            st.error("Hittade inga öppna fotbollsomgångar. Exempelkupongen används tills vidare.")

    if col_reset.button("↩️ Exempelkupong", use_container_width=True):
        st.session_state.pop("draws", None)

    draws: list[dict[str, Any]] | None = st.session_state.get("draws")
    if not draws:
        st.info("Visar exempelkupong. Tryck på knappen för att hämta veckans riktiga fotbollsomgångar.")
        return mock_coupon(mock_n), f"coupon_editor_mock_{mock_n}"

    labels = [f"{draw_label(d)} ({len(_draw_events(d))} matcher)" for d in draws]
    choice = st.selectbox(
        f"Välj omgång ({len(draws)} öppna fotbollsomgångar)",
        range(len(draws)), format_func=lambda i: labels[i],
    )
    draw = draws[choice]
    coupon, missing = draw_to_coupon(draw)

    st.success(f"{draw_label(draw)} · hämtad {st.session_state.get('fetched_at', '')} från Svenska Spel")
    if missing:
        st.warning(
            "Odds saknas för match " + ", ".join(map(str, missing))
            + ". Fyll i dem i tabellen (oddsen publiceras ofta närmare matchstart)."
        )

    ident = f"{draw.get('productName', '')}_{draw.get('drawNumber', choice)}"
    return coupon, f"coupon_editor_{ident}_{st.session_state.get('fetch_id', 0)}"


def render_expekt_source(row_price: int) -> tuple[pd.DataFrame, str]:
    """
    Expekt-Tipset saknar öppet API: användaren klistrar in matcherna och appen
    hämtar odds för samma matcher från Svenska Spels öppna omgångar.
    """
    game = st.selectbox("Expekt-Tipset", list(EXPEKT_GAMES), format_func=lambda g: EXPEKT_GAMES[g][0])
    n_expected = EXPEKT_GAMES[game][1]
    st.markdown(
        f"1. Öppna [Expekt-Tipset ↗]({EXPEKT_URL}) och markera matchlistan för **{EXPEKT_GAMES[game][0]}**.  \n"
        "2. Skriv eller klistra in matcherna nedan med fördelning och odds (1 - X - 2), t.ex. "
        "`Sevilla – Osasuna (53% - 28% - 19%) (1,83 - 3,50 - 4,60)`. Saknas odds: skriv `(Inga odds)`. "
        "Matcherna får stå på samma rad eller en per rad.  \n"
        "3. Matcher utan egna odds kan fyllas i med **Hämta odds** (Svenska Spel och ESPN)."
    )
    pasted = st.text_area(
        "Matcher från Expekt", key=f"expekt_paste_{game}", height=160,
        placeholder="Paris Saint Germain – Olympique Lyonnais (73% - 17% - 10%) (1,32 - 6,00 - 8,00)\n"
                    "Sepsi – Universitatea Craiova (15% - 23% - 62%) (Inga odds)\n…",
    )
    with_odds = parse_matches_with_odds(pasted)
    if with_odds:
        pairs = [(home, away) for home, away, _, _ in with_odds]
        manual_odds: list[Triple | None] = [odds for _, _, odds, _ in with_odds]
        manual_folk: list[Triple | None] = [folk for _, _, _, folk in with_odds]
    else:
        pairs = parse_pasted_matches(pasted)
        manual_odds, manual_folk = [], []

    col_fetch, col_info = st.columns([2, 6])
    if col_fetch.button("🔄 Hämta odds", type="primary", use_container_width=True, disabled=not pairs):
        with st.spinner("Hämtar odds från Svenska Spel och ESPN …"):
            draws, errors = fetch_all_football_draws()
            espn_events, espn_failed = fetch_espn_odds_events()
        for msg in errors:
            st.warning(msg)
        if espn_failed == len(ESPN_LEAGUES):
            st.warning("ESPN svarade inte – bara Svenska Spels odds används.")
        st.session_state["expekt_events"] = svenska_spel_odds_lookup(draws)
        st.session_state["expekt_espn_events"] = espn_events
        st.session_state["expekt_fetch_id"] = st.session_state.get("expekt_fetch_id", 0) + 1

    if not pairs:
        st.info(
            f"Inga matcher inklistrade ännu – visar en exempelkupong med {n_expected} matcher. "
            f"Radpriset på Expekt anger du i sidomenyn (nu {row_price} kr)."
        )
        return mock_coupon(n_expected), f"coupon_editor_expekt_mock_{game}"

    if len(pairs) != n_expected:
        st.warning(
            f"Hittade {len(pairs)} matcher, men {EXPEKT_GAMES[game][0]} har {n_expected}. "
            "Kontrollera inklistringen – du kan också rätta lagnamnen i tabellen nedan."
        )

    events: list[dict[str, Any]] = st.session_state.get("expekt_events") or []
    espn_events: list[dict[str, Any]] = st.session_state.get("expekt_espn_events") or []
    coupon, missing, origins = build_expekt_coupon(
        pairs, events, espn_events, manual_odds=manual_odds, manual_folk=manual_folk
    )
    fetched = "expekt_espn_events" in st.session_state or bool(events)
    n_own = sum(o == "Egna odds" for o in origins)
    if fetched or n_own:
        n_ss = sum(o == "Svenska Spel" for o in origins)
        n_espn = sum(o.startswith("ESPN") for o in origins)
        parts = [f"{n_own} egna"] if n_own else []
        if fetched:
            parts += [f"{n_ss} från Svenska Spel", f"{n_espn} från ESPN"]
        col_info.success(
            f"{len(pairs)} matcher inlästa · odds för {n_own + n_ss + n_espn} ({', '.join(parts)})."
        )
        if missing:
            hint = (
                "matchen hittades varken hos Svenska Spel eller ESPN – rätta lagnamnet och hämta igen, "
                "eller skriv in oddsen i tabellen."
                if fetched else
                "tryck på **Hämta odds** för att söka hos Svenska Spel och ESPN, eller skriv in dem i tabellen."
            )
            st.warning("Odds saknas för match " + ", ".join(map(str, missing)) + " – " + hint)
        with st.expander("Varifrån kommer oddsen?"):
            st.dataframe(
                pd.DataFrame(
                    {"Nr": range(1, len(pairs) + 1),
                     "Match": [f"{h} – {a}" for h, a in pairs],
                     "Oddskälla": [o or "– saknas –" for o in origins]}
                ),
                hide_index=True, use_container_width=True,
            )
    else:
        col_info.caption("Tryck på **Hämta odds**, eller skriv in oddsen själv i tabellen.")
    st.caption(
        "På Expekt visar kolumnerna *Folket %* PoolX-fördelningen (andel av spelarnas rader på "
        "1/X/2), hämtad från %-parentesen du skrev in."
    )
    digest = hashlib.sha256(pasted.encode()).hexdigest()[:10]
    return coupon, f"coupon_editor_expekt_{game}_{digest}_{st.session_state.get('expekt_fetch_id', 0)}"


def main() -> None:
    st.set_page_config(page_title="Tipset-optimeraren", page_icon="⚽", layout="wide")
    st.title("⚽ Tipset-optimeraren")
    settings = render_sidebar()
    tab_football, tab_trav = st.tabs(["⚽ Fotboll", "🐎 V85 (trav)"])
    with tab_football:
        render_football(*settings)
    with tab_trav:
        render_v85_tab()


def render_football(
    budget: int, row_price: int, mock_n: int, products: list[str],
    gemini_key: str, gemini_model: str, ai_allowed: bool,
) -> None:
    """Hela fotbollsdelen: kupong, optimerat system, egna rader, form & skador, AI och sannolikheter."""
    st.caption("Matematiskt optimerade M-system för fotbollskuponger hos Svenska Spel och Expekt.")

    # --- Data input ---------------------------------------------------------
    st.subheader("1. Kupong & odds")
    bookmaker = st.radio(
        "Spelbolag", ["Svenska Spel", "Expekt"], horizontal=True, key="bookmaker",
        help="Svenska Spel: Stryktipset, Europatipset, Topptipset (hämtas automatiskt). "
             "Expekt: Expekt-Tipset Fotboll 13/12/8 (klistras in).",
    )
    if bookmaker == "Expekt":
        source_df, editor_key = render_expekt_source(row_price)
    else:
        source_df, editor_key = render_coupon_source(mock_n, products)
    n_matches = len(source_df)
    for col in FOLK_COLS:  # säkerställ att kolumnerna finns även för äldre data
        if col not in source_df:
            source_df[col] = np.nan
    source_df.insert(0, "Nr", np.arange(1, n_matches + 1))

    edited = st.data_editor(
        source_df,
        key=editor_key,  # ny nyckel vid ny hämtning -> tabellen nollställs
        num_rows="fixed",
        hide_index=True,
        use_container_width=True,
        disabled=["Nr"],
        column_config={
            "Nr": st.column_config.NumberColumn("Nr", width="small"),
            "Hemmalag": st.column_config.TextColumn("Hemmalag", required=True),
            "Bortalag": st.column_config.TextColumn("Bortalag", required=True),
            **{
                c: st.column_config.NumberColumn(c, min_value=1.01, max_value=1000.0, step=0.01, format="%.2f")
                for c in ODDS_COLS
            },
            **{
                c: st.column_config.NumberColumn(
                    c, min_value=0.0, max_value=100.0, step=1.0, format="%.0f",
                    help="Andel av Svenska folkets rader på tecknet (hämtas från Svenska Spel).",
                )
                for c in FOLK_COLS
            },
        },
    )

    errors = validate_coupon(edited)
    if errors:
        for msg in errors:
            st.error(msg)
        return  # (return i stället för st.stop, så att V85-fliken fortfarande visas)

    edited = edited.drop(columns="Nr").reset_index(drop=True)
    edited[ODDS_COLS] = edited[ODDS_COLS].astype(float)
    edited[FOLK_COLS] = edited[FOLK_COLS].apply(pd.to_numeric, errors="coerce")

    # --- Beräkningar --------------------------------------------------------
    max_rows = budget // row_price
    if max_rows < 1:
        st.error("Budgeten räcker inte till en enda rad med valt radpris.")
        return

    probs = compute_probabilities(edited)
    config = find_optimal_system(n_matches, max_rows)
    assigned = assign_signs(probs, config)
    result = build_result_table(assigned)

    system_cost = config.rows * row_price
    coverage = config.rows / 3**n_matches
    # Sannolikhet att systemet innehåller alla rätt (antar oberoende matcher)
    hit_chance = float(assigned["Täckt sannolikhet"].prod())

    # --- Output i flikar ----------------------------------------------------
    st.subheader("2. Analys")
    tab_names = ["🎯 Optimerat system", "✍️ Bygg eget system", "📈 Form & skador", "🔍 Sannolikheter"]
    if ai_allowed:
        tab_names.insert(3, "🤖 AI-analys")
    tabs = dict(zip(tab_names, st.tabs(tab_names)))
    tab_opt, tab_own, tab_form, tab_prob = (
        tabs[name] for name in ("🎯 Optimerat system", "✍️ Bygg eget system", "📈 Form & skador", "🔍 Sannolikheter")
    )

    with tab_opt:
        c1, c2, c3, c4 = st.columns(4)
        c1.metric("Vald budget", f"{budget} kr")
        c2.metric("Faktiskt systempris", f"{system_cost} kr", f"{config.rows} rader", delta_color="off")
        c3.metric("Fördelning", config.label)
        c4.metric("Chans till alla rätt", f"{hit_chance:.2%}")

        st.dataframe(style_result(result), hide_index=True, use_container_width=True)

        st.markdown(
            f"**Täckningsgrad:** {config.rows:,} av {3**n_matches:,} möjliga rader = **{coverage:.4%}**".replace(",", " ")
        )
        st.progress(min(coverage, 1.0))

    with tab_own:
        own_selection = render_manual_builder(
            coupon=edited,
            probs=probs,
            assigned=assigned,
            match_labels=result["Match"],
            coupon_key=editor_key,
            row_price=row_price,
            budget=budget,
            opt_rows=config.rows,
            opt_chance=hit_chance,
        )

    with tab_form:
        injury_notes = render_form_tab(edited, editor_key, gemini_key, gemini_model)

    if ai_allowed:
        with tabs["🤖 AI-analys"]:
            render_ai_tab(
                coupon=edited,
                probs=probs,
                assigned=assigned,
                own_selection=own_selection,
                coupon_key=editor_key,
                row_price=row_price,
                budget=budget,
                api_key=gemini_key,
                model=gemini_model,
                injuries=injury_notes,
            )

    with tab_prob:
        detail = pd.DataFrame(
            {
                "Nr": np.arange(1, n_matches + 1),
                "Match": result["Match"],
                "p(1) %": probs["p1"] * 100,
                "p(X) %": probs["pX"] * 100,
                "p(2) %": probs["p2"] * 100,
                "Folket 1 %": edited["Folket 1 %"],
                "Folket X %": edited["Folket X %"],
                "Folket 2 %": edited["Folket 2 %"],
                "Bolagets marginal %": (probs["margin"] - 1) * 100,
                "Bästa tecken": probs["best_sign"],
                "Täckt sannolikhet %": assigned["Täckt sannolikhet"] * 100,
            }
        )
        st.dataframe(detail.style.format(precision=1, na_rep="–"), hide_index=True, use_container_width=True)
        st.caption(
            "p = marginalfri sannolikhet ur oddsen. 'Chans till alla rätt' = produkten av "
            "täckt sannolikhet per match, under antagandet att matcherna är oberoende."
        )


if __name__ == "__main__":
    main()
