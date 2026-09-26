#!/usr/bin/env python3
"""Fetch + enrich podcast RSS feeds on a GitHub Actions runner.

Reads batches/<batch_id>/targets.json (list of {show_id, feed_url, title,
artist, niche, ...}) and writes per-show enrichment records to results.json
(uploaded as an Actions ARTIFACT by the workflow - never committed to git).

Fetch rules (mirrors the nfa tiered rules):
  - curl_cffi with rotating browser TLS profiles + retries on transient errors
  - CAPTCHA / challenge / login pages -> fetch failure, never solved or bypassed
  - 403/401/404 are never retried
  - podcast RSS feeds are published for automated fetching (podcatchers), so
    no robots.txt gate is applied here; blocks are still never defeated.

Usage:
  python worker/fetch_feeds.py --targets batches/x/targets.json --out results.json
"""
import argparse
import json
import os
import random
import re
import sys
import time
import xml.etree.ElementTree as ET
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import date, datetime, timezone

import feedparser
from curl_cffi.requests import Session
from curl_cffi.requests import exceptions as cexc

PROFILES = [
    {"impersonate": "chrome",
     "headers": {"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                 "AppleWebKit/537.36 (KHTML, like Gecko) "
                 "Chrome/126.0.0.0 Safari/537.36"}},
    {"impersonate": "firefox",
     "headers": {"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64; "
                 "rv:127.0) Gecko/20100101 Firefox/127.0"}},
    {"impersonate": "safari",
     "headers": {"User-Agent": "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) "
                 "AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.4 "
                 "Safari/605.1.15"}},
]

ITUNES_NS = "http://www.itunes.com/dtds/podcast-1.0.dtd"
PODCAST_NS = "https://podcastindex.org/namespace/1.0"
MAX_FEED_BYTES = 8 * 1024 * 1024
FEED_TIMEOUT = 25
VIDEO_EXTS = (".mp4", ".mov", ".m4v", ".webm")
WORKERS = 8
RETRYABLE = (cexc.Timeout, cexc.ConnectionError, cexc.SSLError)

# --- challenge markers: an interstitial that IS the challenge, not content ---
CHALLENGE_MARKERS = (
    "cf-challenge", "cf_challenge", "cdn-cgi/challenge-platform",
    "just a moment", "verifying you are human", "attention required",
    "are you a robot", "please verify you are",
)

# --- sponsor / money-signal detection (editable brand list) ---
SPONSOR_PATTERNS = [
    r"sponsored by", r"brought to you by", r"thanks to our sponsor",
    r"use code", r"promo code", r"discount code", r"affiliate link",
    r"free trial", r"\b\d{1,2}\s*%\s*off\b", r"percent off",
]
PREMIUM_BRANDS = [
    "squarespace", "shopify", "wix", "nordvpn", "expressvpn", "betterhelp",
    "athletic greens", "ag1", "factor", "hellofresh", "butcherbox", "indeed",
    "hubspot", "notion", "masterclass", "skillshare", "audible", "seed",
    "momentous",
    "rocket money", "monarch", "betterment", "wealthfront", "fundrise",
    "public.com", "moomoo", "tradingview", "sofi",
    "deleteme", "granola",
]
SPONSOR_RES = [re.compile(p, re.I) for p in SPONSOR_PATTERNS]
BRAND_RES = []
for _b in PREMIUM_BRANDS:
    if _b == "seed":
        # "Seed" the probiotic brand vs "seed oil(s)" topic chatter
        BRAND_RES.append((_b, re.compile(r"\bseed\b(?!\s+oils?\b)", re.I)))
    else:
        BRAND_RES.append((_b, re.compile(r"\b" + re.escape(_b) + r"\b", re.I)))

YOUTUBE_URL_RE = re.compile(
    r"https?://(?:www\.)?youtube\.com/(?:c/|channel/|user/|@)[\w\-.@]+", re.I)
TIKTOK_URL_RE = re.compile(r"https?://(?:www\.)?tiktok\.com/@[\w.\-]+", re.I)
IG_URL_RE = re.compile(r"https?://(?:www\.)?instagram\.com/([\w.\-]+)", re.I)
X_URL_RE = re.compile(r"https?://(?:www\.)?(?:x\.com|twitter\.com)/([\w]+)", re.I)
IG_BAD_PATHS = {"p", "reel", "reels", "explore", "stories", "tv", "accounts",
                "about", "developer", "direct"}
X_BAD_PATHS = {"home", "explore", "intent", "share", "hashtag", "search", "i",
               "settings", "login", "signup", "tos", "privacy"}


def harvest_social(text):
    """Extract first TikTok/YouTube/Instagram/X profile URL from text."""
    out = {}
    m = TIKTOK_URL_RE.search(text)
    if m:
        out["tiktok"] = m.group(0).rstrip("/")
    m = YOUTUBE_URL_RE.search(text)
    if m:
        out["youtube"] = m.group(0).rstrip("/")
    m = IG_URL_RE.search(text)
    if m and m.group(1).lower() not in IG_BAD_PATHS:
        out["instagram"] = "https://www.instagram.com/" + m.group(1).rstrip(".")
    m = X_URL_RE.search(text)
    if m and m.group(1).lower() not in X_BAD_PATHS:
        out["x"] = "https://x.com/" + m.group(1)
    return out


JUNK_PREFIXES = re.compile(
    r"^(noreply|no-reply|donotreply|do-not-reply|do_not_reply|bounce|bounces|"
    r"mailer-daemon|postmaster|abuse|privacy|unsubscribe|list-unsubscribe|"
    r"test@|example@|webmaster@|hostmaster@|null@|none@|invalid@)", re.I)

HOSTING_DOMAINS = {
    "libsyn.com", "buzzsprout.com", "podbean.com", "anchor.fm", "transistor.fm",
    "captivate.fm", "spreaker.com", "blubrry.com", "rss.com", "redcircle.com",
    "megaphone.fm", "simplecast.com", "acast.com", "omnystudio.com", "art19.com",
    "podomatic.com", "soundcloud.com", "whooshkaa.com", "audioboom.com",
    "podiant.co", "pinecast.com", "fireside.fm", "zencastr.com", "podserve.fm",
    "iono.fm", "shoutengine.com", "podigee.com", "letscast.fm", "podcasts.com",
    "podyssey.fm", "hearthis.at", "mixcloud.com", "podtail.com",
}

EMAIL_RE = re.compile(r"^[A-Za-z0-9._%+\-]+@[A-Za-z0-9.\-]+\.[A-Za-z]{2,}$")


def clean_email(raw):
    if not raw:
        return None
    e = raw.strip().lower()
    e = e.replace("[at]", "@").replace("[dot]", ".").replace("(at)", "@").replace("(dot)", ".")
    e = e.strip(" <>\"'.,;")
    if not EMAIL_RE.match(e):
        return None
    local, _, domain = e.partition("@")
    if JUNK_PREFIXES.match(local) or JUNK_PREFIXES.match(e):
        return None
    if domain in HOSTING_DOMAINS or any(domain.endswith("." + d) for d in HOSTING_DOMAINS):
        return None
    if len(e) > 254 or ".." in e:
        return None
    return e


def looks_like_challenge(text):
    low = text[:20000].lower()
    return any(m in low for m in CHALLENGE_MARKERS)


def fetch_bytes(url):
    """Fetch a URL with rotating TLS profiles. Returns (bytes, error_reason).
    error_reason is None on success; otherwise a short failure code."""
    last_err = "unknown"
    for attempt in range(3):
        prof = random.choice(PROFILES)
        try:
            with Session(impersonate=prof["impersonate"]) as s:
                s.headers.update(prof["headers"])
                r = s.get(url, timeout=FEED_TIMEOUT, stream=True,
                          allow_redirects=True, max_redirects=5)
                code = r.status_code
                if code in (401, 403):
                    return None, "http_403"
                if code == 404:
                    return None, "http_404"
                if code == 429:
                    last_err = "http_429"
                    time.sleep(2 ** attempt)
                    continue
                if code >= 500:
                    last_err = f"http_{code}"
                    time.sleep(2 ** attempt)
                    continue
                if code >= 400:
                    return None, f"http_{code}"
                chunks, size = [], 0
                truncated = False
                for c in r.iter_content(65536):
                    chunks.append(c)
                    size += len(c)
                    if size > MAX_FEED_BYTES:
                        truncated = True
                        break
                raw = b"".join(chunks)
                if looks_like_challenge(raw.decode("utf-8", "ignore")):
                    return None, "challenge_page"
                return raw, ("truncated" if truncated else None)
        except RETRYABLE as e:
            last_err = f"{type(e).__name__}"
            time.sleep(2 ** attempt)
        except cexc.RequestsError as e:
            return None, f"request_error:{type(e).__name__}"
        except Exception as e:  # DNS etc.
            return None, f"fetch_error:{type(e).__name__}"
    return None, last_err


def owner_email_from_xml(raw):
    """Targeted namespace scan of the channel header for owner emails.
    Order: itunes:owner/itunes:email -> podcast:locked @owner -> managingEditor.
    Returns (email, source)."""
    try:
        root = ET.fromstring(raw)
    except ET.ParseError:
        cut = raw.rfind(b"</item>")
        if cut == -1:
            return None, None
        try:
            root = ET.fromstring(raw[:cut + len(b"</item>")] + b"</channel></rss>")
        except ET.ParseError:
            return None, None
    ch = root.find("channel")
    if ch is None:
        ch = root
    owner = ch.find(f"{{{ITUNES_NS}}}owner")
    if owner is not None:
        oe = owner.find(f"{{{ITUNES_NS}}}email")
        if oe is not None and oe.text:
            e = clean_email(oe.text)
            if e:
                on = owner.find(f"{{{ITUNES_NS}}}name")
                name = on.text.strip() if on is not None and on.text else None
                return e, "itunes_owner", name
    locked = ch.find(f"{{{PODCAST_NS}}}locked")
    if locked is not None and locked.get("owner"):
        e = clean_email(locked.get("owner"))
        if e:
            return e, "podcast_locked", None
    me = ch.findtext("managingEditor")
    if me:
        m = re.search(r"[\w.+-]+@[\w-]+\.[\w.]+", me)
        if m:
            e = clean_email(m.group(0))
            if e:
                return e, "managing_editor", None
    return None, None, None


def entry_text(entry):
    parts = []
    desc = entry.get("description") or ""
    if desc:
        parts.append(desc)
    for c in entry.get("content") or []:
        v = c.get("value") if isinstance(c, dict) else None
        if v:
            parts.append(v)
    return " ".join(parts)


def enrich_one(target):
    show_id = target.get("show_id")
    url = target.get("feed_url", "")
    rec = {
        "show_id": show_id,
        "feed_url": url,
        "title": target.get("title"),
        "artist": target.get("artist"),
        "niche": target.get("niche"),
        "genres": target.get("genres"),
        "episode_count": target.get("episode_count"),  # iTunes trackCount
        "artwork_url": target.get("artwork_url"),
        "email": None, "email_source": None, "owner_name": None,
        "website_url": None,
        "youtube_url": None, "tiktok_url": None,
        "instagram_url": None, "x_url": None,
        "description_len": 0,
        "feed_entry_count": 0,
        "has_video": False, "video_episode_count": 0,
        "last_episode_date": None, "days_since_last_episode": None,
        "sponsor_mentions": 0, "sponsor_brands": [],
        "has_premium_sponsor": False,
        "fetch_status": "error", "fetch_error": None,
        "fetched_at": datetime.now(timezone.utc).isoformat(),
    }
    raw, err = fetch_bytes(url)
    if raw is None:
        rec["fetch_error"] = err
        return rec
    truncated = (err == "truncated")

    d = feedparser.parse(raw)
    if not d.entries and truncated:
        # Big feeds get cut mid-XML by the size cap; the channel header and
        # most-recent items sit at the start, so recover at the last </item>.
        cut = raw.rfind(b"</item>")
        if cut != -1:
            d = feedparser.parse(raw[:cut + len(b"</item>")] + b"</channel></rss>")

    feed = d.feed
    entries = d.entries or []
    rec["feed_entry_count"] = len(entries)

    # --- owner email (namespace scan of channel header) ---
    email, source, owner_name = owner_email_from_xml(raw)
    rec["email"], rec["email_source"], rec["owner_name"] = email, source, owner_name

    # --- website / description / artwork ---
    site = (feed.get("link") or "").strip()
    if site and not site.startswith(("http://", "https://")):
        site = None
    rec["website_url"] = site or None
    desc = feed.get("description") or feed.get("subtitle") or ""
    # strip HTML tags for a length measure
    desc_text = re.sub(r"<[^>]+>", " ", desc)
    desc_text = re.sub(r"\s+", " ", desc_text).strip()
    rec["description_len"] = len(desc_text)
    if not rec["artwork_url"]:
        img = feed.get("image") or {}
        rec["artwork_url"] = img.get("href") or None

    # --- social: channel header of the feed XML ONLY (no homepage fetches) ---
    head_txt = raw.decode("utf-8", "ignore")
    cut = head_txt.find("<item")
    ecut = head_txt.find("<entry")
    if cut == -1 or (ecut != -1 and ecut < cut):
        cut = ecut
    channel_head = head_txt[:cut] if cut != -1 else head_txt
    social = harvest_social(channel_head)
    rec["youtube_url"] = social.get("youtube")
    rec["tiktok_url"] = social.get("tiktok")
    rec["instagram_url"] = social.get("instagram")
    rec["x_url"] = social.get("x")

    # --- video detection + recency + sponsor scan: 10 newest episodes ---
    video_ct = 0
    last_pub = None
    sponsor_episodes = 0
    sponsor_brands = set()
    for entry in entries[:10]:
        for enc in entry.get("enclosures") or []:
            etype = (enc.get("type") or "").lower()
            ehref = (enc.get("href") or "").lower()
            if etype.startswith("video/") or ehref.endswith(VIDEO_EXTS):
                video_ct += 1
                break
        pp = entry.get("published_parsed") or entry.get("updated_parsed")
        if pp and last_pub is None:
            try:
                last_pub = date(pp[0], pp[1], pp[2]).isoformat()
            except Exception:
                pass
        ep_text = entry_text(entry)
        if ep_text and any(rx.search(ep_text) for rx in SPONSOR_RES):
            sponsor_episodes += 1
            for brand, brx in BRAND_RES:
                if brx.search(ep_text):
                    sponsor_brands.add(brand)

    days_since = None
    if last_pub:
        try:
            days_since = (date.today() - date.fromisoformat(last_pub)).days
        except Exception:
            pass

    rec.update({
        "has_video": video_ct > 0,
        "video_episode_count": video_ct,
        "last_episode_date": last_pub,
        "days_since_last_episode": days_since,
        "sponsor_mentions": sponsor_episodes,
        "sponsor_brands": sorted(sponsor_brands),
        "has_premium_sponsor": len(sponsor_brands) > 0,
        "fetch_status": "ok",
        "fetch_error": "truncated_recovered" if truncated else None,
    })
    return rec


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--targets", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--workers", type=int, default=WORKERS)
    args = ap.parse_args()

    with open(args.targets, encoding="utf-8") as f:
        targets = json.load(f)
    print(f"[fetch_feeds] {len(targets)} targets, {args.workers} workers",
          flush=True)

    results = []
    done = 0
    with ThreadPoolExecutor(max_workers=args.workers) as ex:
        futs = {ex.submit(enrich_one, t): t for t in targets}
        for fut in as_completed(futs):
            try:
                results.append(fut.result())
            except Exception as e:
                t = futs[fut]
                results.append({
                    "show_id": t.get("show_id"), "feed_url": t.get("feed_url"),
                    "title": t.get("title"), "fetch_status": "error",
                    "fetch_error": f"worker_exception:{type(e).__name__}",
                    "fetched_at": datetime.now(timezone.utc).isoformat(),
                })
            done += 1
            if done % 25 == 0 or done == len(targets):
                ok = sum(1 for r in results if r["fetch_status"] == "ok")
                em = sum(1 for r in results if r.get("email"))
                print(f"[fetch_feeds] {done}/{len(targets)} ok={ok} emailed={em}",
                      flush=True)

    # keep input order for stable output
    order = {t.get("show_id"): i for i, t in enumerate(targets)}
    results.sort(key=lambda r: order.get(r.get("show_id"), 10 ** 9))
    with open(args.out, "w", encoding="utf-8") as f:
        json.dump(results, f, ensure_ascii=False)
    ok = sum(1 for r in results if r["fetch_status"] == "ok")
    print(f"[fetch_feeds] wrote {len(results)} records ({ok} ok) -> {args.out}",
          flush=True)


if __name__ == "__main__":
    main()
