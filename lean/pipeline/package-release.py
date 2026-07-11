#!/usr/bin/env python3
"""Build and verify the downloadable Lean source archive embedded in both sites."""

from __future__ import annotations

import argparse
import base64
import hashlib
import json
import re
import sys
import zipfile
from pathlib import Path


LEAN_ROOT = Path(__file__).resolve().parents[1]
SITE_ROOT = LEAN_ROOT.parent
ARCHIVE = SITE_ROOT / "npcc-lean-formalization.zip"
ARCHIVE_NAME = ARCHIVE.name
CHECKSUM = SITE_ROOT / f"{ARCHIVE_NAME}.sha256"
PREFIX = "npcc-lean-formalization/"
HTML_FILES = [SITE_ROOT / "index.html", SITE_ROOT / "inspector" / "index.html"]
EXCLUDED_PARTS = {".lake", "__pycache__"}
DL_RE = re.compile(
    r'(<script id="dl" type="application/json">)(.*?)(</script>)', re.DOTALL
)


def source_entries() -> list[tuple[str, Path]]:
    files = sorted(
        path
        for path in LEAN_ROOT.rglob("*")
        if path.is_file()
        and not any(part in EXCLUDED_PARTS for part in path.relative_to(LEAN_ROOT).parts)
        and path.suffix not in {".pyc", ".pyo"}
    )
    entries = [(PREFIX + path.relative_to(LEAN_ROOT).as_posix(), path) for path in files]
    for name in ["CITATION.cff", "LICENSE", "LICENSE.md"]:
        path = SITE_ROOT / name
        if path.exists():
            entries.append((PREFIX + name, path))
    return sorted(entries)


def build_archive(entries: list[tuple[str, Path]]) -> bytes:
    temporary = ARCHIVE.with_suffix(ARCHIVE.suffix + ".tmp")
    temporary.unlink(missing_ok=True)
    try:
        with zipfile.ZipFile(
            temporary, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9
        ) as bundle:
            for name, path in entries:
                info = zipfile.ZipInfo(name, date_time=(2026, 1, 1, 0, 0, 0))
                info.compress_type = zipfile.ZIP_DEFLATED
                info.external_attr = 0o100644 << 16
                bundle.writestr(info, path.read_bytes())
        temporary.replace(ARCHIVE)
    finally:
        temporary.unlink(missing_ok=True)
    return ARCHIVE.read_bytes()


def verify_archive(entries: list[tuple[str, Path]], payload: bytes) -> None:
    expected = dict(entries)
    with zipfile.ZipFile(ARCHIVE) as bundle:
        actual_names = bundle.namelist()
        if len(actual_names) != len(set(actual_names)):
            raise ValueError("release archive contains duplicate entries")
        if set(actual_names) != set(expected):
            missing = sorted(set(expected) - set(actual_names))
            extra = sorted(set(actual_names) - set(expected))
            raise ValueError(f"release archive file set differs: missing={missing}, extra={extra}")
        for name, path in expected.items():
            if bundle.read(name) != path.read_bytes():
                raise ValueError(f"release archive has stale bytes for {name}")
    if payload != ARCHIVE.read_bytes():
        raise ValueError("release archive changed while it was being checked")


def embedded_payload(html_path: Path) -> tuple[dict[str, object], bytes]:
    html = html_path.read_text(encoding="utf-8")
    match = DL_RE.search(html)
    if not match:
        raise ValueError(f"{html_path} has no embedded download manifest")
    manifest = json.loads(match.group(2))["lean"]
    return manifest, base64.b64decode(str(manifest["b64"]), validate=True)


def embed(payload: bytes) -> None:
    manifest = {
        "lean": {
            "b64": base64.b64encode(payload).decode("ascii"),
            "name": ARCHIVE_NAME,
            "kb": max(1, round(len(payload) / 1024)),
        }
    }
    encoded = json.dumps(manifest, separators=(",", ":"))
    for html_path in HTML_FILES:
        html = html_path.read_text(encoding="utf-8")
        updated, count = DL_RE.subn(r"\1" + encoded + r"\3", html, count=1)
        if count != 1:
            raise ValueError(f"could not update embedded download in {html_path}")
        with html_path.open("w", encoding="utf-8", newline="") as output:
            output.write(updated)


def verify_embeds(payload: bytes) -> None:
    expected_kb = max(1, round(len(payload) / 1024))
    for html_path in HTML_FILES:
        manifest, embedded = embedded_payload(html_path)
        if manifest.get("name") != ARCHIVE_NAME:
            raise ValueError(f"{html_path} advertises the wrong archive name")
        if manifest.get("kb") != expected_kb:
            raise ValueError(f"{html_path} advertises the wrong archive size")
        if embedded != payload:
            raise ValueError(f"{html_path} embeds a stale release archive")


def checksum_line(payload: bytes) -> str:
    return f"{hashlib.sha256(payload).hexdigest()}  {ARCHIVE_NAME}\n"


def verify_checksum(payload: bytes) -> None:
    if not CHECKSUM.exists() or CHECKSUM.read_text(encoding="ascii") != checksum_line(payload):
        raise ValueError(f"missing or stale release checksum: {CHECKSUM}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true", help="verify without rewriting")
    args = parser.parse_args()

    entries = source_entries()
    if args.check:
        if not ARCHIVE.exists():
            raise ValueError(f"missing release archive: {ARCHIVE}")
        payload = ARCHIVE.read_bytes()
    else:
        payload = build_archive(entries)
        embed(payload)
        CHECKSUM.write_text(checksum_line(payload), encoding="ascii", newline="")

    verify_archive(entries, payload)
    verify_embeds(payload)
    verify_checksum(payload)
    digest = hashlib.sha256(payload).hexdigest()
    print(f"release archive verified: {len(entries)} files, {len(payload)} bytes, sha256={digest}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError, zipfile.BadZipFile, json.JSONDecodeError) as error:
        print(f"release archive check failed: {error}", file=sys.stderr)
        raise SystemExit(1)
