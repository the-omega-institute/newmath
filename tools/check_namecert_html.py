#!/usr/bin/env python3
"""Gate published dossier HTML links for NameCert and full-paper pages."""

from __future__ import annotations

import argparse
import json
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DATA_DIR = ROOT / "docs" / "dossier" / "data"
DEP_PATH = DATA_DIR / "dependency.json"
MANIFEST_PATH = DATA_DIR / "namecert_sources.json"
PAPER_MANIFEST_PATH = DATA_DIR / "paper_sources.json"
DEFAULT_SITE_ROOT = ROOT / "docs" / "dossier" / "_site"
SCOPES = {"namecert", "paper", "all"}


def load_json(path: Path) -> object:
    return json.loads(path.read_text(encoding="utf-8"))


def normalize_html_url(html_url: str) -> str:
    return html_url.strip().rstrip("/")


def page_path(site_root: Path, html_url: str) -> Path:
    normalized = normalize_html_url(html_url)
    return site_root / normalized / "index.html"


def page_exists(site_root: Path, html_url: str) -> bool:
    return page_path(site_root, html_url).exists()


def validate_url(url: object, prefixes: tuple[str, ...]) -> str | None:
    if not isinstance(url, str) or not url:
        return f"html_url must be a non-empty string: {url!r}"
    if url.startswith("/") or "\\" in url or "://" in url:
        return f"html_url must be relative under dossier pages: {url!r}"
    parts = [part for part in url.split("/") if part]
    if any(part in {"..", "."} for part in parts):
        return f"html_url must not escape dossier pages: {url!r}"
    if not any(url.startswith(prefix) for prefix in prefixes):
        return f"html_url must stay under {prefixes!r}: {url!r}"
    return None


def read_manifest_rows(path: Path) -> list[dict]:
    if not path.exists():
        return []
    manifest = load_json(path)
    return [dict(row) for row in manifest] if isinstance(manifest, list) else []


def check_namecert_manifest(
    manifest_path: Path = MANIFEST_PATH,
    site_root: Path = DEFAULT_SITE_ROOT,
    allow_partial: bool = True,
    require_manifest_pages: bool = False,
) -> list[str]:
    errors: list[str] = []
    sources = read_manifest_rows(manifest_path)
    for source in sources:
        slug = source.get("slug")
        region = source.get("region")
        url = source.get("html_url")
        if not slug or not region or not url:
            errors.append(f"manifest row missing slug/region/html_url: {source!r}")
            continue
        url_error = validate_url(url, ("namecert/",))
        if url_error:
            errors.append(f"manifest {slug}: {url_error}")
            continue
        if (require_manifest_pages or not allow_partial) and not page_exists(site_root, str(url)):
            errors.append(f"manifest {slug}: missing {page_path(site_root, str(url))}")
    return errors


def check_paper_manifest(
    paper_manifest_path: Path = PAPER_MANIFEST_PATH,
    site_root: Path = DEFAULT_SITE_ROOT,
    allow_partial: bool = True,
    require_manifest_pages: bool = False,
) -> list[str]:
    errors: list[str] = []
    sources = read_manifest_rows(paper_manifest_path)
    for source in sources:
        slug = source.get("slug")
        url = source.get("html_url")
        order = source.get("order")
        if not slug or not url or order is None:
            errors.append(f"paper manifest row missing slug/order/html_url: {source!r}")
            continue
        url_error = validate_url(url, ("paper/", "namecert/"))
        if url_error:
            errors.append(f"paper manifest {slug}: {url_error}")
            continue
        if (require_manifest_pages or not allow_partial) and not page_exists(site_root, str(url)):
            errors.append(f"paper manifest {slug}: missing {page_path(site_root, str(url))}")
    return errors


def check_dependency_links(
    dependency_path: Path = DEP_PATH,
    manifest_path: Path = MANIFEST_PATH,
    site_root: Path = DEFAULT_SITE_ROOT,
    allow_partial: bool = True,
) -> list[str]:
    errors: list[str] = []
    dep = load_json(dependency_path)
    sources = read_manifest_rows(manifest_path)
    nodes = dep.get("nodes", []) if isinstance(dep, dict) else []
    node_by_region = {n.get("id"): n for n in nodes if isinstance(n, dict)}
    urls_by_region: dict[str, set[str]] = {}
    for source in sources:
        if source.get("region") and source.get("html_url"):
            urls_by_region.setdefault(str(source.get("region")), set()).add(str(source.get("html_url")))

    for node in nodes:
        if not isinstance(node, dict):
            continue
        nid = node.get("id")
        url = node.get("html_url")
        if url is None:
            continue
        url_error = validate_url(url, ("namecert/",))
        if url_error:
            errors.append(f"node {nid}: {url_error}")
            continue
        source_urls = urls_by_region.get(str(nid))
        if source_urls and url not in source_urls:
            errors.append(f"node {nid}: html_url {url!r} is not listed in manifest URLs {sorted(source_urls)!r}")
        if not allow_partial and not page_exists(site_root, str(url)):
            errors.append(f"node {nid}: missing {page_path(site_root, str(url))}")

    for nid in ("kernel", "observer", "interhist"):
        node = node_by_region.get(nid)
        if node and node.get("html_url"):
            errors.append(f"node {nid}: non concrete node must not carry html_url")
    return errors


def check(
    dependency_path: Path = DEP_PATH,
    manifest_path: Path = MANIFEST_PATH,
    paper_manifest_path: Path = PAPER_MANIFEST_PATH,
    site_root: Path = DEFAULT_SITE_ROOT,
    allow_partial: bool = True,
    require_manifest_pages: bool = False,
    scope: str = "namecert",
) -> list[str]:
    if scope not in SCOPES:
        raise ValueError(f"unknown scope: {scope}")
    errors: list[str] = []
    if scope in {"namecert", "all"}:
        errors.extend(check_dependency_links(dependency_path, manifest_path, site_root, allow_partial))
        errors.extend(check_namecert_manifest(manifest_path, site_root, allow_partial, require_manifest_pages))
    if scope in {"paper", "all"}:
        errors.extend(check_paper_manifest(paper_manifest_path, site_root, allow_partial, require_manifest_pages))
    return errors


def self_test() -> int:
    with tempfile.TemporaryDirectory() as td:
        root = Path(td)
        data = root / "data"
        html = root / "site"
        data.mkdir()
        (html / "namecert" / "foo").mkdir(parents=True)
        (html / "namecert" / "foo" / "index.html").write_text("<html></html>", encoding="utf-8")
        (html / "paper" / "bar").mkdir(parents=True)
        (html / "paper" / "bar" / "index.html").write_text("<html></html>", encoding="utf-8")
        dep = data / "dependency.json"
        man = data / "namecert_sources.json"
        paper = data / "paper_sources.json"
        dep.write_text(json.dumps({"nodes": [{"id": "foo", "html_url": "namecert/foo/"}, {"id": "kernel"}]}), encoding="utf-8")
        man.write_text(json.dumps([{"slug": "foo", "region": "foo", "html_url": "namecert/foo/"}]), encoding="utf-8")
        paper.write_text(json.dumps([{"slug": "bar", "order": 1, "html_url": "paper/bar/"}]), encoding="utf-8")
        assert check(dep, man, paper, site_root=html, require_manifest_pages=True, scope="all") == []
        paper.write_text(json.dumps([{"slug": "bad", "order": 1, "html_url": "../foo/"}]), encoding="utf-8")
        assert check(dep, man, paper, site_root=html, scope="paper")
    print("[check-namecert-html] self-test ok")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--scope", choices=sorted(SCOPES), default="namecert")
    parser.add_argument("--dependency", type=Path, default=DEP_PATH)
    parser.add_argument("--manifest", type=Path, default=MANIFEST_PATH)
    parser.add_argument("--paper-manifest", type=Path, default=PAPER_MANIFEST_PATH)
    parser.add_argument("--site-root", type=Path, default=DEFAULT_SITE_ROOT)
    parser.add_argument("--allow-partial", action="store_true", help="validate URL structure without requiring every page to exist")
    parser.add_argument("--full", action="store_true", help="require every manifest page to exist")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.full and args.allow_partial:
        parser.error("--full and --allow-partial are mutually exclusive")
    if args.self_test:
        return self_test()
    errors = check(
        args.dependency,
        args.manifest,
        args.paper_manifest,
        site_root=args.site_root,
        allow_partial=args.allow_partial or not args.full,
        require_manifest_pages=args.full,
        scope=args.scope,
    )
    if errors:
        for err in errors:
            print(f"[check-namecert-html] {err}")
        return 1
    print("[check-namecert-html] ok")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
