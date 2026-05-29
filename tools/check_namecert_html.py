#!/usr/bin/env python3
"""Gate published NameCert HTML links in dossier dependency data.

The dossier graph stores `html_url` fields that point to generated chapter
pages. This module checks those URLs against the Quarto site tree, so the
published artifact is verified rather than only the source staging directory.
It stays stdlib-only because the gate runs in local tooling and CI workflows.
"""

from __future__ import annotations

import argparse
import json
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DATA_DIR = ROOT / "docs" / "dossier" / "data"
DEP_PATH = DATA_DIR / "dependency.json"
MANIFEST_PATH = DATA_DIR / "namecert_sources.json"
DEFAULT_SITE_ROOT = ROOT / "docs" / "dossier" / "_site"


def load_json(path: Path) -> object:
    return json.loads(path.read_text(encoding="utf-8"))


def page_path(site_root: Path, html_url: str) -> Path:
    return site_root / html_url / "index.html"


def page_exists(site_root: Path, html_url: str) -> bool:
    return page_path(site_root, html_url).exists()


def check(
    dependency_path: Path = DEP_PATH,
    manifest_path: Path = MANIFEST_PATH,
    site_root: Path = DEFAULT_SITE_ROOT,
    allow_partial: bool = True,
    require_manifest_pages: bool = False,
) -> list[str]:
    errors: list[str] = []
    dep = load_json(dependency_path)
    manifest = load_json(manifest_path)
    nodes = dep.get("nodes", []) if isinstance(dep, dict) else []
    sources = manifest if isinstance(manifest, list) else []
    node_by_region = {n.get("id"): n for n in nodes if isinstance(n, dict)}
    urls_by_region: dict[str, set[str]] = {}
    for source in sources:
        if isinstance(source, dict) and source.get("region") and source.get("html_url"):
            urls_by_region.setdefault(str(source.get("region")), set()).add(str(source.get("html_url")))

    site_root = site_root.resolve()

    for node in nodes:
        if not isinstance(node, dict):
            continue
        nid = node.get("id")
        url = node.get("html_url")
        if url is None:
            continue
        if not isinstance(url, str) or not url.startswith("namecert/") or ".." in url:
            errors.append(f"node {nid}: html_url must stay under namecert/: {url!r}")
            continue
        source_urls = urls_by_region.get(str(nid))
        if source_urls and url not in source_urls:
            errors.append(f"node {nid}: html_url {url!r} is not listed in manifest URLs {sorted(source_urls)!r}")
        if not allow_partial and not page_exists(site_root, url):
            errors.append(f"node {nid}: missing {page_path(site_root, url)}")

    for source in sources:
        if not isinstance(source, dict):
            errors.append("manifest contains non-object row")
            continue
        slug = source.get("slug")
        region = source.get("region")
        url = source.get("html_url")
        if not slug or not region or not url:
            errors.append(f"manifest row missing slug/region/html_url: {source!r}")
            continue
        if not isinstance(url, str) or not url.startswith("namecert/") or ".." in url:
            errors.append(f"manifest {slug}: html_url must stay under namecert/: {url!r}")
            continue
        if (require_manifest_pages or not allow_partial) and not page_exists(site_root, url):
            errors.append(f"manifest {slug}: missing {page_path(site_root, url)}")

    for nid in ("kernel", "observer", "interhist"):
        node = node_by_region.get(nid)
        if node and node.get("html_url"):
            errors.append(f"node {nid}: non concrete node must not carry html_url")
    return errors


def self_test() -> int:
    with tempfile.TemporaryDirectory() as td:
        root = Path(td)
        data = root / "data"
        html = root / "site"
        data.mkdir()
        (html / "namecert" / "foo").mkdir(parents=True)
        (html / "namecert" / "foo" / "index.html").write_text("<html></html>", encoding="utf-8")
        dep = data / "dependency.json"
        man = data / "namecert_sources.json"
        dep.write_text(json.dumps({"nodes": [{"id": "foo", "html_url": "namecert/foo/"}, {"id": "kernel"}]}), encoding="utf-8")
        man.write_text(json.dumps([{"slug": "foo", "region": "foo", "html_url": "namecert/foo/"}]), encoding="utf-8")
        assert check(dep, man, site_root=html, require_manifest_pages=True) == []
        dep.write_text(json.dumps({"nodes": [{"id": "foo", "html_url": "../foo/"}]}), encoding="utf-8")
        assert check(dep, man, site_root=html)
    print("[check-namecert-html] self-test ok")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--dependency", type=Path, default=DEP_PATH)
    parser.add_argument("--manifest", type=Path, default=MANIFEST_PATH)
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
        site_root=args.site_root,
        allow_partial=args.allow_partial or not args.full,
        require_manifest_pages=args.allow_partial,
    )
    if errors:
        for err in errors:
            print(f"[check-namecert-html] {err}")
        return 1
    print("[check-namecert-html] ok")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
