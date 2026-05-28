#!/usr/bin/env python3
"""Gate static NameCert HTML links in dossier dependency data."""

from __future__ import annotations

import argparse
import json
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DATA_DIR = ROOT / "docs" / "dossier" / "data"
DEP_PATH = DATA_DIR / "dependency.json"
MANIFEST_PATH = DATA_DIR / "namecert_sources.json"
HTML_ROOT = ROOT / "docs" / "dossier"


def load_json(path: Path) -> object:
    return json.loads(path.read_text(encoding="utf-8"))


def page_exists(html_url: str) -> bool:
    return (HTML_ROOT / html_url / "index.html").exists()


def check(dependency_path: Path = DEP_PATH, manifest_path: Path = MANIFEST_PATH, allow_partial: bool = True) -> list[str]:
    errors: list[str] = []
    dep = load_json(dependency_path)
    manifest = load_json(manifest_path)
    nodes = dep.get("nodes", []) if isinstance(dep, dict) else []
    sources = manifest if isinstance(manifest, list) else []
    node_by_region = {n.get("id"): n for n in nodes if isinstance(n, dict)}

    generated_urls = {
        str(s.get("html_url"))
        for s in sources
        if isinstance(s, dict) and s.get("html_url") and page_exists(str(s.get("html_url")))
    }

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
        if not allow_partial and not page_exists(url):
            errors.append(f"node {nid}: missing {url}index.html")

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
        if allow_partial:
            if url in generated_urls and not page_exists(url):
                errors.append(f"manifest {slug}: generated URL set is inconsistent")
        elif not page_exists(url):
            errors.append(f"manifest {slug}: missing {url}index.html")

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
        global HTML_ROOT
        old = HTML_ROOT
        HTML_ROOT = html
        try:
            assert check(dep, man) == []
            dep.write_text(json.dumps({"nodes": [{"id": "foo", "html_url": "../foo/"}]}), encoding="utf-8")
            assert check(dep, man)
        finally:
            HTML_ROOT = old
    print("[check-namecert-html] self-test ok")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--dependency", type=Path, default=DEP_PATH)
    parser.add_argument("--manifest", type=Path, default=MANIFEST_PATH)
    parser.add_argument("--full", action="store_true", help="require every manifest page to exist")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        return self_test()
    errors = check(args.dependency, args.manifest, allow_partial=not args.full)
    if errors:
        for err in errors:
            print(f"[check-namecert-html] {err}")
        return 1
    print("[check-namecert-html] ok")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
