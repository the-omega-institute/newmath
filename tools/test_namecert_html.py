#!/usr/bin/env python3
"""Small stdlib tests for NameCert HTML helpers."""

from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

import build_namecert_html
import check_namecert_html


class NamecertHtmlTests(unittest.TestCase):
    def test_slug_region_normalization(self) -> None:
        self.assertEqual(build_namecert_html.normalize_region("real-sequence-algebra"), "realsequencealgebra")

    def test_dependency_nav_edges(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            dep = Path(td) / "dependency.json"
            dep.write_text(
                json.dumps({
                    "nodes": [{"id": "foo"}, {"id": "bar"}, {"id": "baz"}],
                    "edges": [
                        {"source": "bar", "target": "foo"},
                        {"source": "foo", "target": "baz"},
                    ],
                }),
                encoding="utf-8",
            )
            up, down = build_namecert_html.dependency_edges(dep)
        self.assertEqual(up["foo"], ["bar"])
        self.assertEqual(down["foo"], ["baz"])

    def test_gate_rejects_escape_url(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            data = root / "data"
            html = root / "site"
            data.mkdir()
            dep = data / "dependency.json"
            manifest = data / "namecert_sources.json"
            dep.write_text(json.dumps({"nodes": [{"id": "foo", "html_url": "../foo/"}]}), encoding="utf-8")
            manifest.write_text(json.dumps([]), encoding="utf-8")
            old = check_namecert_html.HTML_ROOT
            check_namecert_html.HTML_ROOT = html
            try:
                self.assertTrue(check_namecert_html.check(dep, manifest))
            finally:
                check_namecert_html.HTML_ROOT = old

    def test_gate_accepts_existing_page(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            data = root / "data"
            html = root / "site"
            data.mkdir()
            (html / "namecert" / "foo").mkdir(parents=True)
            (html / "namecert" / "foo" / "index.html").write_text("<html></html>", encoding="utf-8")
            dep = data / "dependency.json"
            manifest = data / "namecert_sources.json"
            dep.write_text(json.dumps({"nodes": [{"id": "foo", "html_url": "namecert/foo/"}, {"id": "kernel"}]}), encoding="utf-8")
            manifest.write_text(json.dumps([{"slug": "foo", "region": "foo", "html_url": "namecert/foo/"}]), encoding="utf-8")
            old = check_namecert_html.HTML_ROOT
            check_namecert_html.HTML_ROOT = html
            try:
                self.assertEqual(check_namecert_html.check(dep, manifest), [])
            finally:
                check_namecert_html.HTML_ROOT = old


if __name__ == "__main__":
    unittest.main()
