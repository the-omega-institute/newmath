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

    def test_full_gate_rejects_missing_published_page(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            data = root / "data"
            site = root / "site"
            data.mkdir()
            dep = data / "dependency.json"
            manifest = data / "namecert_sources.json"
            dep.write_text(
                json.dumps({"nodes": [{"id": "foo", "html_url": "namecert/foo/"}]}),
                encoding="utf-8",
            )
            manifest.write_text(
                json.dumps([{"slug": "foo", "region": "foo", "html_url": "namecert/foo/"}]),
                encoding="utf-8",
            )

            errors = check_namecert_html.check(dep, manifest, site_root=site, allow_partial=False)

        self.assertTrue(errors)
        self.assertTrue(any("missing" in err and "namecert/foo" in err for err in errors))

    def test_scan_sources_extracts_slug_and_source_from_chapter_label(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            parts = root / "papers" / "bedc" / "parts" / "concrete_instances"
            src = parts / "foo" / "namecert_construction.tex"
            src.parent.mkdir(parents=True)
            src.write_text(
                "\\chapter{Foo}\n\\label{ch:concrete-instances-foo-namecert}\n",
                encoding="utf-8",
            )
            old_root = build_namecert_html.ROOT
            old_parts = build_namecert_html.PARTS_DIR
            build_namecert_html.ROOT = root
            build_namecert_html.PARTS_DIR = parts
            try:
                rows = build_namecert_html.scan_sources()
            finally:
                build_namecert_html.ROOT = old_root
                build_namecert_html.PARTS_DIR = old_parts

        self.assertEqual(rows, [{
            "slug": "foo",
            "region": "foo",
            "source": "papers/bedc/parts/concrete_instances/foo/namecert_construction.tex",
            "html_url": "namecert/foo/",
        }])

    def test_nav_html_renders_upstream_and_downstream_links(self) -> None:
        rows_by_region = {
            "bar": {"slug": "bar"},
            "baz": {"slug": "baz"},
            "foo": {"slug": "foo"},
        }
        html = build_namecert_html.nav_html({"slug": "foo"}, rows_by_region, ["bar"], ["baz"])

        self.assertIn("Depends on:", html)
        self.assertIn('<a href="../bar/">bar</a>', html)
        self.assertIn("Used by:", html)
        self.assertIn('<a href="../baz/">baz</a>', html)

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
            self.assertTrue(check_namecert_html.check(dep, manifest, site_root=html))

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
            self.assertEqual(check_namecert_html.check(dep, manifest, site_root=html), [])


if __name__ == "__main__":
    unittest.main()
