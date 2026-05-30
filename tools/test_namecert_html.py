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
            "scope": "namecert",
            "kind": "namecert",
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

    def test_scan_paper_sources_keeps_main_order_and_part(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            paper_dir = root / "papers" / "bedc"
            (paper_dir / "parts").mkdir(parents=True)
            main = paper_dir / "main.tex"
            main.write_text(
                "\\part{Alpha}\n"
                "\\input{parts/one.tex}\n"
                "\\part{Beta}\n"
                "\\chapter{Inline Chapter}\n"
                "\\input{parts/two.tex}\n",
                encoding="utf-8",
            )
            (paper_dir / "parts" / "one.tex").write_text("\\chapter{One}\n", encoding="utf-8")
            (paper_dir / "parts" / "two.tex").write_text("Body\n", encoding="utf-8")

            old_root = build_namecert_html.ROOT
            old_paper = build_namecert_html.PAPER_DIR
            old_main = build_namecert_html.MAIN_TEX
            build_namecert_html.ROOT = root
            build_namecert_html.PAPER_DIR = paper_dir
            build_namecert_html.MAIN_TEX = main
            try:
                rows = build_namecert_html.scan_paper_sources(main, [])
            finally:
                build_namecert_html.ROOT = old_root
                build_namecert_html.PAPER_DIR = old_paper
                build_namecert_html.MAIN_TEX = old_main

        self.assertEqual([row["source"] for row in rows], [
            "papers/bedc/parts/one.tex",
            "papers/bedc/parts/two.tex",
        ])
        self.assertEqual(rows[0]["part"], "Alpha")
        self.assertEqual(rows[0]["chapter"], "One")
        self.assertEqual(rows[1]["part"], "Beta")
        self.assertEqual(rows[1]["chapter"], "Inline Chapter")

    def test_scan_paper_sources_reuses_namecert_urls(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            paper_dir = root / "papers" / "bedc"
            src = paper_dir / "parts" / "concrete_instances" / "foo" / "namecert_construction.tex"
            src.parent.mkdir(parents=True)
            main = paper_dir / "main.tex"
            main.write_text("\\part{Concrete}\n\\input{parts/concrete_instances/foo/namecert_construction.tex}\n", encoding="utf-8")
            src.write_text("\\chapter{Foo}\n\\label{ch:concrete-instances-foo-namecert}\n", encoding="utf-8")

            old_root = build_namecert_html.ROOT
            old_paper = build_namecert_html.PAPER_DIR
            build_namecert_html.ROOT = root
            build_namecert_html.PAPER_DIR = paper_dir
            try:
                rows = build_namecert_html.scan_paper_sources(main, [{
                    "slug": "foo",
                    "region": "foo",
                    "source": "papers/bedc/parts/concrete_instances/foo/namecert_construction.tex",
                    "html_url": "namecert/foo/",
                }])
            finally:
                build_namecert_html.ROOT = old_root
                build_namecert_html.PAPER_DIR = old_paper

        self.assertEqual(rows[0]["html_url"], "namecert/foo/")
        self.assertTrue(rows[0]["reused_namecert"])

    def test_scan_paper_sources_uses_paper_prefix_for_non_namecert(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            paper_dir = root / "papers" / "bedc"
            (paper_dir / "parts").mkdir(parents=True)
            main = paper_dir / "main.tex"
            main.write_text("\\part{Alpha}\n\\input{parts/core_intro.tex}\n", encoding="utf-8")
            (paper_dir / "parts" / "core_intro.tex").write_text("\\chapter{Core Intro}\n", encoding="utf-8")
            old_root = build_namecert_html.ROOT
            old_paper = build_namecert_html.PAPER_DIR
            build_namecert_html.ROOT = root
            build_namecert_html.PAPER_DIR = paper_dir
            try:
                rows = build_namecert_html.scan_paper_sources(main, [])
            finally:
                build_namecert_html.ROOT = old_root
                build_namecert_html.PAPER_DIR = old_paper

        self.assertEqual(rows[0]["html_url"], "paper/1-core-intro/")
        self.assertFalse(rows[0]["reused_namecert"])

    def test_macro_prelude_collects_and_guards_simple_declarations(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            tex = root / "a.tex"
            tex.write_text(
                "\\newcommand{\\Foo}{Foo}\n"
                "\\providecommand{\\Bar}{Bar}\n"
                "\\def\\Baz#1{#1}\n",
                encoding="utf-8",
            )
            old_root = build_namecert_html.ROOT
            build_namecert_html.ROOT = root
            try:
                prelude = build_namecert_html.collect_macro_prelude([{"source": "a.tex"}])
            finally:
                build_namecert_html.ROOT = old_root

        self.assertIn("\\providecommand{\\Foo}{Foo}", prelude)
        self.assertIn("\\providecommand{\\Bar}{Bar}", prelude)
        self.assertIn("\\def\\Baz#1{#1}", prelude)

    def test_fingerprint_changes_with_macro_prelude_and_recursive_input(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            paper = root / "papers" / "bedc"
            paper.mkdir(parents=True)
            src = paper / "source.tex"
            child = paper / "child.tex"
            preamble = paper / "preamble.tex"
            cfg = paper / "make4ht-dossier.cfg"
            src.write_text("\\input{child.tex}\n", encoding="utf-8")
            child.write_text("A\n", encoding="utf-8")
            preamble.write_text("", encoding="utf-8")
            cfg.write_text("", encoding="utf-8")
            old_root = build_namecert_html.ROOT
            old_paper = build_namecert_html.PAPER_DIR
            build_namecert_html.ROOT = root
            build_namecert_html.PAPER_DIR = paper
            row = {"scope": "paper", "slug": "source", "region": "source", "source": "papers/bedc/source.tex", "html_url": "paper/1-source/"}
            try:
                a = build_namecert_html.region_fingerprint(row, {}, {}, {}, "", False, "", src, "")
                b = build_namecert_html.region_fingerprint(row, {}, {}, {}, "", False, "", src, "\\providecommand{\\Foo}{Foo}\n")
                child.write_text("B\n", encoding="utf-8")
                c = build_namecert_html.region_fingerprint(row, {}, {}, {}, "", False, "", src, "")
            finally:
                build_namecert_html.ROOT = old_root
                build_namecert_html.PAPER_DIR = old_paper

        self.assertNotEqual(a, b)
        self.assertNotEqual(a, c)

    def test_checker_scope_paper_accepts_paper_url_and_rejects_escape(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            site = root / "site"
            data = root / "data"
            data.mkdir()
            dep = data / "dependency.json"
            namecert = data / "namecert_sources.json"
            paper = data / "paper_sources.json"
            dep.write_text(json.dumps({"nodes": []}), encoding="utf-8")
            namecert.write_text(json.dumps([]), encoding="utf-8")
            paper.write_text(json.dumps([{"slug": "foo", "order": 1, "html_url": "paper/foo/"}]), encoding="utf-8")
            self.assertEqual(check_namecert_html.check(dep, namecert, paper, site_root=site, scope="paper"), [])
            paper.write_text(json.dumps([{"slug": "bad", "order": 1, "html_url": "../foo/"}]), encoding="utf-8")
            self.assertTrue(check_namecert_html.check(dep, namecert, paper, site_root=site, scope="paper"))

    def test_checker_full_scope_paper_requires_existing_page(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            site = root / "site"
            data = root / "data"
            data.mkdir()
            dep = data / "dependency.json"
            namecert = data / "namecert_sources.json"
            paper = data / "paper_sources.json"
            dep.write_text(json.dumps({"nodes": []}), encoding="utf-8")
            namecert.write_text(json.dumps([]), encoding="utf-8")
            paper.write_text(json.dumps([{"slug": "foo", "order": 1, "html_url": "paper/foo"}]), encoding="utf-8")
            errors = check_namecert_html.check(
                dep,
                namecert,
                paper,
                site_root=site,
                scope="paper",
                allow_partial=False,
                require_manifest_pages=True,
            )

        self.assertTrue(errors)
        self.assertTrue(any("missing" in err and "paper/foo" in err for err in errors))

    def test_rows_to_render_all_scope_skips_reused_namecert_url(self) -> None:
        namecert_rows = [{
            "scope": "namecert",
            "slug": "foo",
            "source": "papers/bedc/parts/concrete_instances/foo/namecert_construction.tex",
            "html_url": "namecert/foo/",
        }]
        paper_rows = [
            {
                "scope": "paper",
                "slug": "foo",
                "source": "papers/bedc/parts/concrete_instances/foo/namecert_construction.tex",
                "html_url": "namecert/foo/",
                "reused_namecert": True,
            },
            {
                "scope": "paper",
                "slug": "bar",
                "source": "papers/bedc/parts/bar.tex",
                "html_url": "paper/2-bar/",
                "reused_namecert": False,
            },
        ]

        rows = build_namecert_html.rows_to_render("all", namecert_rows, paper_rows)

        self.assertEqual([row["html_url"] for row in rows], ["namecert/foo/", "paper/2-bar/"])

    def test_limited_manifest_rows_keeps_selected_url_or_source(self) -> None:
        manifest_rows = [
            {"slug": "foo", "source": "a.tex", "html_url": "namecert/foo/"},
            {"slug": "bar", "source": "b.tex", "html_url": "paper/bar/"},
            {"slug": "baz", "source": "c.tex", "html_url": "paper/baz/"},
        ]
        selected = [
            {"slug": "url-match", "source": "other.tex", "html_url": "namecert/foo/"},
            {"slug": "source-match", "source": "b.tex", "html_url": "paper/other/"},
        ]

        rows = build_namecert_html.limited_manifest_rows(manifest_rows, selected)

        self.assertEqual([row["slug"] for row in rows], ["foo", "bar"])


if __name__ == "__main__":
    unittest.main()
