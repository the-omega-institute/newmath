#!/usr/bin/env python3
"""Build static HTML pages for concrete-instance NameCert chapters.

NameCert chapters are generated from BEDC paper sources but consumed from the
dossier DAG as standalone HTML pages. This module discovers chapter labels,
renders each source through make4ht, and writes stable `namecert/<slug>/`
paths that Quarto can copy into the published site.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PAPER_DIR = ROOT / "papers" / "bedc"
PARTS_DIR = PAPER_DIR / "parts" / "concrete_instances"
OUT_ROOT = ROOT / "docs" / "dossier" / "namecert"
DEFAULT_MANIFEST = ROOT / "docs" / "dossier" / "data" / "namecert_sources.json"
DEFAULT_DEPENDENCY = ROOT / "docs" / "dossier" / "data" / "dependency.json"
LABEL_RE = re.compile(r"\\label\{ch:concrete-instances-([a-z0-9-]+)-namecert\}")
PUBLISH_SUFFIXES = {".html", ".css", ".png", ".svg", ".jpg", ".jpeg", ".gif", ".webp"}
PAGE_CSS = """
<style>
:root { color-scheme: light; }
body { margin: 0 auto; max-width: 920px; padding: 2rem 1.2rem 4rem; color: #202124; background: #fbfbfa; font: 16px/1.58 system-ui, -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif; }
h1, h2, h3, h4 { line-height: 1.22; color: #171717; }
a { color: #245c8a; }
.dossier-nav { display: flex; justify-content: space-between; gap: .7rem; margin: 0 0 1.4rem; padding-bottom: .8rem; border-bottom: 1px solid #ddd; flex-wrap: wrap; }
.dossier-nav a { text-decoration: none; border: 1px solid #c9d3dc; border-radius: 4px; padding: .25rem .55rem; background: #fff; }
.lean-badge { display: block; margin: .45rem 0; font: 13px/1.35 ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; }
.lean-badge span { display: inline-block; border-radius: 3px; padding: .12rem .42rem; margin-right: .35rem; font-family: system-ui, sans-serif; font-weight: 650; }
.lean-checked span { background: #e9f7ef; color: #1e7c43; }
.lean-variant span { background: #f1f3f4; color: #5f6368; }
.lean-stmt span { background: #eaf3fb; color: #1f5d8a; }
.lean-def span { background: #f5f5f5; color: #555; }
.lean-sorry span { background: #fff4df; color: #9a5b00; }
.closure-status { margin: 1.2rem 0; padding: .85rem 1rem; border: 1px solid #d6dde3; border-left: 4px solid #52616f; background: #fff; }
.closure-status p { margin: .35rem 0; }
.closure-status strong { color: #333; }
code, .texttt { overflow-wrap: anywhere; }
img, svg { max-width: 100%; height: auto; }
</style>
"""


def read_json(path: Path) -> object:
    return json.loads(path.read_text(encoding="utf-8"))


def normalize_region(slug: str) -> str:
    return slug.replace("-", "")


def scan_sources() -> list[dict]:
    rows: list[dict] = []
    seen: set[str] = set()
    for tex in sorted(PARTS_DIR.rglob("*.tex")):
        text = tex.read_text(encoding="utf-8", errors="ignore")
        m = LABEL_RE.search(text)
        if not m:
            continue
        slug = m.group(1)
        if slug in seen:
            continue
        seen.add(slug)
        rows.append({
            "slug": slug,
            "region": normalize_region(slug),
            "source": str(tex.relative_to(ROOT)),
            "html_url": f"namecert/{slug}/",
        })
    return rows


def load_manifest(path: Path) -> list[dict]:
    if path.exists():
        data = read_json(path)
        if not isinstance(data, list):
            raise SystemExit(f"manifest must be a JSON list: {path}")
        return [dict(row) for row in data]
    return scan_sources()


def dependency_edges(path: Path) -> tuple[dict[str, list[str]], dict[str, list[str]]]:
    if not path.exists():
        return {}, {}
    data = read_json(path)
    nodes = {n.get("id") for n in data.get("nodes", []) if isinstance(n, dict)}
    up: dict[str, list[str]] = {n: [] for n in nodes if n}
    down: dict[str, list[str]] = {n: [] for n in nodes if n}
    for edge in data.get("edges", []):
        if not isinstance(edge, dict):
            continue
        source = edge.get("source")
        target = edge.get("target")
        if source in nodes and target in nodes:
            up.setdefault(target, []).append(source)
            down.setdefault(source, []).append(target)
    return (
        {k: sorted(set(v)) for k, v in up.items()},
        {k: sorted(set(v)) for k, v in down.items()},
    )


def by_region(rows: list[dict]) -> dict[str, dict]:
    return {str(r.get("region") or normalize_region(str(r["slug"]))): r for r in rows}


def nav_html(row: dict, rows_by_region: dict[str, dict], up: list[str], down: list[str]) -> str:
    def link(region: str) -> str:
        target = rows_by_region.get(region)
        if not target:
            return ""
        slug = target["slug"]
        return f'<a href="../{slug}/">{slug}</a>'

    up_links = " ".join(x for x in (link(r) for r in up[:12]) if x)
    down_links = " ".join(x for x in (link(r) for r in down[:12]) if x)
    home = '<a href="../../visualization.html">Project map</a>'
    parts = [home]
    if up_links:
        parts.append(f'<span>Depends on: {up_links}</span>')
    if down_links:
        parts.append(f'<span>Used by: {down_links}</span>')
    return '<nav class="dossier-nav">' + " ".join(parts) + "</nav>"


def write_wrapper(tmpdir: Path, row: dict, nav: str) -> Path:
    source = row["source"]
    wrapper = tmpdir / "namecert-wrapper.tex"
    wrapper.write_text(
        "\\documentclass[11pt,oneside,openany]{book}\n"
        "\\input{preamble.tex}\n"
        "\\providecommand{\\dossierNavHtml}{}\n"
        "\\renewcommand{\\dossierNavHtml}{" + nav.replace("\\", "\\textbackslash{}").replace("%", "\\%") + "}\n"
        "\\makeatletter\n"
        "\\renewcommand{\\leanchecked}[1]{\\par\\noindent\\HtmlParOff\\HCode{<div class=\"lean-badge lean-checked\"><span>Lean4 checked</span><code>}\\detokenize{#1}\\HCode{</code></div>}\\HtmlParOn\\par}\n"
        "\\renewcommand{\\leanvariant}[1]{\\par\\noindent\\HtmlParOff\\HCode{<div class=\"lean-badge lean-variant\"><span>variant</span><code>}\\detokenize{#1}\\HCode{</code></div>}\\HtmlParOn\\par}\n"
        "\\renewcommand{\\leanstmt}[1]{\\par\\noindent\\HtmlParOff\\HCode{<div class=\"lean-badge lean-stmt\"><span>statement</span><code>}\\detokenize{#1}\\HCode{</code></div>}\\HtmlParOn\\par}\n"
        "\\renewcommand{\\leandef}[1]{\\par\\noindent\\HtmlParOff\\HCode{<div class=\"lean-badge lean-def\"><span>definition</span><code>}\\detokenize{#1}\\HCode{</code></div>}\\HtmlParOn\\par}\n"
        "\\renewcommand{\\leansorryd}[2]{\\par\\noindent\\HtmlParOff\\HCode{<div class=\"lean-badge lean-sorry\"><span>sorry</span><code>}\\detokenize{#1}\\HCode{</code> #2</div>}\\HtmlParOn\\par}\n"
        "\\makeatother\n"
        "\\begin{document}\n"
        f"\\input{{{source}}}\n"
        "\\end{document}\n",
        encoding="utf-8",
    )
    return wrapper


def polish_html(path: Path) -> None:
    html = path.read_text(encoding="utf-8", errors="ignore")
    if "<meta name=\"viewport\"" not in html:
        html = html.replace("<head>", "<head>\n<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\" />", 1)
    if "lean-badge" in html and PAGE_CSS.strip() not in html:
        html = html.replace("</head>", PAGE_CSS + "\n</head>", 1)
    path.write_text(html, encoding="utf-8")


def make4ht_supports_build_dir() -> bool:
    proc = subprocess.run(["make4ht", "--help"], text=True, capture_output=True)
    help_text = f"{proc.stdout}\n{proc.stderr}"
    return "--build-dir" in help_text or "-B,--build-dir" in help_text


def run_make4ht(
    row: dict,
    rows_by_region: dict[str, dict],
    upstream: dict[str, list[str]],
    downstream: dict[str, list[str]],
    mode: str,
    strict: bool,
    use_build_dir: bool,
) -> dict:
    slug = row["slug"]
    region = row.get("region") or normalize_region(slug)
    source_path = ROOT / row["source"]
    if not source_path.exists():
        return {"slug": slug, "ok": False, "error": f"missing source {source_path}"}

    out_dir = OUT_ROOT / slug
    if out_dir.exists():
        shutil.rmtree(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    nav = nav_html(row, rows_by_region, upstream.get(region, []), downstream.get(region, []))
    with tempfile.TemporaryDirectory(prefix=f"namecert-{slug}-") as td:
        tmpdir = Path(td)
        wrapper = write_wrapper(tmpdir, row, nav)
        build_dir = tmpdir / "build"
        build_dir.mkdir()
        cfg = PAPER_DIR / "make4ht-dossier.cfg"
        if mode == "mathjax":
            cfg = tmpdir / "make4ht-dossier-mathjax.cfg"
            cfg.write_text(
                (PAPER_DIR / "make4ht-dossier.cfg").read_text(encoding="utf-8").replace(
                    "\\Preamble{xhtml,mathml}",
                    "\\Preamble{xhtml,mathjax}",
                ),
                encoding="utf-8",
            )
        cmd = [
            "make4ht",
            "-a", "warning",
            "-c", str(cfg),
            "-d", str(out_dir),
            "-j", "index",
        ]
        if use_build_dir:
            cmd.extend(["-B", str(build_dir)])
        if mode and mode != "mathjax":
            cmd.extend(["-m", mode])
        cmd.append(wrapper.name)
        env = os.environ.copy()
        env["TEXINPUTS"] = f"{PAPER_DIR}{os.pathsep}{ROOT}{os.pathsep}{env.get('TEXINPUTS', '')}"
        proc = subprocess.run(cmd, cwd=tmpdir, env=env, text=True, capture_output=True)
        if use_build_dir and (build_dir / "index.html").exists():
            for item in build_dir.iterdir():
                if item.is_file() and item.suffix.lower() not in PUBLISH_SUFFIXES:
                    continue
                dest = out_dir / item.name
                if item.is_dir():
                    shutil.copytree(item, dest, dirs_exist_ok=True)
                else:
                    shutil.copy2(item, dest)
        debug_files = list(out_dir.rglob("*"))[:20]
    index = out_dir / "index.html"
    ok = proc.returncode == 0 and index.exists()
    if ok:
        polish_html(index)
        html = index.read_text(encoding="utf-8", errors="ignore")
        has_badge = "lean-badge" in html
        has_math = ("<math" in html) or ("MathJax" in html) or ("mjx-" in html)
        if strict and not has_badge:
            ok = False
            err = "HTML lacks lean badge markup"
        elif strict and not has_math:
            ok = False
            err = "HTML lacks MathML/MathJax output"
        else:
            err = ""
    else:
        err = (proc.stderr or proc.stdout)[-4000:]
        if not err:
            err = f"make4ht returned {proc.returncode}; files: {[str(p.relative_to(out_dir)) for p in debug_files]}"
    return {"slug": slug, "ok": ok, "error": err, "returncode": proc.returncode}


def write_manifest(path: Path, rows: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(rows, indent=2, ensure_ascii=False), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--dependency", type=Path, default=DEFAULT_DEPENDENCY)
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--limit", type=int, default=0)
    parser.add_argument("--strict", action="store_true")
    parser.add_argument("-m", "--mode", default="", help="make4ht mode, e.g. mathjax")
    parser.add_argument("--write-manifest-only", action="store_true")
    args = parser.parse_args()

    rows = load_manifest(args.manifest)
    write_manifest(args.manifest, rows)
    if args.write_manifest_only:
        print(f"[namecert-html] wrote manifest {args.manifest} ({len(rows)} sources)")
        return 0

    selected = rows[: args.limit] if args.limit and args.limit > 0 else rows
    if not selected:
        print("[namecert-html] no sources selected")
        return 0
    if shutil.which("make4ht") is None:
        print("[namecert-html] make4ht not found", file=sys.stderr)
        return 1
    use_build_dir = make4ht_supports_build_dir()
    if not use_build_dir:
        print("[namecert-html] make4ht lacks --build-dir; using temporary cwd with output-dir only")

    upstream, downstream = dependency_edges(args.dependency)
    rows_by_region = by_region(rows)
    OUT_ROOT.mkdir(parents=True, exist_ok=True)
    workers = max(1, args.jobs)
    failures: list[dict] = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
        futs = [
            pool.submit(
                run_make4ht,
                row,
                rows_by_region,
                upstream,
                downstream,
                args.mode,
                args.strict,
                use_build_dir,
            )
            for row in selected
        ]
        for fut in concurrent.futures.as_completed(futs):
            result = fut.result()
            status = "ok" if result["ok"] else "FAIL"
            print(f"[namecert-html] {status} {result['slug']}")
            if not result["ok"]:
                failures.append(result)

    if failures:
        for fail in failures:
            print(f"[namecert-html] {fail['slug']}: {fail['error']}", file=sys.stderr)
        return 1
    print(f"[namecert-html] built {len(selected)} page(s)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
