#!/usr/bin/env python3
"""Build paginated HTML pages for BEDC dossier sources.

The builder renders NameCert chapters, full-paper chapters, or both according
to ``--scope namecert|paper|all`` and writes the matching manifest rows.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
PAPER_DIR = ROOT / "papers" / "bedc"
PARTS_DIR = PAPER_DIR / "parts" / "concrete_instances"
MAIN_TEX = PAPER_DIR / "main.tex"
NAMECERT_OUT_ROOT = ROOT / "docs" / "dossier" / "namecert"
PAPER_OUT_ROOT = ROOT / "docs" / "dossier" / "paper"
DEFAULT_NAMECERT_MANIFEST = ROOT / "docs" / "dossier" / "data" / "namecert_sources.json"
DEFAULT_PAPER_MANIFEST = ROOT / "docs" / "dossier" / "data" / "paper_sources.json"
DEFAULT_DEPENDENCY = ROOT / "docs" / "dossier" / "data" / "dependency.json"
SCOPES = {"namecert", "paper", "all"}

OUT_ROOT = NAMECERT_OUT_ROOT
DEFAULT_MANIFEST = DEFAULT_NAMECERT_MANIFEST

LABEL_RE = re.compile(r"\\label\{ch:concrete-instances-([a-z0-9-]+)-namecert\}")
INPUT_RE = re.compile(r"\\(?:input|include)\{([^}]+)\}")
STRUCTURE_RE = re.compile(r"\\(part|chapter|input|include)\{([^{}]+)\}")
MACRO_LINE_RE = re.compile(
    r"^\s*\\(?:(?:re)?newcommand|providecommand)\*?\s*(?:\{\\[A-Za-z@]+\}|\\[A-Za-z@]+)"
    r"(?:\s*\[[^\]]+\]){0,2}\s*\{.*\}\s*$"
)
DEF_LINE_RE = re.compile(r"^\s*\\def\\[A-Za-z@]+(?:#[1-9])*\s*\{.*\}\s*$")
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


def text_without_comments(text: str) -> str:
    lines = []
    for line in text.splitlines():
        pos = line.find("%")
        if pos >= 0:
            line = line[:pos]
        lines.append(line)
    return "\n".join(lines)


def title_slug(text: str) -> str:
    words = re.findall(r"[A-Za-z0-9]+", text.lower())
    return "-".join(words[:10]) or "source"


def source_slug(path: Path) -> str:
    stem = path.stem
    stem = re.sub(r"^\d+_", "", stem)
    stem = re.sub(r"_namecert_construction(?:_core)?$", "", stem)
    return title_slug(stem.replace("_", " "))


def human_title(path: Path) -> str:
    stem = re.sub(r"^\d+_", "", path.stem)
    stem = re.sub(r"_namecert_construction(?:_core)?$", "", stem)
    return " ".join(part.capitalize() for part in re.findall(r"[A-Za-z0-9]+", stem)) or path.stem


def tex_title(path: Path, fallback: str = "") -> str:
    if path.exists():
        text = text_without_comments(path.read_text(encoding="utf-8", errors="ignore"))
        match = re.search(r"\\chapter\{([^{}]+)\}", text)
        if match:
            return match.group(1).strip()
        match = re.search(r"\\section\{([^{}]+)\}", text)
        if match:
            return match.group(1).strip()
    return fallback or human_title(path)


def relative_source(path: Path) -> str:
    resolved = path.resolve()
    root = ROOT.resolve()
    if resolved.is_relative_to(root):
        return str(resolved.relative_to(root))
    return str(resolved)


def scan_namecert_sources() -> list[dict]:
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
            "scope": "namecert",
            "kind": "namecert",
            "slug": slug,
            "region": normalize_region(slug),
            "source": str(tex.relative_to(ROOT)),
            "html_url": f"namecert/{slug}/",
        })
    return rows


def scan_sources() -> list[dict]:
    return scan_namecert_sources()


def load_namecert_manifest(path: Path) -> list[dict]:
    if path.exists():
        data = read_json(path)
        if not isinstance(data, list):
            raise SystemExit(f"manifest must be a JSON list: {path}")
        rows = [dict(row) for row in data]
    else:
        rows = scan_namecert_sources()
    for row in rows:
        row.setdefault("scope", "namecert")
        row.setdefault("kind", "namecert")
        if row.get("slug") and not row.get("region"):
            row["region"] = normalize_region(str(row["slug"]))
        if row.get("slug") and not row.get("html_url"):
            row["html_url"] = f"namecert/{row['slug']}/"
    return rows


def namecert_indexes(rows: list[dict]) -> tuple[dict[str, dict], dict[str, dict]]:
    by_source: dict[str, dict] = {}
    by_slug: dict[str, dict] = {}
    for row in rows:
        if row.get("source"):
            by_source[str(row["source"])] = row
        if row.get("slug"):
            by_slug[str(row["slug"])] = row
    return by_source, by_slug


def resolve_tex_input(name: str, base_dir: Path) -> Path | None:
    raw = name.strip()
    if not raw:
        return None
    raw_path = Path(raw)
    names = [raw_path] if raw_path.suffix else [raw_path, Path(f"{raw}.tex")]
    candidates: list[Path] = []
    for item in names:
        if item.is_absolute():
            candidates.append(item)
        else:
            candidates.extend([base_dir / item, PAPER_DIR / item, ROOT / item])
    for candidate in candidates:
        if candidate.is_file():
            return candidate.resolve()
    return (PAPER_DIR / names[-1]).resolve()


def detect_namecert_row(path: Path, text: str, by_source: dict[str, dict], by_slug: dict[str, dict]) -> dict | None:
    rel = relative_source(path)
    if rel in by_source:
        return by_source[rel]
    label = LABEL_RE.search(text)
    if label and label.group(1) in by_slug:
        return by_slug[label.group(1)]
    for match in INPUT_RE.finditer(text_without_comments(text)):
        child = resolve_tex_input(match.group(1), path.parent)
        if not child or not child.exists():
            continue
        child_rel = relative_source(child)
        if child_rel in by_source:
            return by_source[child_rel]
        child_text = child.read_text(encoding="utf-8", errors="ignore")
        child_label = LABEL_RE.search(child_text)
        if child_label and child_label.group(1) in by_slug:
            return by_slug[child_label.group(1)]
    file_match = re.match(r"^\d+_(.+)_namecert_construction(?:_core)?$", path.stem)
    if file_match:
        candidate = file_match.group(1).replace("_", "-")
        if candidate in by_slug:
            return by_slug[candidate]
    return None


def _paper_tex_body(path: Path, main_tex: Path) -> str:
    text = text_without_comments(path.read_text(encoding="utf-8", errors="ignore"))
    if path.resolve() == main_tex.resolve() and "\\begin{document}" in text:
        return text.split("\\begin{document}", 1)[1]
    return text


def _walk_main_inputs(path: Path, main_tex: Path, part: str = "", chapter: str = "") -> list[tuple[Path, str, str]]:
    if not path.exists() or path.suffix.lower() != ".tex":
        return []
    rows: list[tuple[Path, str, str]] = []
    cursor_part = part
    cursor_chapter = chapter
    for match in STRUCTURE_RE.finditer(_paper_tex_body(path, main_tex)):
        command, value = match.group(1), match.group(2).strip()
        if command == "part":
            cursor_part = value
        elif command == "chapter":
            cursor_chapter = value
        elif command in {"input", "include"}:
            child = resolve_tex_input(value, path.parent)
            if child is None or not child.exists():
                continue
            rows.append((child, cursor_part, cursor_chapter))
            rows.extend(_walk_main_inputs(child, main_tex, cursor_part, cursor_chapter))
    return rows


def _build_paper_row(
    path: Path,
    order: int,
    part: str,
    chapter: str,
    by_source: dict[str, dict],
    by_slug: dict[str, dict],
) -> dict:
    text = path.read_text(encoding="utf-8", errors="ignore")
    nc_row = detect_namecert_row(path, text, by_source, by_slug)
    title = tex_title(path, chapter or human_title(path))
    if nc_row:
        slug = str(nc_row["slug"])
        html_url = str(nc_row.get("html_url") or f"namecert/{slug}/")
        region = str(nc_row.get("region") or normalize_region(slug))
        kind = "namecert"
        reused = True
    else:
        slug = source_slug(path)
        html_url = f"paper/{order}-{slug}/"
        region = normalize_region(slug)
        kind = "tex"
        reused = False
    return {
        "scope": "paper",
        "kind": kind,
        "order": order,
        "part": part,
        "chapter": title if re.search(r"\\chapter\{", text_without_comments(text)) else chapter,
        "slug": slug,
        "title": title,
        "source": relative_source(path),
        "region": region,
        "html_url": html_url,
        "reused_namecert": reused,
    }


def scan_paper_sources(main_tex: Path = MAIN_TEX, namecert_rows: list[dict] | None = None) -> list[dict]:
    """Walk the paper input tree and return manifest rows in document order."""
    if namecert_rows is None:
        namecert_rows = scan_namecert_sources()
    by_source, by_slug = namecert_indexes(namecert_rows)
    rows: list[dict] = []
    seen_sources: set[Path] = set()
    order = 0
    for path, part, chapter in _walk_main_inputs(main_tex.resolve(), main_tex.resolve()):
        resolved = path.resolve()
        if resolved in seen_sources or not resolved.exists() or resolved.suffix.lower() != ".tex":
            continue
        seen_sources.add(resolved)
        order += 1
        rows.append(_build_paper_row(resolved, order, part, chapter, by_source, by_slug))
    return rows


def load_paper_manifest(path: Path, main_tex: Path, namecert_rows: list[dict]) -> list[dict]:
    rows = scan_paper_sources(main_tex, namecert_rows)
    for row in rows:
        row.setdefault("scope", "paper")
        row.setdefault("kind", "tex")
        row.setdefault("reused_namecert", str(row.get("html_url", "")).startswith("namecert/"))
    return rows


def load_rows_for_scope(scope: str, manifest: Path, paper_manifest: Path) -> tuple[list[dict], list[dict]]:
    """Load the NameCert and paper row sets requested by the command scope."""
    if scope not in SCOPES:
        raise SystemExit(f"unknown scope: {scope}")
    namecert_rows = load_namecert_manifest(manifest)
    if scope == "namecert":
        return namecert_rows, []
    paper_rows = load_paper_manifest(paper_manifest, MAIN_TEX, namecert_rows)
    if scope == "paper":
        return [], paper_rows
    return namecert_rows, paper_rows


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

    scope = row.get("scope", "namecert")
    if scope == "paper":
        home = '<a href="../../paper.html">Full paper</a>'
    else:
        home = '<a href="../../visualization.html">Project map</a>'
    parts = [home]
    if scope != "paper":
        up_links = " ".join(x for x in (link(r) for r in up[:12]) if x)
        down_links = " ".join(x for x in (link(r) for r in down[:12]) if x)
        if up_links:
            parts.append(f'<span>Depends on: {up_links}</span>')
        if down_links:
            parts.append(f'<span>Used by: {down_links}</span>')
    return '<nav class="dossier-nav">' + " ".join(parts) + "</nav>"


def update_hash_file(h: Any, label: str, path: Path) -> None:
    h.update(f"file:{label}\n".encode("utf-8"))
    rel = str(path.relative_to(ROOT)) if path.is_relative_to(ROOT) else str(path)
    h.update(rel.encode("utf-8"))
    h.update(b"\n")
    if path.exists():
        h.update(path.read_bytes())
    else:
        h.update(b"<missing>")
    h.update(b"\n")


def collect_tex_inputs(source_path: Path) -> list[Path]:
    pending = [source_path.resolve()]
    seen: set[Path] = set()
    ordered: list[Path] = []
    while pending:
        path = pending.pop()
        if path in seen:
            continue
        seen.add(path)
        ordered.append(path)
        if not path.exists() or path.suffix.lower() != ".tex":
            continue
        text = text_without_comments(path.read_text(encoding="utf-8", errors="ignore"))
        for match in INPUT_RE.finditer(text):
            resolved = resolve_tex_input(match.group(1), path.parent)
            if resolved is not None and resolved not in seen:
                pending.append(resolved)
    return sorted(ordered, key=lambda p: str(p))


def guard_macro_declaration(text: str) -> str:
    """Convert replayable macro declarations to non-conflicting declarations."""
    stripped = text.strip()
    if re.match(r"^\\newcommand\*?", stripped):
        return re.sub(r"^\\newcommand", r"\\providecommand", stripped, count=1)
    return stripped


def extract_macro_declarations(path: Path) -> list[str]:
    """Read simple top-level TeX macro declarations from one source file."""
    if not path.exists() or path.suffix.lower() != ".tex":
        return []
    declarations: list[str] = []
    for line in path.read_text(encoding="utf-8", errors="ignore").splitlines():
        stripped = line.strip()
        if not stripped or stripped.startswith("%"):
            continue
        clean = stripped.split("%", 1)[0].rstrip()
        if MACRO_LINE_RE.match(clean) or DEF_LINE_RE.match(clean):
            declarations.append(guard_macro_declaration(clean))
    return declarations


def collect_macro_prelude(rows: list[dict]) -> str:
    """Collect macro declarations needed by standalone chapter wrappers."""
    seen: set[str] = set()
    declarations: list[str] = []
    source_paths = [ROOT / str(row["source"]) for row in rows if row.get("source")]
    for source in source_paths:
        for path in collect_tex_inputs(source):
            for declaration in extract_macro_declarations(path):
                if declaration not in seen:
                    seen.add(declaration)
                    declarations.append(declaration)
    if not declarations:
        return ""
    return "\n".join(declarations) + "\n"


def stamp_name(row: dict) -> str:
    return f".{row.get('scope', 'namecert')}-stamp"


def output_root_for_row(row: dict) -> Path:
    html_url = str(row.get("html_url", ""))
    if not html_url or html_url.startswith("/") or "\\" in html_url:
        raise ValueError(f"unsafe html_url: {html_url!r}")
    parts = [part for part in html_url.split("/") if part]
    if any(part in {"..", "."} for part in parts):
        raise ValueError(f"unsafe html_url: {html_url!r}")
    return ROOT / "docs" / "dossier" / Path(*parts)


def region_fingerprint(
    row: dict,
    rows_by_region: dict[str, dict],
    upstream: dict[str, list[str]],
    downstream: dict[str, list[str]],
    mode: str,
    strict: bool,
    nav: str,
    source_path: Path,
    macro_prelude: str,
) -> str:
    region = row.get("region") or normalize_region(str(row["slug"]))
    up = upstream.get(str(region), [])
    down = downstream.get(str(region), [])
    payload = {
        "version": 2,
        "row": row,
        "scope": row.get("scope", "namecert"),
        "html_url": row.get("html_url"),
        "output_prefix": str(output_root_for_row(row).relative_to(ROOT)),
        "mode": mode,
        "strict": strict,
        "upstream": up,
        "downstream": down,
        "nav": nav,
        "macro_prelude_sha256": hashlib.sha256(macro_prelude.encode("utf-8")).hexdigest(),
        "neighbor_slugs": {
            r: rows_by_region[r]["slug"]
            for r in sorted(set(up + down))
            if r in rows_by_region and "slug" in rows_by_region[r]
        },
    }
    h = hashlib.sha256()
    h.update(json.dumps(payload, sort_keys=True, ensure_ascii=False).encode("utf-8"))
    h.update(b"\n")
    update_hash_file(h, "source", source_path)
    for input_path in collect_tex_inputs(source_path):
        if input_path != source_path.resolve():
            update_hash_file(h, "tex-input", input_path)
    for input_path in collect_tex_inputs(PAPER_DIR / "preamble.tex"):
        update_hash_file(h, "preamble-input", input_path)
    update_hash_file(h, "make4ht-dossier.cfg", PAPER_DIR / "make4ht-dossier.cfg")
    update_hash_file(h, "build_namecert_html.py", Path(__file__).resolve())
    return h.hexdigest()


def tex_string_literal(text: str) -> str:
    return text.replace("\\", "\\textbackslash{}").replace("%", "\\%")


def write_wrapper(tmpdir: Path, row: dict, nav: str, macro_prelude: str) -> Path:
    source = row["source"]
    wrapper = tmpdir / "namecert-wrapper.tex"
    prelude = ""
    if macro_prelude.strip():
        prelude = "\\makeatletter\n" + macro_prelude + "\\makeatother\n"
    wrapper.write_text(
        "\\documentclass[11pt,oneside,openany]{book}\n"
        "\\input{preamble.tex}\n"
        + prelude +
        "\\providecommand{\\dossierNavHtml}{}\n"
        "\\renewcommand{\\dossierNavHtml}{" + tex_string_literal(nav) + "}\n"
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
    if '<meta name="viewport"' not in html:
        html = html.replace("<head>", '<head>\n<meta name="viewport" content="width=device-width, initial-scale=1" />', 1)
    if PAGE_CSS.strip() not in html:
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
    force: bool,
    macro_prelude: str,
) -> dict:
    slug = row["slug"]
    region = row.get("region") or normalize_region(slug)
    source_path = ROOT / row["source"]
    if not source_path.exists():
        return {"slug": slug, "ok": False, "error": f"missing source {source_path}"}

    nav = nav_html(row, rows_by_region, upstream.get(str(region), []), downstream.get(str(region), []))
    try:
        out_dir = output_root_for_row(row)
    except ValueError as exc:
        return {"slug": slug, "ok": False, "error": str(exc)}
    fingerprint = region_fingerprint(
        row,
        rows_by_region,
        upstream,
        downstream,
        mode,
        strict,
        nav,
        source_path,
        macro_prelude,
    )
    stamp = out_dir / stamp_name(row)
    index = out_dir / "index.html"
    if not force and index.exists() and stamp.exists():
        cached = stamp.read_text(encoding="utf-8", errors="ignore").strip()
        if cached == fingerprint:
            return {"slug": slug, "ok": True, "cached": True, "error": "", "returncode": 0}

    if out_dir.exists():
        shutil.rmtree(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    proc: subprocess.CompletedProcess[str] | None = None
    debug_files: list[Path] = []
    with tempfile.TemporaryDirectory(prefix=f"{row.get('scope', 'namecert')}-{slug}-") as td:
        tmpdir = Path(td)
        wrapper = write_wrapper(tmpdir, row, nav, macro_prelude)
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
    ok = proc.returncode == 0 and index.exists()
    if ok:
        polish_html(index)
        html = index.read_text(encoding="utf-8", errors="ignore")
        has_badge = "lean-badge" in html
        has_math = ("<math" in html) or ("MathJax" in html) or ("mjx-" in html)
        if strict and row.get("scope", "namecert") == "namecert":
            if not has_badge:
                ok = False
                err = "HTML lacks lean badge markup"
            elif not has_math:
                ok = False
                err = "HTML lacks MathML/MathJax output"
            else:
                err = ""
                stamp.write_text(f"{fingerprint}\n", encoding="utf-8")
        else:
            err = ""
            stamp.write_text(f"{fingerprint}\n", encoding="utf-8")
    else:
        err = (proc.stderr or proc.stdout)[-4000:] if proc else ""
        if not err:
            err = f"make4ht returned {proc.returncode if proc else 'none'}; files: {[str(p.relative_to(out_dir)) for p in debug_files]}"
    return {
        "slug": slug,
        "scope": row.get("scope", "namecert"),
        "html_url": row.get("html_url"),
        "ok": ok,
        "cached": False,
        "error": err,
        "returncode": proc.returncode if proc else 1,
    }


def write_manifest(path: Path, rows: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(rows, indent=2, ensure_ascii=False), encoding="utf-8")


def unique_by_html_url(rows: list[dict]) -> list[dict]:
    selected: list[dict] = []
    seen: set[str] = set()
    for row in rows:
        url = str(row.get("html_url", ""))
        key = url or str(row.get("source", ""))
        if key in seen:
            continue
        seen.add(key)
        selected.append(row)
    return selected


def rows_to_render(scope: str, namecert_rows: list[dict], paper_rows: list[dict]) -> list[dict]:
    """Return unique render rows for a scope, keyed by published URL."""
    if scope == "namecert":
        return unique_by_html_url(namecert_rows)
    if scope == "paper":
        return unique_by_html_url(paper_rows)
    namecert_urls = {str(row.get("html_url")) for row in namecert_rows}
    paper_unique = [row for row in unique_by_html_url(paper_rows) if str(row.get("html_url")) not in namecert_urls]
    return unique_by_html_url(namecert_rows + paper_unique)


def limited_manifest_rows(rows: list[dict], selected: list[dict]) -> list[dict]:
    """Keep manifest rows selected by source path or published URL."""
    selected_sources = {str(row.get("source")) for row in selected}
    selected_urls = {str(row.get("html_url")) for row in selected}
    return [row for row in rows if str(row.get("source")) in selected_sources or str(row.get("html_url")) in selected_urls]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--scope", choices=sorted(SCOPES), default="namecert")
    parser.add_argument("--manifest", type=Path, default=DEFAULT_NAMECERT_MANIFEST)
    parser.add_argument("--paper-manifest", type=Path, default=DEFAULT_PAPER_MANIFEST)
    parser.add_argument("--dependency", type=Path, default=DEFAULT_DEPENDENCY)
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--limit", type=int, default=0)
    parser.add_argument(
        "--write-selected-manifest",
        action="store_true",
        help="when --limit is used, write only selected rows to the matching manifest",
    )
    parser.add_argument("--strict", action="store_true")
    parser.add_argument(
        "--allow-failures",
        action="store_true",
        help="report failed pages but exit successfully after building the rest",
    )
    parser.add_argument("-m", "--mode", default="", help="make4ht mode, e.g. mathjax")
    parser.add_argument("--force", action="store_true", help="ignore per-page stamps and rebuild selected pages")
    parser.add_argument("--write-manifest-only", action="store_true")
    return parser.parse_args()


def _select_rows(args: argparse.Namespace, namecert_rows: list[dict], paper_rows: list[dict]) -> list[dict]:
    render_rows = rows_to_render(args.scope, namecert_rows, paper_rows)
    if args.limit and args.limit > 0:
        if args.scope == "all":
            return rows_to_render(
                args.scope,
                namecert_rows[: args.limit],
                paper_rows[: args.limit],
            )
        return render_rows[: args.limit]
    return render_rows


def _write_selected_manifests(
    args: argparse.Namespace,
    namecert_rows: list[dict],
    paper_rows: list[dict],
    selected: list[dict],
) -> None:
    if args.scope in {"namecert", "all"}:
        rows = limited_manifest_rows(namecert_rows, selected) if args.write_selected_manifest else namecert_rows
        write_manifest(args.manifest, rows)
    if args.scope in {"paper", "all"}:
        rows = limited_manifest_rows(paper_rows, selected) if args.write_selected_manifest else paper_rows
        write_manifest(args.paper_manifest, rows)


def _prepare_render_context(
    args: argparse.Namespace,
    namecert_rows: list[dict],
    paper_rows: list[dict],
) -> tuple[dict[str, list[str]], dict[str, list[str]], dict[str, dict], str, bool] | int:
    if shutil.which("make4ht") is None:
        print("[namecert-html] make4ht not found", file=sys.stderr)
        return 1
    use_build_dir = make4ht_supports_build_dir()
    if not use_build_dir:
        print("[namecert-html] make4ht lacks --build-dir; using temporary cwd with output-dir only")

    upstream, downstream = dependency_edges(args.dependency)
    all_manifest_rows = namecert_rows + paper_rows
    rows_by_region = by_region(all_manifest_rows)
    NAMECERT_OUT_ROOT.mkdir(parents=True, exist_ok=True)
    PAPER_OUT_ROOT.mkdir(parents=True, exist_ok=True)
    macro_prelude = collect_macro_prelude(all_manifest_rows)
    return upstream, downstream, rows_by_region, macro_prelude, use_build_dir


def _render_selected_rows(
    args: argparse.Namespace,
    selected: list[dict],
    rows_by_region: dict[str, dict],
    upstream: dict[str, list[str]],
    downstream: dict[str, list[str]],
    use_build_dir: bool,
    macro_prelude: str,
) -> tuple[list[dict], int]:
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
                args.force,
                macro_prelude,
            )
            for row in selected
        ]
        cached_count = 0
        for fut in concurrent.futures.as_completed(futs):
            result = fut.result()
            label = f"{result.get('scope', args.scope)}:{result['slug']}"
            if result.get("cached"):
                cached_count += 1
                print(f"[namecert-html] cached {label}")
            else:
                status = "ok" if result["ok"] else "FAIL"
                print(f"[namecert-html] {status} {label}")
            if not result["ok"]:
                failures.append(result)

    return failures, cached_count


def _finish_render(args: argparse.Namespace, selected: list[dict], failures: list[dict], cached_count: int) -> int:
    if failures:
        for fail in failures:
            print(f"[namecert-html] {fail.get('scope', args.scope)}:{fail['slug']}: {fail['error']}", file=sys.stderr)
        if args.allow_failures:
            built_count = len(selected) - len(failures) - cached_count
            print(f"[namecert-html] built {built_count}/{len(selected)} page(s); cached {cached_count}; {len(failures)} failed")
            return 0
        return 1
    built_count = len(selected) - cached_count
    print(f"[namecert-html] built {built_count}/{len(selected)} page(s); cached {cached_count}")
    return 0


def main() -> int:
    args = parse_args()
    namecert_rows, paper_rows = load_rows_for_scope(args.scope, args.manifest, args.paper_manifest)
    selected = _select_rows(args, namecert_rows, paper_rows)
    _write_selected_manifests(args, namecert_rows, paper_rows, selected)
    if args.write_manifest_only:
        print(
            f"[namecert-html] wrote manifests: namecert={len(namecert_rows)} paper={len(paper_rows)} scope={args.scope}"
        )
        return 0
    if not selected:
        print("[namecert-html] no sources selected")
        return 0
    context = _prepare_render_context(args, namecert_rows, paper_rows)
    if isinstance(context, int):
        return context
    upstream, downstream, rows_by_region, macro_prelude, use_build_dir = context
    failures, cached_count = _render_selected_rows(
        args,
        selected,
        rows_by_region,
        upstream,
        downstream,
        use_build_dir,
        macro_prelude,
    )
    return _finish_render(args, selected, failures, cached_count)


if __name__ == "__main__":
    sys.exit(main())
