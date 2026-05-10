#!/usr/bin/env python3
"""Operator-side review CLI for AI-proposed BEDC chapters.

Phase 2 scaffolding only. The phase_propose codex trigger is not yet
wired into codex_revise.py; proposals land in `papers/bedc/proposals/`
either by hand or by manual `codex exec` invocation. This CLI lets the
operator review pending proposals and either promote them to seed-stub
chapters or archive them as rejections.

Usage:

    python3 lean4/scripts/review_proposals.py list
    python3 lean4/scripts/review_proposals.py show <sha>
    python3 lean4/scripts/review_proposals.py accept <sha>
    python3 lean4/scripts/review_proposals.py reject <sha> --reason "..."

Acceptance criteria are enforced lightly (slug uniqueness, dependency
count); deeper taste judgement remains operator responsibility.
"""

from __future__ import annotations

import argparse
import re
import shutil
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
PROPOSALS_DIR = REPO_ROOT / "papers" / "bedc" / "proposals"
ACCEPTED_DIR = PROPOSALS_DIR / "accepted"
REJECTED_DIR = PROPOSALS_DIR / "rejected"
CONCRETE_INSTANCES_DIR = REPO_ROOT / "papers" / "bedc" / "parts" / "concrete_instances"
PREAMBLE_PATH = REPO_ROOT / "papers" / "bedc" / "preamble.tex"
MAIN_TEX_PATH = REPO_ROOT / "papers" / "bedc" / "main.tex"

PROPOSAL_NAME_RE = re.compile(r"^([0-9a-f]{6,40})_([a-z][a-z0-9-]*)\.md$")


def _list_pending() -> list[Path]:
    if not PROPOSALS_DIR.exists():
        return []
    return sorted(
        p
        for p in PROPOSALS_DIR.glob("*.md")
        if p.name != "README.md" and PROPOSAL_NAME_RE.match(p.name)
    )


def _find_by_sha(sha: str) -> Path | None:
    for p in _list_pending():
        if p.name.startswith(sha):
            return p
    return None


def _existing_slugs() -> set[str]:
    """Return lowercase slugs of every existing concrete-instance chapter."""
    slugs: set[str] = set()
    if not CONCRETE_INSTANCES_DIR.exists():
        return slugs
    for tex in CONCRETE_INSTANCES_DIR.glob("*_namecert_construction.tex"):
        # filename: <NN>_<slug>_namecert_construction.tex
        parts = tex.stem.split("_")
        if len(parts) >= 3:
            slug = "_".join(parts[1:-2])  # strip leading <NN> and trailing _namecert_construction
            slugs.add(slug.lower())
    return slugs


def _next_chapter_index() -> int:
    max_idx = 0
    if not CONCRETE_INSTANCES_DIR.exists():
        return 1
    for tex in CONCRETE_INSTANCES_DIR.glob("*_namecert_construction.tex"):
        parts = tex.stem.split("_")
        try:
            idx = int(parts[0])
            if idx > max_idx:
                max_idx = idx
        except (ValueError, IndexError):
            pass
    return max_idx + 1


def _parse_proposal(path: Path) -> dict:
    """Extract slug, dependencies, chapter title from a proposal file."""
    text = path.read_text()
    info: dict[str, object] = {"path": path}
    m = PROPOSAL_NAME_RE.match(path.name)
    if m:
        info["sha"] = m.group(1)
        info["slug"] = m.group(2).replace("-", "")
    title_match = re.search(r"^# +([A-Z][A-Za-z0-9]+Up)", text, re.MULTILINE)
    info["title"] = title_match.group(1) if title_match else None
    deps_match = re.search(r"^proposed_dependencies:\s*(.+)$", text, re.MULTILINE)
    info["dependencies"] = (
        [d.strip() for d in deps_match.group(1).split(",")] if deps_match else []
    )
    info["body"] = text
    return info


def cmd_list(_args) -> int:
    pending = _list_pending()
    if not pending:
        print("No pending proposals.")
        return 0
    print(f"{len(pending)} pending proposal(s):")
    for p in pending:
        info = _parse_proposal(p)
        title = info.get("title") or "(no title)"
        deps = ", ".join(info.get("dependencies") or []) or "(no deps)"
        print(f"  {info.get('sha', '?')[:8]}  {title:25}  deps: {deps}")
    return 0


def cmd_show(args) -> int:
    p = _find_by_sha(args.sha)
    if p is None:
        print(f"No proposal matching sha {args.sha}", file=sys.stderr)
        return 1
    print(p.read_text())
    return 0


def _validate(info: dict) -> list[str]:
    issues: list[str] = []
    title = info.get("title")
    if not title:
        issues.append("missing chapter title (expected `# <X>Up` heading)")
    else:
        slug_lower = info.get("slug", "").lower()
        existing = _existing_slugs()
        if slug_lower in existing:
            issues.append(f"slug '{slug_lower}' collides with existing chapter")
    deps = info.get("dependencies") or []
    if len(deps) < 3:
        issues.append(f"only {len(deps)} dependencies cited; need >= 3")
    return issues


def cmd_accept(args) -> int:
    p = _find_by_sha(args.sha)
    if p is None:
        print(f"No proposal matching sha {args.sha}", file=sys.stderr)
        return 1
    info = _parse_proposal(p)
    issues = _validate(info)
    if issues and not args.force:
        print("Validation issues (use --force to override):", file=sys.stderr)
        for s in issues:
            print(f"  - {s}", file=sys.stderr)
        return 1

    title = info["title"]
    slug = info.get("slug")
    next_idx = _next_chapter_index()
    chapter_path = CONCRETE_INSTANCES_DIR / f"{next_idx}_{slug}_namecert_construction.tex"
    if chapter_path.exists():
        print(f"Refusing to overwrite {chapter_path}", file=sys.stderr)
        return 1

    chapter_path.write_text(_seed_stub(title, slug, info))

    # Move proposal to accepted/.
    ACCEPTED_DIR.mkdir(parents=True, exist_ok=True)
    shutil.move(str(p), str(ACCEPTED_DIR / p.name))

    print(f"Accepted: {title}")
    print(f"  chapter: {chapter_path.relative_to(REPO_ROOT)}")
    print(f"  next steps:")
    print(f"    1. add `\\newcommand{{\\{title}}}{{\\mathsf{{{title.removesuffix('Up')}}}^{{\\uparrow}}}}` to preamble.tex")
    print(f"    2. add `\\input{{parts/concrete_instances/{chapter_path.name}}}` to main.tex")
    print(f"    3. run `cd papers/bedc && make` to verify")
    print(f"    4. write Lean target at lean4/BEDC/Derived/{title}/TasteGate.lean")
    print(f"    5. commit with `\\origin{{ai}}` already on the closurestatus block")
    return 0


def cmd_reject(args) -> int:
    p = _find_by_sha(args.sha)
    if p is None:
        print(f"No proposal matching sha {args.sha}", file=sys.stderr)
        return 1
    REJECTED_DIR.mkdir(parents=True, exist_ok=True)
    text = p.read_text()
    text += f"\n\n---\n\n## Rejection\n\n{args.reason}\n"
    target = REJECTED_DIR / p.name
    target.write_text(text)
    p.unlink()
    print(f"Rejected: {p.name} -> {target.relative_to(REPO_ROOT)}")
    return 0


def _seed_stub(title: str, slug: str, info: dict) -> str:
    """Generate a minimal seed-stub chapter with \\origin{ai}."""
    deps = info.get("dependencies") or []
    deps_text = ", ".join(f"$\\NameCert_{{\\{d}}}$" for d in deps) if deps else "(see proposal)"
    return f"""\\chapter{{A Concrete Naming Certificate for $\\{title}$}}
\\label{{ch:concrete-instances-{slug}-namecert}}

The $\\{title}$ interface is an AI-proposed BEDC chapter. Its carrier
sketch and dependency anchors come from the proposal at
\\texttt{{papers/bedc/proposals/accepted/}}; the seed-stub here records
the closurestatus block. Dependencies cited by the proposal:
{deps_text}.

\\section{{Carrier definition}}
\\label{{sec:{slug}-carrier}}

(Stub. The full carrier obligation is supplied by subsequent paper
rounds following the proposal's NameCert sketch.)

\\begin{{closurestatus}}{{\\{title}}}
  \\constructivestory{{}}
  \\theoryclosure{{\\seedClosure}}
  \\scopeclosed{{The seed scope is the proposed-chapter inventory recorded
  in the accepted proposal at \\texttt{{papers/bedc/proposals/accepted/}}.}}
  \\formalstatus{{\\unformalizedV}}
  \\bridgestatus{{none}}
  \\origin{{ai}}
  \\notclaimed{{The chapter does not close any obligation beyond the seed
  carrier sketch until the TasteGate instance and the five NameCert
  obligations are wired in.}}
  \\upgradepath{{Obligation closure requires (a) the four TasteGate
  obligations witnessed by a Lean instance at
  \\texttt{{BEDC.Derived.{title}.taste\\_gate}}, and (b) the NameCert
  obligation surface following the proposal sketch.}}
\\end{{closurestatus}}
"""


def main() -> int:
    parser = argparse.ArgumentParser(description="Review AI-proposed BEDC chapters")
    sub = parser.add_subparsers(dest="cmd", required=True)
    sub.add_parser("list", help="list pending proposals")
    show = sub.add_parser("show", help="print a proposal")
    show.add_argument("sha")
    accept = sub.add_parser("accept", help="promote to seed-stub chapter")
    accept.add_argument("sha")
    accept.add_argument("--force", action="store_true", help="bypass validation")
    reject = sub.add_parser("reject", help="archive as rejected")
    reject.add_argument("sha")
    reject.add_argument("--reason", required=True)
    args = parser.parse_args()

    fn = {"list": cmd_list, "show": cmd_show, "accept": cmd_accept, "reject": cmd_reject}[args.cmd]
    return fn(args)


if __name__ == "__main__":
    raise SystemExit(main())
