#!/usr/bin/env python3
"""Bridge coverage-gap discovery for BEDC Nat-value sequence carriers.

Lists BEDC.Derived carriers with Nat-valued source functions and local
theorem signals that mention those functions.

This script reports the coverage tail. A Nat-valued row is only honest as a
pointwise/readback equality over an existing BEDC.Derived source; it is not a
carrier equivalence. Consumers that need mathlib target hints can use
`bridge_nat_sequence_candidates.py`.

It never writes a bridge and never touches MATRIX.

Usage:
    python3 scripts/bridge_coverage_gap.py            # human-readable table
    python3 scripts/bridge_coverage_gap.py --json     # machine-readable
    python3 scripts/bridge_coverage_gap.py --top 10   # highest-priority N
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

DECL_HEADER_RE = re.compile(
    r"(?ms)^\s*def\s+([A-Za-z_][A-Za-z0-9_']*)\b(.*?)(?::=|\n\s*\|)"
)
THEOREM_START_RE = re.compile(
    r"^\s*(?:private\s+|protected\s+)?(?:theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_']*)\b"
)
TOP_LEVEL_DECL_RE = re.compile(
    r"^\s*(?:private\s+|protected\s+)?"
    r"(?:abbrev|def|theorem|lemma|inductive|structure|class|instance|namespace|section|end)\b"
)
THEOREM_SIGNAL_RE = re.compile(
    r"(?:recurrence|recursion|closedform|closedformula|closed_form|closed_formula|closed|formula)"
    r"|(?:^|_)(?:eq|succ|successor|zero)(?:_|$)",
    re.IGNORECASE,
)
STRONG_THEOREM_SIGNAL_RE = re.compile(
    r"(?:recurrence|recursion|closedform|closedformula|closed_form|closed_formula|closed|formula)",
    re.IGNORECASE,
)
BINDER_RE = re.compile(r"[\(\{\[]([^()\[\]{}]*:[^()\[\]{}]*)[\)\}\]]")


def repo_root() -> Path:
    out = subprocess.run(
        ["git", "rev-parse", "--show-toplevel"], capture_output=True, text=True
    )
    return Path(out.stdout.strip() or ".")


def open_feat_bridge_slugs(root: Path) -> set[str]:
    """Slugs of carriers currently being worked by an open feat-bridge branch.

    We normalise both branch slug and carrier stem to lowercase alnum so
    `feat-bridge-narayana` matches carrier `NarayanaNumberUp`.
    """
    out = subprocess.run(
        ["git", "for-each-ref", "--format=%(refname:short)", "refs/remotes/origin/"],
        capture_output=True,
        text=True,
        cwd=root,
    ).stdout
    slugs: set[str] = set()
    for line in out.splitlines():
        m = re.search(r"feat-bridge-([a-z0-9-]+)", line)
        if m:
            slugs.add(re.sub(r"[^a-z0-9]", "", m.group(1)))
    return slugs


def carrier_contested(stem_norm: str, slugs: set[str]) -> str | None:
    """Return the matching branch slug if this carrier is under active work."""
    for s in slugs:
        # boundary/aggregate branch slugs (e.g. combinatorialboundaries) are
        # skipped as too broad to imply a specific carrier claim.
        if s.endswith("boundaries") or s.endswith("boundary"):
            continue
        core = re.sub(r"(number|numbers|up|poly|polynomial|second|mod|p)$", "", s)
        core = core or s
        if len(core) >= 4 and (stem_norm.startswith(core) or core.startswith(stem_norm[:6])):
            return s
    return None


def carrier_bridged(name: str, matrix: str) -> bool:
    """A carrier is bridged if a MATRIX row cites BEDC.Derived.<name>.<fn>."""
    return f"BEDC.Derived.{name}." in matrix


def _last_top_level_colon(text: str) -> int:
    depth = 0
    found = -1
    for index, char in enumerate(text):
        if char in "([{":
            depth += 1
        elif char in ")]}" and depth > 0:
            depth -= 1
        elif char == ":" and depth == 0:
            found = index
    return found


def _split_top_level_arrows(text: str) -> list[str]:
    clean = text.replace("→", "->")
    parts: list[str] = []
    start = 0
    depth = 0
    index = 0
    while index < len(clean):
        char = clean[index]
        if char in "([{":
            depth += 1
            index += 1
        elif char in ")]}" and depth > 0:
            depth -= 1
            index += 1
        elif clean.startswith("->", index) and depth == 0:
            parts.append(clean[start:index].strip())
            index += 2
            start = index
        else:
            index += 1
    parts.append(clean[start:].strip())
    return parts


def _nat_atom(text: str) -> bool:
    item = text.strip()
    while item.startswith("(") and item.endswith(")"):
        item = item[1:-1].strip()
    return item == "Nat"


def _binder_nat_arity(content: str) -> int | None:
    colon = _last_top_level_colon(content)
    if colon < 0:
        return None
    names = content[:colon].strip()
    typ = content[colon + 1 :].strip()
    if not _nat_atom(typ):
        return None
    return max(1, len([part for part in names.split() if part != "_"]))


def _pure_nat_value_decl_info(header: str) -> dict | None:
    colon = _last_top_level_colon(header)
    if colon < 0:
        return None
    prefix = header[:colon]
    typ = header[colon + 1 :]
    arity = 0
    spans: list[tuple[int, int]] = []
    for match in BINDER_RE.finditer(prefix):
        binder_arity = _binder_nat_arity(match.group(1))
        if binder_arity is None:
            return None
        arity += binder_arity
        spans.append(match.span())
    remainder_parts: list[str] = []
    cursor = 0
    for start, end in spans:
        remainder_parts.append(prefix[cursor:start])
        cursor = end
    remainder_parts.append(prefix[cursor:])
    if "".join(remainder_parts).strip():
        return None
    parts = _split_top_level_arrows(typ)
    if not parts or not all(_nat_atom(part) for part in parts):
        return None
    arity += max(0, len(parts) - 1)
    if arity == 0:
        return None
    return {"arity": arity}


def _pure_nat_value_decl(header: str) -> bool:
    return _pure_nat_value_decl_info(header) is not None


def pure_nat_value_decl_infos(text: str) -> list[dict]:
    infos: list[dict] = []
    for order, match in enumerate(DECL_HEADER_RE.finditer(text)):
        info = _pure_nat_value_decl_info(match.group(2))
        if info is None:
            continue
        infos.append({"name": match.group(1), "arity": info["arity"], "order": order})
    return infos


def pure_nat_value_decl_names(text: str) -> list[str]:
    return [info["name"] for info in pure_nat_value_decl_infos(text)]


def theorem_blocks(text: str) -> list[dict]:
    blocks: list[dict] = []
    active_name: str | None = None
    active_lines: list[str] = []
    for line in text.splitlines(keepends=True):
        start = THEOREM_START_RE.match(line)
        if start:
            if active_name is not None:
                blocks.append({"name": active_name, "text": "".join(active_lines)})
            active_name = start.group(1)
            active_lines = [line]
            continue
        if active_name is not None and TOP_LEVEL_DECL_RE.match(line):
            blocks.append({"name": active_name, "text": "".join(active_lines)})
            active_name = None
            active_lines = []
        if active_name is not None:
            active_lines.append(line)
    if active_name is not None:
        blocks.append({"name": active_name, "text": "".join(active_lines)})
    return blocks


def _token_re(name: str) -> re.Pattern[str]:
    return re.compile(rf"(?<![A-Za-z0-9_']){re.escape(name)}(?![A-Za-z0-9_'])")


def structural_theorem_signals(text: str, decl_infos: list[dict]) -> dict[str, list[dict]]:
    signals = {str(info["name"]): [] for info in decl_infos}
    token_res = {name: _token_re(name) for name in signals}
    for block in theorem_blocks(text):
        theorem_name = str(block["name"])
        if not THEOREM_SIGNAL_RE.search(theorem_name):
            continue
        block_text = str(block["text"])
        after_name = block_text.split(theorem_name, 1)[1] if theorem_name in block_text else block_text
        strong = bool(STRONG_THEOREM_SIGNAL_RE.search(theorem_name))
        for name, token in token_res.items():
            if token.search(after_name):
                signals[name].append({"name": theorem_name, "strong": strong})
    return signals


def order_decl_infos(decl_infos: list[dict], signals: dict[str, list[dict]]) -> list[dict]:
    primary = min(decl_infos, key=lambda info: int(info.get("order", 0)))
    rest = [info for info in decl_infos if info is not primary]
    ranked_rest = sorted(
        rest,
        key=lambda info: (
            -sum(1 for item in signals.get(str(info["name"]), []) if item.get("strong")),
            -len(signals.get(str(info["name"]), [])),
            int(info.get("order", 0)),
            str(info["name"]),
        ),
    )
    return [primary, *ranked_rest]


def scan(root: Path):
    derived = root / "lean4" / "BEDC" / "Derived"
    matrix = (root / "papers" / "bedc_mathlib_bridge" / "MATRIX.md").read_text()
    slugs = open_feat_bridge_slugs(root)

    total = bridged = contested = no_theorem_signal = 0
    worklist = []
    for f in sorted(derived.glob("*Up.lean")):
        name = f.stem  # e.g. NarayanaNumberUp
        stem_norm = re.sub(r"[^a-z0-9]", "", name[:-2].lower())
        text = f.read_text()
        decl_infos = pure_nat_value_decl_infos(text)
        if not decl_infos:
            continue
        signals = structural_theorem_signals(text, decl_infos)
        signalled_infos = [info for info in decl_infos if signals.get(str(info["name"]))]
        if not signalled_infos:
            no_theorem_signal += 1
            continue
        total += 1
        if carrier_bridged(name, matrix):
            bridged += 1
            continue
        claim = carrier_contested(stem_norm, slugs)
        if claim:
            contested += 1
            continue
        ordered_infos = order_decl_infos(signalled_infos, signals)
        theorem_count = sum(len(signals.get(str(info["name"]), [])) for info in signalled_infos)
        strong_theorem_count = sum(
            1
            for info in signalled_infos
            for theorem in signals.get(str(info["name"]), [])
            if theorem.get("strong")
        )
        nat_defs = len(signalled_infos)
        priority = strong_theorem_count * 4 + theorem_count * 2 + min(nat_defs, 3)
        namespace = f"BEDC.Derived.{name}"
        bridge_decls = [f"{namespace}.{info['name']}" for info in ordered_infos[:4]]
        source_theorems = [
            f"{namespace}.{theorem['name']}"
            for info in ordered_infos
            for theorem in signals.get(str(info["name"]), [])
        ][:8]
        worklist.append(
            {
                "carrier": name,
                "namespace": namespace,
                "bridge_decls": bridge_decls,
                "file": str(f.relative_to(root)),
                "nat_recursion_defs": nat_defs,
                "has_recurrence_or_closedform_theorem": True,
                "structural_signal_theorem_count": theorem_count,
                "strong_structural_signal_theorem_count": strong_theorem_count,
                "bedc_source_theorem_guess": source_theorems,
                "priority": priority,
            }
        )
    worklist.sort(key=lambda d: (-d["priority"], d["carrier"]))
    return {
        "class": "nat_sequence_coverage_gap",
        "structural_candidate": False,
        "allowed_bridge_kind": "nat_value_sequence",
        "note": "Nat-valued carriers are eligible only as honest pointwise/readback bridges.",
        "total_bridge_shaped_carriers": total,
        "already_in_matrix": bridged,
        "contested_open_feat_bridge": contested,
        "without_recurrence_or_closedform_signal": no_theorem_signal,
        "uncontested_unbridged": len(worklist),
        "worklist": worklist,
    }


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--json", action="store_true", help="machine-readable output")
    ap.add_argument("--top", type=int, default=0, help="only the highest-priority N")
    args = ap.parse_args()

    result = scan(repo_root())
    if args.top:
        result["worklist"] = result["worklist"][: args.top]

    if args.json:
        print(json.dumps(result, indent=2))
        return 0

    print(
        f"bridge coverage gap: {result['total_bridge_shaped_carriers']} "
        f"bridge-shaped Nat-value sequence carriers | "
        f"{result['already_in_matrix']} bridged | "
        f"{result['contested_open_feat_bridge']} contested (open feat-bridge) | "
        f"{result['uncontested_unbridged']} uncontested-unbridged worklist"
    )
    for row in result["worklist"]:
        flag = "recur" if row["has_recurrence_or_closedform_theorem"] else "     "
        print(
            f"  p{row['priority']} [{flag}] {row['carrier']:34} "
            f"({row['nat_recursion_defs']} Nat-rec defs)"
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())
