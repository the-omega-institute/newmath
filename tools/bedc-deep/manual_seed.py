#!/usr/bin/env python3
"""manual_seed — directly submit hand-crafted BOARD candidates to the
board_spawn judge, bypassing oracle_refill / probe.

When BOARD drains and oracle_refill is slow / failing, this tool lets a
human (or a separate Claude session) inject candidates directly. They go
through the SAME maker/checker quality bar as oracle and probe candidates
— no shortcut, just a different upstream source.

Usage:

  # Interactive: prompt for fields, one candidate at a time
  python3 tools/bedc-deep/manual_seed.py

  # File: read a JSON list of candidates
  python3 tools/bedc-deep/manual_seed.py --file my_seeds.json

  # Dry-run: show what would happen without appending to BOARD
  python3 tools/bedc-deep/manual_seed.py --file my_seeds.json --dry-run

Each candidate is a dict with keys:
  - title (≤80 chars)
  - claim (single implication form)
  - chapter (one of: core / proof_obligations / concrete_instances /
            hardening / formalization / proof_sprint / proof_standing)
  - fit_score (int 0-10)
  - novelty (int 0-10)
  - rationale (≥100 chars; cite file:line evidence of why this is open)
  - estimated_complexity ("short" | "medium" | "deep")
  - local_inputs (list of paper paths the proof depends on)

Optional:
  - source (auto-stamped to "manual_seed" if absent)

Example file:

  [
    {
      "title": "Polynomial division algorithm well-foundedness",
      "claim": "If p,q are polynomial spines with q non-zero, then iterated leading-coefficient elimination terminates in finitely many steps.",
      "chapter": "concrete_instances",
      "fit_score": 9,
      "novelty": 9,
      "rationale": "Polynomial chapter has add/multiply/normalize but no division-with-remainder. ...",
      "estimated_complexity": "medium",
      "local_inputs": ["papers/bedc/parts/concrete_instances/25_polynomial_namecert_construction.tex"]
    }
  ]
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))


REQUIRED_FIELDS = {
    "title": str,
    "claim": str,
    "chapter": str,
    "fit_score": (int, float),
    "novelty": (int, float),
    "rationale": str,
    "estimated_complexity": str,
    "local_inputs": list,
}

VALID_CHAPTERS = {
    "core", "proof_obligations", "concrete_instances", "hardening",
    "formalization", "proof_sprint", "proof_standing", "project_governance",
    "capstones",
}


def _validate(c: dict, idx: int) -> list[str]:
    errs: list[str] = []
    for key, typ in REQUIRED_FIELDS.items():
        if key not in c:
            errs.append(f"missing required field '{key}'")
        elif not isinstance(c[key], typ):
            errs.append(f"field '{key}' has wrong type: expected {typ}, got {type(c[key]).__name__}")
    if c.get("chapter") not in VALID_CHAPTERS:
        errs.append(f"chapter '{c.get('chapter')}' not one of {sorted(VALID_CHAPTERS)}")
    title = c.get("title", "")
    if len(title) > 80:
        errs.append(f"title too long ({len(title)}>80)")
    rationale = c.get("rationale", "")
    if len(rationale) < 100:
        errs.append(f"rationale too short ({len(rationale)}<100); cite file:line evidence")
    return errs


def _interactive_collect() -> list[dict]:
    print("Interactive mode — enter candidates one at a time. Empty title = done.")
    print()
    out: list[dict] = []
    while True:
        title = input("title (empty to finish): ").strip()
        if not title:
            break
        c: dict = {"title": title}
        c["claim"] = input("claim (single implication): ").strip()
        c["chapter"] = input(f"chapter ({'/'.join(sorted(VALID_CHAPTERS))}): ").strip()
        c["fit_score"] = int(input("fit_score (0-10): ").strip() or "8")
        c["novelty"] = int(input("novelty (0-10): ").strip() or "7")
        c["rationale"] = input("rationale (file:line evidence, why this is open): ").strip()
        c["estimated_complexity"] = input("estimated_complexity (short/medium/deep): ").strip() or "medium"
        local_inputs_raw = input("local_inputs (comma-separated paper paths): ").strip()
        c["local_inputs"] = [p.strip() for p in local_inputs_raw.split(",") if p.strip()]
        errs = _validate(c, len(out))
        if errs:
            print("VALIDATION ERRORS — fix and re-enter:")
            for e in errs:
                print(f"  - {e}")
            continue
        out.append(c)
        print(f"  → added candidate #{len(out)}: {title}")
        print()
    return out


def _load_file(path: Path) -> list[dict]:
    text = path.read_text(encoding="utf-8")
    data = json.loads(text)
    if isinstance(data, dict) and "candidates" in data:
        data = data["candidates"]
    if not isinstance(data, list):
        raise SystemExit("file must contain a JSON list of candidates "
                         "(or a dict with 'candidates' key)")
    return data


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--file", "-f", type=Path,
                        help="JSON file with a list of candidates (or {'candidates': [...]})")
    parser.add_argument("--dry-run", action="store_true",
                        help="Show what would be submitted without calling judge")
    parser.add_argument("--fit-threshold", type=int, default=None,
                        help="Override board_spawn fit_score threshold")
    parser.add_argument("--novelty-threshold", type=int, default=None,
                        help="Override board_spawn novelty threshold")
    args = parser.parse_args()

    if args.file:
        candidates = _load_file(args.file)
    else:
        candidates = _interactive_collect()

    if not candidates:
        print("No candidates to submit.")
        return 0

    # Validate all upfront
    all_errs: list[str] = []
    for i, c in enumerate(candidates):
        if not isinstance(c, dict):
            all_errs.append(f"candidate #{i}: not a dict")
            continue
        for e in _validate(c, i):
            all_errs.append(f"candidate #{i} ('{c.get('title','?')[:40]}'): {e}")
        c.setdefault("source", "manual_seed")
    if all_errs:
        print("VALIDATION FAILED — fix these and re-run:")
        for e in all_errs:
            print(f"  - {e}")
        return 1

    print(f"\nSubmitting {len(candidates)} candidate(s) to board_spawn judge:")
    for c in candidates:
        print(f"  • [{c['chapter']}] fit={c['fit_score']} nov={c['novelty']}  {c['title']}")
    print()

    if args.dry_run:
        print("DRY RUN — not calling judge.")
        print()
        print(json.dumps(candidates, ensure_ascii=False, indent=2))
        return 0

    import board_spawn
    kwargs: dict = {"codex_candidates": [], "oracle_candidates": candidates}
    if args.fit_threshold is not None:
        kwargs["fit_threshold"] = args.fit_threshold
    if args.novelty_threshold is not None:
        kwargs["novelty_threshold"] = args.novelty_threshold

    result = board_spawn.spawn_from_candidates(**kwargs)

    print()
    print("=" * 60)
    print(f"  ok={result.ok}  accepted={len(result.accepted)}  "
          f"rejected={len(result.rejected)}")
    print("=" * 60)
    if result.appended_ids:
        print(f"\nappended to BOARD: {', '.join(result.appended_ids)}")
    print()
    for c in result.accepted:
        print(f"  ✅ {c.get('title', '?')}")
    for c in result.rejected:
        reason = (c.get("reason") or c.get("verdict_reason") or "?")[:200]
        print(f"  ❌ {c.get('title', '?')}")
        print(f"      {reason}")
    if result.error:
        print(f"\nERROR: {result.error}")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
