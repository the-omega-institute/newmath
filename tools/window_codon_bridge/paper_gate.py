#!/usr/bin/env python3
"""Gate the generated Window6--codon-Q6 bridge paper."""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[1]
CLAIMS = SCRIPT_DIR / "registries" / "claims.json"
PAPER_DIR = REPO_ROOT / "papers" / "window_codon_bridge"
PARTS_DIR = PAPER_DIR / "parts"

CJK_RE = re.compile(r"[\u3400-\u4DBF\u4E00-\u9FFF\uF900-\uFAFF]")
FORBIDDEN_MATH_RE = re.compile(r"\\\[|\\begin\{(?:equation|equation\*|align|align\*|eqnarray|eqnarray\*)\}")
CLAIM_STATUS_RE = re.compile(r"^%\s*CLAIM_STATUS\s+claim_id=(\S+)\s+status=(\S+)\s*$", re.MULTILINE)


def load_claims() -> dict[str, str]:
    doc = json.loads(CLAIMS.read_text(encoding="utf-8"))
    return {
        str(claim.get("claim_id")): str(claim.get("status"))
        for claim in doc.get("claims", [])
        if claim.get("claim_id")
    }


def tex_files() -> list[Path]:
    files = [PAPER_DIR / "main.tex"]
    if PARTS_DIR.exists():
        files.extend(sorted(PARTS_DIR.glob("*.tex")))
    return files


def check_no_cjk(files: list[Path]) -> list[str]:
    errors: list[str] = []
    for path in files:
        text = path.read_text(encoding="utf-8")
        for line_no, line in enumerate(text.splitlines(), start=1):
            if CJK_RE.search(line):
                errors.append(f"{path.relative_to(REPO_ROOT)}:{line_no}: CJK text is not allowed in bridge paper TeX")
    return errors


def check_math_env(files: list[Path]) -> list[str]:
    errors: list[str] = []
    for path in files:
        text = path.read_text(encoding="utf-8")
        match = FORBIDDEN_MATH_RE.search(text)
        if match:
            line_no = text[: match.start()].count("\n") + 1
            errors.append(f"{path.relative_to(REPO_ROOT)}:{line_no}: forbidden math environment {match.group(0)}")
    return errors


def check_consistency() -> list[str]:
    errors: list[str] = []
    expected = load_claims()
    corr_path = PARTS_DIR / "correspondences.tex"
    if not corr_path.exists():
        return [f"{corr_path.relative_to(REPO_ROOT)}: missing generated correspondences file"]
    text = corr_path.read_text(encoding="utf-8")
    seen: dict[str, str] = {}
    for claim_id, status in CLAIM_STATUS_RE.findall(text):
        if claim_id in seen:
            errors.append(f"{corr_path.relative_to(REPO_ROOT)}: duplicate claim marker for {claim_id}")
        seen[claim_id] = status
    for claim_id, status in expected.items():
        if claim_id not in seen:
            errors.append(f"{corr_path.relative_to(REPO_ROOT)}: missing claim {claim_id}")
            continue
        if seen[claim_id] != status:
            errors.append(
                f"{corr_path.relative_to(REPO_ROOT)}: claim {claim_id} has verdict {seen[claim_id]}, registry has {status}"
            )
    for claim_id in seen:
        if claim_id not in expected:
            errors.append(f"{corr_path.relative_to(REPO_ROOT)}: unknown generated claim {claim_id}")
    return errors


def main() -> int:
    files = tex_files()
    errors: list[str] = []
    errors.extend(check_consistency())
    errors.extend(check_no_cjk(files))
    errors.extend(check_math_env(files))
    if errors:
        for error in errors:
            print(f"[paper-gate] FAIL: {error}", file=sys.stderr)
        return 1
    print("[paper-gate] OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
