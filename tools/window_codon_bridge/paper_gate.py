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
EXPS = SCRIPT_DIR / "registries" / "experiments.json"
EXPERIMENTS_DIR = SCRIPT_DIR / "experiments"
ORACLE_INBOX = SCRIPT_DIR / "oracle_inbox" / "candidates.jsonl"
CHATGPT_ORACLE_INBOX = SCRIPT_DIR / "oracle_inbox" / "chatgpt_consultations.jsonl"
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


def load_claim_doc() -> dict:
    return json.loads(CLAIMS.read_text(encoding="utf-8"))


def load_experiment_doc() -> dict:
    return json.loads(EXPS.read_text(encoding="utf-8"))


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


def check_registry_topology() -> list[str]:
    errors: list[str] = []
    claims = load_claim_doc().get("claims", [])
    experiments = load_experiment_doc().get("experiments", [])

    claim_ids = [str(claim.get("claim_id")) for claim in claims if claim.get("claim_id")]
    experiment_ids = [str(exp.get("experiment_id")) for exp in experiments if exp.get("experiment_id")]
    claim_by_id = {claim_id: claim for claim_id, claim in zip(claim_ids, claims)}
    experiment_by_id = {experiment_id: exp for experiment_id, exp in zip(experiment_ids, experiments)}

    if len(claim_by_id) != len(claim_ids):
        errors.append(f"{CLAIMS.relative_to(REPO_ROOT)}: duplicate claim_id")
    if len(experiment_by_id) != len(experiment_ids):
        errors.append(f"{EXPS.relative_to(REPO_ROOT)}: duplicate experiment_id")

    for claim_id, claim in claim_by_id.items():
        experiment_id = str(claim.get("experiment_id") or "")
        if not experiment_id:
            errors.append(f"{CLAIMS.relative_to(REPO_ROOT)}: claim {claim_id} has no experiment_id")
            continue
        exp = experiment_by_id.get(experiment_id)
        if exp is None:
            errors.append(f"{CLAIMS.relative_to(REPO_ROOT)}: claim {claim_id} points to missing experiment {experiment_id}")
            continue
        if str(exp.get("claim_id") or "") != claim_id:
            errors.append(
                f"{EXPS.relative_to(REPO_ROOT)}: experiment {experiment_id} points to {exp.get('claim_id')}, expected {claim_id}"
            )

    referenced_scripts: set[str] = set()
    for experiment_id, exp in experiment_by_id.items():
        claim_id = str(exp.get("claim_id") or "")
        if claim_id and claim_id not in claim_by_id:
            errors.append(f"{EXPS.relative_to(REPO_ROOT)}: experiment {experiment_id} points to missing claim {claim_id}")
        script_path = exp.get("script_path")
        if not script_path:
            continue
        script = REPO_ROOT / str(script_path)
        referenced_scripts.add(str(script.relative_to(REPO_ROOT)))
        if not script.exists():
            errors.append(f"{EXPS.relative_to(REPO_ROOT)}: experiment {experiment_id} script is missing: {script_path}")

    for script in sorted(EXPERIMENTS_DIR.glob("run_*.py")):
        rel = str(script.relative_to(REPO_ROOT))
        if rel not in referenced_scripts:
            errors.append(f"{script.relative_to(REPO_ROOT)}: derivation script is not registered in experiments.json")

    return errors


def check_oracle_inbox() -> list[str]:
    errors: list[str] = []
    for inbox, schema in (
        (ORACLE_INBOX, "window_codon_oracle_candidate.v1"),
        (CHATGPT_ORACLE_INBOX, "window_codon_chatgpt_oracle_consultation.v1"),
    ):
        if not inbox.exists():
            continue
        errors.extend(check_oracle_jsonl(inbox, schema))
    return errors


def check_oracle_jsonl(path: Path, schema: str) -> list[str]:
    errors: list[str] = []
    for line_no, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        if not line.strip():
            continue
        try:
            row = json.loads(line)
        except json.JSONDecodeError as exc:
            errors.append(f"{path.relative_to(REPO_ROOT)}:{line_no}: invalid JSONL row: {exc.msg}")
            continue
        if row.get("record_schema") != schema:
            errors.append(f"{path.relative_to(REPO_ROOT)}:{line_no}: unexpected oracle record_schema")
        if row.get("claim_update_allowed") is not False:
            errors.append(f"{path.relative_to(REPO_ROOT)}:{line_no}: oracle row must not allow claim updates")
        if row.get("verdict_update_allowed") is not False:
            errors.append(f"{path.relative_to(REPO_ROOT)}:{line_no}: oracle row must not allow verdict updates")
        if not row.get("prompt_sha256"):
            errors.append(f"{path.relative_to(REPO_ROOT)}:{line_no}: missing prompt_sha256")
    return errors


def main() -> int:
    files = tex_files()
    errors: list[str] = []
    errors.extend(check_registry_topology())
    errors.extend(check_oracle_inbox())
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
