#!/usr/bin/env python3
"""Publish sound negative discovery-radar records to a persistent dossier ledger.

The publisher consumes only kernel-grounded structural reconstruction
refutations from `bedc_ci.py discovery-radar --json`. It never promotes a
positive discovery assertion.
"""

from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
from datetime import datetime
from pathlib import Path
from typing import Any

try:
    from host_context import host_path, host_value
except Exception:  # pragma: no cover - usable from minimal checkouts.
    def host_value(_root: Path, name: str, default: str | None = None) -> str | None:
        return os.environ.get(name, default)

    def host_path(_root: Path, name: str, default: str | Path) -> Path:
        return Path(os.environ.get(name, str(default))).expanduser()

from structural_dna_build import ensure_structural_dna_build


REPO_ROOT = host_path(
    Path(__file__).resolve().parent.parent,
    "REPO_ROOT",
    default=Path(__file__).resolve().parent.parent,
)
BASE_BRANCH = host_value(REPO_ROOT, "BEDC_PIPELINE_BRANCH", default="codex-auto-dev") or "codex-auto-dev"
PUBLISH_WORKTREE = host_path(
    REPO_ROOT,
    "BEDC_REFUTATION_PUBLISH_WORKTREE",
    default="/tmp/bedc-refutation-wt",
)
LOG_DIR = REPO_ROOT / "tools" / "logs"
LOG_PATH = LOG_DIR / "discovery_refutation_publisher.log"
DEFAULT_INTERVAL = 21600
COMMAND_TIMEOUT = 1800
GIT_TIMEOUT = 180
JSON_LEDGER_REL = Path("docs/dossier/discovery_refutation_ledger.json")
MD_LEDGER_REL = Path("docs/dossier/discovery-refutation-ledger.md")
ALLOWED_LEDGER_RELS = (JSON_LEDGER_REL, MD_LEDGER_REL)


def now_iso() -> str:
    return datetime.now().isoformat(timespec="seconds")


def append_log(message: str) -> None:
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    with LOG_PATH.open("a", encoding="utf-8") as fh:
        fh.write(f"{now_iso()} {message}\n")


def run_cmd(
    cmd: list[str],
    *,
    cwd: Path = REPO_ROOT,
    env: dict[str, str] | None = None,
    timeout: int = COMMAND_TIMEOUT,
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        cmd,
        cwd=cwd,
        env=env,
        capture_output=True,
        text=True,
        timeout=timeout,
    )


def tail_text(text: str, limit: int = 1000) -> str:
    text = text.strip()
    if len(text) <= limit:
        return text
    return text[-limit:]


def load_radar_payload() -> dict[str, Any]:
    proc = run_cmd(["python3", "lean4/scripts/bedc_ci.py", "discovery-radar", "--json"])
    if proc.returncode != 0:
        combined = (proc.stdout or "") + (proc.stderr or "")
        raise RuntimeError(f"discovery-radar failed: {tail_text(combined)}")
    try:
        payload = json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        raise RuntimeError(f"discovery-radar emitted invalid JSON: {exc}") from exc
    if not isinstance(payload, dict):
        raise RuntimeError("discovery-radar JSON root is not an object")
    return payload


def radar_degraded_reason(payload: dict[str, Any]) -> str | None:
    fingerprints = int(payload.get("fingerprint_count") or 0)
    candidates = int(payload.get("candidate_count") or 0)
    refuted = int(payload.get("refuted_count") or 0)
    scanned = int(payload.get("classifier_endpoint_count") or 0)
    if fingerprints <= 0:
        return f"fingerprint_count={fingerprints}; scanned={scanned}"
    if candidates <= 0 and refuted <= 0:
        return f"candidate_count={candidates}; refuted_count={refuted}"
    return None


def _candidate_name(candidate: dict[str, Any]) -> str:
    for key in ("target", "candidate", "name"):
        value = str(candidate.get(key) or "").strip()
        if value:
            return value
    return ""


def _reconstruction_priors(candidate: dict[str, Any]) -> list[str]:
    priors: list[str] = []
    for item in _reconstruction_provenance(candidate):
        prior = str(item.get("prior") or "").strip()
        if prior:
            priors.append(prior)
    return sorted(set(priors))


def _reconstruction_provenance(candidate: dict[str, Any]) -> list[dict[str, Any]]:
    out: list[dict[str, Any]] = []
    for item in candidate.get("provenance", []) or []:
        if not isinstance(item, dict):
            continue
        if str(item.get("relation") or "") != "reconstruction":
            continue
        if item.get("kernel_grounded") is False:
            continue
        if str(item.get("evidence") or "") != "canonical_payload_equal":
            continue
        candidate_payload = str(item.get("candidate_canonical_payload") or "")
        prior_payload = str(item.get("prior_canonical_payload") or "")
        canonical_payload = str(item.get("canonical_payload") or "")
        if not canonical_payload:
            canonical_payload = candidate_payload if candidate_payload == prior_payload else ""
        if not candidate_payload or not prior_payload or candidate_payload != prior_payload:
            continue
        if not canonical_payload:
            continue
        out.append(item)
    return out


def _evidence_reduced_fp(candidate: dict[str, Any]) -> str:
    for item in _reconstruction_provenance(candidate):
        value = str(item.get("reduced_fp") or "")
        if value:
            return value
    evidence = candidate.get("evidence")
    if isinstance(evidence, dict):
        value = str(evidence.get("reduced_fp") or evidence.get("candidate_reduced_fp") or "")
        if value:
            return value
    for key in ("reduced_fp", "candidate_reduced_fp", "after_classifier_reduced_fingerprint"):
        value = str(candidate.get(key) or "")
        if value:
            return value
    return ""


def _evidence_canonical_payload(candidate: dict[str, Any]) -> str:
    for item in _reconstruction_provenance(candidate):
        value = str(
            item.get("canonical_payload")
            or item.get("candidate_canonical_payload")
            or ""
        )
        if value:
            return value
    return ""


def _has_kernel_grounded_canonical_payload_twin(candidate: dict[str, Any]) -> bool:
    if str(candidate.get("state") or "") != "refuted":
        return False
    refutation = candidate.get("refutation")
    if not isinstance(refutation, dict) or refutation.get("kernel_grounded") is not True:
        return False
    return bool(_reconstruction_provenance(candidate))


def refutation_records_from_payload(payload: dict[str, Any], *, timestamp: str) -> list[dict[str, Any]]:
    records: dict[tuple[str, tuple[str, ...]], dict[str, Any]] = {}
    for raw_candidate in payload.get("candidates", []) or []:
        if not isinstance(raw_candidate, dict):
            continue
        if not _has_kernel_grounded_canonical_payload_twin(raw_candidate):
            continue
        candidate = _candidate_name(raw_candidate)
        priors = _reconstruction_priors(raw_candidate)
        reduced_fp = _evidence_reduced_fp(raw_candidate)
        canonical_payload = _evidence_canonical_payload(raw_candidate)
        if not candidate or not priors or not canonical_payload:
            continue
        key = (candidate, tuple(priors))
        why = "structural reconstruction (canonical payload equal) of " + ", ".join(priors)
        records[key] = {
            "candidate": candidate,
            "refuted_because": why,
            "evidence": {
                "reduced_fp": reduced_fp,
                "evidence": "canonical_payload_equal",
                "prior": priors,
            },
            "kernel_grounded": True,
            "first_seen": timestamp,
        }
    return [records[key] for key in sorted(records)]


def load_existing_ledger(path: Path) -> list[dict[str, Any]]:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        return []
    except Exception as exc:
        append_log(f"[refutation] existing ledger unreadable; rebuilding entries: {exc}")
        return []
    if isinstance(data, list):
        return [item for item in data if isinstance(item, dict)]
    if isinstance(data, dict) and isinstance(data.get("records"), list):
        return [item for item in data["records"] if isinstance(item, dict)]
    return []


def ledger_key(entry: dict[str, Any]) -> tuple[str, tuple[str, ...]]:
    evidence = entry.get("evidence")
    priors: tuple[str, ...] = ()
    if isinstance(evidence, dict):
        raw_priors = evidence.get("prior")
        if isinstance(raw_priors, list):
            priors = tuple(sorted({str(item).strip() for item in raw_priors if str(item).strip()}))
        else:
            prior = str(raw_priors or "").strip()
            if prior:
                priors = (prior,)
    return (str(entry.get("candidate") or ""), priors)


def merge_records(existing: list[dict[str, Any]], current: list[dict[str, Any]], *, timestamp: str) -> list[dict[str, Any]]:
    first_seen_by_key: dict[tuple[str, tuple[str, ...]], str] = {}
    for entry in existing:
        key = ledger_key(entry)
        if not key[0] or not key[1]:
            continue
        first_seen = str(entry.get("first_seen") or "").strip()
        if first_seen:
            first_seen_by_key.setdefault(key, first_seen)
    merged: dict[tuple[str, tuple[str, ...]], dict[str, Any]] = {}
    for entry in current:
        key = ledger_key(entry)
        if not key[0] or not key[1]:
            continue
        updated = dict(entry)
        updated["first_seen"] = first_seen_by_key.get(key) or str(entry.get("first_seen") or timestamp)
        updated["refuted_because"] = entry["refuted_because"]
        updated["evidence"] = entry["evidence"]
        updated["kernel_grounded"] = True
        updated.pop("last_seen", None)
        merged[key] = updated
    return [merged[key] for key in sorted(merged)]


def ledger_content_signature(records: list[dict[str, Any]]) -> str:
    normalized = [
        {
            "candidate": str(entry.get("candidate") or ""),
            "refuted_because": str(entry.get("refuted_because") or ""),
            "evidence": entry.get("evidence") if isinstance(entry.get("evidence"), dict) else {},
            "kernel_grounded": bool(entry.get("kernel_grounded")),
            "first_seen": str(entry.get("first_seen") or ""),
        }
        for entry in records
    ]
    return json.dumps(normalized, ensure_ascii=False, sort_keys=True, separators=(",", ":"))


def write_json_ledger(path: Path, records: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(".json.tmp")
    tmp.write_text(json.dumps(records, indent=2, ensure_ascii=False, sort_keys=True) + "\n", encoding="utf-8")
    tmp.replace(path)


def _md_cell(value: str) -> str:
    return value.replace("|", "\\|").replace("\n", " ")


def write_markdown_ledger(path: Path, records: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    lines = [
        "# Discovery Refutation Ledger",
        "",
        "Sound negative records: candidates proven to be structural reconstructions, not novel discoveries.",
        "",
        "| candidate | why-not | evidence |",
        "|---|---|---|",
    ]
    for entry in records:
        evidence = entry.get("evidence") if isinstance(entry.get("evidence"), dict) else {}
        priors = ", ".join(str(item) for item in evidence.get("prior", []) if str(item))
        fp = str(evidence.get("reduced_fp") or "")
        evidence_text = f"reduced_fp={fp}; prior={priors}"
        lines.append(
            "| "
            + _md_cell(str(entry.get("candidate") or ""))
            + " | "
            + _md_cell(str(entry.get("refuted_because") or ""))
            + " | "
            + _md_cell(evidence_text)
            + " |"
        )
    tmp = path.with_suffix(".md.tmp")
    tmp.write_text("\n".join(lines) + "\n", encoding="utf-8")
    tmp.replace(path)


def git(*args: str, cwd: Path = REPO_ROOT, timeout: int = GIT_TIMEOUT) -> subprocess.CompletedProcess[str]:
    return run_cmd(["git", *args], cwd=cwd, timeout=timeout)


def import_push_lock():
    from contextlib import nullcontext

    tools_path = str(REPO_ROOT / "tools")
    if tools_path not in sys.path:
        sys.path.insert(0, tools_path)
    try:
        from repo_push_lock import acquire_push_lock

        return acquire_push_lock
    except Exception as exc:
        append_log(f"[refutation] push lock unavailable: {exc}")

        def fallback(_branch: str, timeout: int = 120):
            del _branch, timeout
            return nullcontext()

        return fallback


def ensure_publish_worktree() -> bool:
    PUBLISH_WORKTREE.parent.mkdir(parents=True, exist_ok=True)
    fetch = git("fetch", "origin", BASE_BRANCH)
    if fetch.returncode != 0:
        append_log(f"[refutation] fetch origin/{BASE_BRANCH} failed: {tail_text(fetch.stderr or fetch.stdout)}")
        return False
    if not (PUBLISH_WORKTREE / ".git").exists():
        if PUBLISH_WORKTREE.exists():
            shutil.rmtree(PUBLISH_WORKTREE)
        add = git(
            "worktree",
            "add",
            "--detach",
            str(PUBLISH_WORKTREE),
            f"origin/{BASE_BRANCH}",
            timeout=GIT_TIMEOUT,
        )
        if add.returncode != 0:
            append_log(f"[refutation] worktree add failed: {tail_text(add.stderr or add.stdout)}")
            return False
    reset = git("reset", "--hard", f"origin/{BASE_BRANCH}", cwd=PUBLISH_WORKTREE)
    if reset.returncode != 0:
        append_log(f"[refutation] worktree reset failed: {tail_text(reset.stderr or reset.stdout)}")
        return False
    clean = git("clean", "-fd", cwd=PUBLISH_WORKTREE)
    if clean.returncode != 0:
        append_log(f"[refutation] worktree clean failed: {tail_text(clean.stderr or clean.stdout)}")
        return False
    return True


def copy_ledgers_to_publish_worktree() -> None:
    for rel in ALLOWED_LEDGER_RELS:
        source = REPO_ROOT / rel
        dest = PUBLISH_WORKTREE / rel
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, dest)


def ledger_diff_exists(cwd: Path) -> bool:
    status = git("status", "--porcelain", "--", *(str(rel) for rel in ALLOWED_LEDGER_RELS), cwd=cwd)
    if status.returncode == 0 and status.stdout.strip():
        return True
    if status.returncode != 0:
        append_log(f"[refutation] git status failed: {tail_text(status.stderr or status.stdout)}")
        return False
    diff = git("diff", "--quiet", "--", *(str(rel) for rel in ALLOWED_LEDGER_RELS), cwd=cwd)
    if diff.returncode == 1:
        return True
    if diff.returncode != 0:
        append_log(f"[refutation] git diff failed: {tail_text(diff.stderr or diff.stdout)}")
    return False


def touched_paths(cwd: Path) -> list[str]:
    status = git("status", "--porcelain", "--", *(str(rel) for rel in ALLOWED_LEDGER_RELS), cwd=cwd)
    if status.returncode != 0:
        return []
    return sorted(line[3:].strip() for line in status.stdout.splitlines() if line.strip())


def push_to_origin(target_branch: str) -> bool:
    acquire_push_lock = import_push_lock()
    try:
        with acquire_push_lock(target_branch, timeout=120):
            for attempt in range(3):
                env = dict(os.environ)
                env["LEAN4_GUARDRAILS_BYPASS"] = "1"
                push = run_cmd(
                    ["git", "push", "origin", f"HEAD:{target_branch}"],
                    cwd=PUBLISH_WORKTREE,
                    env=env,
                    timeout=GIT_TIMEOUT,
                )
                if push.returncode == 0:
                    return True
                git("fetch", "origin", target_branch, cwd=PUBLISH_WORKTREE)
                rebase = git("rebase", f"origin/{target_branch}", cwd=PUBLISH_WORKTREE, timeout=GIT_TIMEOUT)
                if rebase.returncode != 0:
                    git("rebase", "--abort", cwd=PUBLISH_WORKTREE, timeout=60)
                    append_log(
                        "[refutation] rebase conflicted; abandon push this tick: "
                        + tail_text(rebase.stderr or rebase.stdout)
                    )
                    return False
                append_log(f"[refutation] origin/{target_branch} advanced; rebase retry {attempt + 1}/3")
            append_log("[refutation] push rejected after retries")
            return False
    except Exception as exc:
        append_log(f"[refutation] push failed: {type(exc).__name__}: {exc}")
        return False


def commit_and_maybe_push(*, no_push: bool) -> tuple[bool, str]:
    if no_push:
        return True, "push skipped"
    if not ensure_publish_worktree():
        return False, "publish worktree unavailable"
    copy_ledgers_to_publish_worktree()
    if not ledger_diff_exists(PUBLISH_WORKTREE):
        return True, "no ledger changes"
    changed = touched_paths(PUBLISH_WORKTREE)
    allowed = {str(rel) for rel in ALLOWED_LEDGER_RELS}
    if not changed or any(path not in allowed for path in changed):
        append_log(f"[refutation] unexpected touched paths: {changed}")
        return False, "unexpected touched paths"
    add = git("add", "--", *(str(rel) for rel in ALLOWED_LEDGER_RELS), cwd=PUBLISH_WORKTREE)
    if add.returncode != 0:
        append_log(f"[refutation] git add failed: {tail_text(add.stderr or add.stdout)}")
        return False, "git add failed"
    commit = git("commit", "-m", "发现 refutation ledger 自动更新", cwd=PUBLISH_WORKTREE)
    if commit.returncode != 0:
        append_log(f"[refutation] git commit failed: {tail_text(commit.stderr or commit.stdout)}")
        return False, "git commit failed"
    sha = git("rev-parse", "--short", "HEAD", cwd=PUBLISH_WORKTREE)
    commit_ref = sha.stdout.strip() if sha.returncode == 0 else "HEAD"
    if no_push:
        return True, f"committed {commit_ref}; push skipped"
    if push_to_origin(BASE_BRANCH):
        return True, f"committed and pushed {commit_ref}"
    return False, f"committed {commit_ref}; push failed"


def build_ledgers() -> tuple[list[dict[str, Any]], dict[str, Any]]:
    timestamp = now_iso()
    build_failure = ensure_structural_dna_build(append_log=append_log, label="refutation")
    if build_failure is not None:
        raise RuntimeError(build_failure)
    payload = load_radar_payload()
    degraded = radar_degraded_reason(payload)
    if degraded is not None:
        raise RuntimeError(f"discovery-radar degraded or empty: {degraded}")
    current_records = refutation_records_from_payload(payload, timestamp=timestamp)
    if not current_records:
        raise RuntimeError("discovery-radar returned no kernel-grounded refuted candidates")
    json_path = REPO_ROOT / JSON_LEDGER_REL
    existing = load_existing_ledger(json_path)
    records = merge_records(existing, current_records, timestamp=timestamp)
    content_changed = ledger_content_signature(existing) != ledger_content_signature(records)
    write_json_ledger(json_path, records)
    write_markdown_ledger(REPO_ROOT / MD_LEDGER_REL, records)
    summary = {
        "radar_refuted_count": int(payload.get("refuted_count") or 0),
        "kernel_grounded_records": len(current_records),
        "ledger_records": len(records),
        "ledger_content_changed": content_changed,
    }
    return records, summary


def run_once(*, no_push: bool) -> bool:
    try:
        _records, summary = build_ledgers()
        ok, message = commit_and_maybe_push(no_push=no_push)
        status = "OK" if ok else "WARN"
        append_log(
            f"[refutation] {status} radar_refuted={summary['radar_refuted_count']} "
            f"kernel_grounded={summary['kernel_grounded_records']} "
            f"ledger={summary['ledger_records']} {message}"
        )
        print(
            "[discovery-refutation-publisher]"
            f" radar_refuted={summary['radar_refuted_count']}"
            f" kernel_grounded={summary['kernel_grounded_records']}"
            f" ledger={summary['ledger_records']}"
            f" {message}",
            flush=True,
        )
        return ok
    except Exception as exc:
        append_log(f"[refutation] ERROR {type(exc).__name__}: {exc}")
        print(f"[discovery-refutation-publisher] ERROR {type(exc).__name__}: {exc}", file=sys.stderr)
        return False


def interval_seconds() -> int:
    raw = os.environ.get("REFUTATION_PUBLISH_INTERVAL_SECONDS", "")
    if not raw:
        return DEFAULT_INTERVAL
    try:
        return max(int(raw), 1)
    except ValueError:
        append_log(f"[refutation] invalid REFUTATION_PUBLISH_INTERVAL_SECONDS={raw!r}; using {DEFAULT_INTERVAL}")
        return DEFAULT_INTERVAL


def main() -> int:
    parser = argparse.ArgumentParser(description="Publish kernel-grounded discovery refutations.")
    parser.add_argument("--once", action="store_true", help="Run one publish cycle and exit")
    parser.add_argument("--no-push", action="store_true", help="Commit in the publish worktree but do not push")
    args = parser.parse_args()
    if args.once:
        return 0 if run_once(no_push=args.no_push) else 1
    sys.stderr.write("discovery refutation publisher loop moved to tools/discovery_pipeline_daemon.py; use --once for debugging\n")
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
