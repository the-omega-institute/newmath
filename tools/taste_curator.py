#!/usr/bin/env python3
"""Taste curator daemon for BEDC concrete-instance review.

The daemon detects suspicious taste signals, alerts, and appends stable
review-queue entries. Its automated action is rule evolution: cluster repeated
findings by flag and dispatch codex to tighten P/R prompts or audit/lint gates.
It does not edit concrete-instance content directly.
"""

from __future__ import annotations

import argparse
import contextlib
import difflib
import hashlib
import json
import math
import os
import re
import shutil
import signal
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parent.parent
BASE_BRANCH = "codex-auto-dev"
PID_FILE = Path("/tmp/.bedc_taste_curator.pid")
ALERT_LOG = Path("/tmp/.bedc_taste_alerts.log")
QUEUE_FILE = Path("/tmp/.bedc_taste_review_queue.jsonl")
COOLDOWN_FILE = Path("/tmp/.bedc_taste_cooldown.json")
STATE_FILE = Path("/tmp/.bedc_taste_state.json")
ALLOWLIST_FILE = REPO_ROOT / "papers" / "bedc" / "taste_allowlist.json"
APPROVALS_FILE = REPO_ROOT / "papers" / "bedc" / "taste_approvals.json"
CONFIG_FILE = REPO_ROOT / "papers" / "bedc" / "taste_curator_config.json"
CODEX_PATH = shutil.which("codex") or "/opt/homebrew/bin/codex"

DEFAULT_CONFIG: dict[str, Any] = {
    "version": 1,
    "AUTO_FIX_WITHOUT_CONFIRMATION": True,
    "MISLABELED_COMPOSITE_FIELD_OVERLAP_MIN": 3,
    "MISLABELED_COMPOSITE_BUCKET_MEMBER_MIN": 3,
    "ISOLATED_THEOREM_GRACE_ROUNDS": 50,
    "LOW_ENTROPY_AUTOREF_MIN_TARGETS": 3,
    "LOW_ENTROPY_SHANNON_MIN": 1.0,
    "LOW_ENTROPY_BOILERPLATE_SCORE_MIN": 0.7,
    "COOLDOWN_HOURS": 24,
    "MAX_AUTO_FIXES_PER_CYCLE": 1,
    "CYCLE_INTERVAL_SECONDS": 3600,
}

TIMEOUTS = {
    "git": 60,
    "carrier": 120,
    "inventory": 180,
    "scan": 180,
    "codex": 1800,
    "verify": 900,
}

AUTO_FIXABLE_FLAGS = {
    "missing_origin",
    "invalid_origin",
    "mislabeled_composite",
    "simple_label_correction",
    "allowlist_metadata_correction",
}

RULE_EVOLUTION_ALLOWED_FILES = {
    "papers/bedc/scripts/prompts/phase_b.txt",
    "papers/bedc/scripts/prompts/phase_c.txt",
    "papers/bedc/scripts/prompts/phase_review.txt",
    "papers/bedc/scripts/prompts/phase_revise.txt",
    "lean4/scripts/bedc_ci.py",
    "papers/bedc/scripts/phase_paper_gates.py",
    "lean4/scripts/phase_d_lint.py",
}

RULE_EVOLUTION_OPTIONAL_FILES = {
    "papers/bedc/scripts/prompts/phase_verify.txt",
    "lean4/scripts/prompts/phase_b.txt",
    "lean4/scripts/prompts/phase_c.txt",
    "lean4/scripts/prompts/phase_d.txt",
}

RULE_EVOLUTION_FORBIDDEN_PREFIXES = (
    "papers/bedc/parts/concrete_instances/",
    "lean4/BEDC/",
    "papers/bedc/scripts/codex_revise.py",
    "lean4/scripts/codex_formalize.py",
)

MAX_RULE_EVOLUTION_CLUSTER_SIZE = 20

META_PROMPT_RULE_EVOLUTION = """You are evolving the P/R automation pipeline RULES based on observed quality
violations. You will receive a cluster of findings (multiple chapters / Lean
targets exhibiting the same pattern). Your job:

1. Identify the ROOT CAUSE — which P/R prompt instruction is missing, OR
   which audit check would have caught this pattern at merge time.
2. Modify ONE OR MORE of these files (ONLY these — file whitelist enforced):
   - papers/bedc/scripts/prompts/phase_b.txt
   - papers/bedc/scripts/prompts/phase_c.txt
   - papers/bedc/scripts/prompts/phase_review.txt
   - papers/bedc/scripts/prompts/phase_revise.txt
   - papers/bedc/scripts/prompts/phase_verify.txt (if exists)
   - lean4/scripts/prompts/phase_b.txt
   - lean4/scripts/prompts/phase_c.txt
   - lean4/scripts/prompts/phase_d.txt (if exists)
   - lean4/scripts/bedc_ci.py (add detect_*() function + payload wiring,
     pattern: detect_preamble_duplicate_commands at line ~541)
   - papers/bedc/scripts/phase_paper_gates.py
   - lean4/scripts/phase_d_lint.py
3. DO NOT touch papers/bedc/parts/concrete_instances/**/*.tex
   DO NOT touch lean4/BEDC/**
   DO NOT touch codex_revise.py / codex_formalize.py / other daemon scripts
4. Bump the prompt version marker in any prompt file you edit (e.g. v5.X → v5.X+1).
5. Add terse imperative rule text. No rationale paragraphs, no incident
   history, no version-numbered names.
6. Verify locally before commit:
   - python3 -m py_compile lean4/scripts/bedc_ci.py
   - python3 lean4/scripts/bedc_ci.py audit (NEW gate may flag legacy
     violations, that is expected; the gate must not crash)
   - For any phase_paper_gates.py change: smoke test it parses
   - For any phase_d_lint.py change: smoke test it parses
7. Commit with message format:
   "taste-evolve: <flag> pattern - <one-line summary>"
8. Do NOT push (orchestrator [the daemon] will push after success).

Cluster evidence will be provided after this prompt.
"""

BOILERPLATE_PHRASES = (
    "name certificate",
    "namecert",
    "closure status",
    "finite carrier",
    "the carrier fields",
    "the construction records",
    "witness package",
    "obligation surface",
    "semantic certificate",
    "classifier route",
    "ledger",
    "scoped closure",
)

TEMPLATE_PARAGRAPHS = (
    "The packet records a finite NameCert carrier together with the "
    "obligation surface needed for closure accounting.",
    "The construction is a finite BEDC carrier whose fields are read as "
    "closed generated histories and whose theorem exports certify the route.",
    "This chapter packages the concrete instance as a NameCert construction "
    "and reports its closure status at the end of the section.",
)


@dataclass
class ChangedArtifacts:
    head: str
    base: str
    concrete_files: list[Path]
    lean_files: list[Path]
    subjects: list[str]
    local_round: int


@dataclass
class Finding:
    flag: str
    chapter_slug: str
    severity: str
    evidence: dict[str, Any]
    recommended_action: str
    paper_file: str | None = None
    lean_files: list[str] = field(default_factory=list)
    lean_target: str | None = None
    round_age: int | None = None
    commit: str | None = None
    id: str | None = None

    def to_queue_entry(self, ts: str) -> dict[str, Any]:
        payload: dict[str, Any] = {
            "ts": ts,
            "id": self.id,
            "flag": self.flag,
            "chapter_slug": self.chapter_slug,
            "commit": self.commit,
            "severity": self.severity,
            "evidence": self.evidence,
            "recommended_action": self.recommended_action,
        }
        if self.paper_file:
            payload["paper_file"] = self.paper_file
        if self.lean_files:
            payload["lean_files"] = self.lean_files
        if self.lean_target:
            payload["lean_target"] = self.lean_target
        if self.round_age is not None:
            payload["round_age"] = self.round_age
        return payload


class TasteError(RuntimeError):
    pass


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def short_hash(text: str, n: int = 8) -> str:
    return hashlib.sha1(text.encode("utf-8", errors="ignore")).hexdigest()[:n]


def sanitize_branch_piece(text: str) -> str:
    out = re.sub(r"[^A-Za-z0-9._-]+", "-", text.strip())
    out = re.sub(r"-+", "-", out).strip("-")
    return out[:80] or "unknown"


def slug_key(text: str) -> str:
    text = text.replace("Up", "")
    return re.sub(r"[^a-z0-9]+", "", text.lower())


def rel(path: Path) -> str:
    try:
        return str(path.relative_to(REPO_ROOT))
    except ValueError:
        return str(path)


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8", errors="ignore")


def read_json(path: Path, default: Any) -> Any:
    try:
        if not path.exists():
            return default
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception as exc:
        print(f"[taste] could not read JSON {path}: {exc}", file=sys.stderr)
        return default


def write_json(path: Path, data: Any, dry_run: bool = False) -> None:
    if dry_run:
        print(f"[taste] dry-run: would write {path}", file=sys.stderr)
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(data, indent=2, sort_keys=False) + "\n", encoding="utf-8")
    tmp.replace(path)


def run(
    cmd: list[str],
    *,
    cwd: Path = REPO_ROOT,
    check: bool = True,
    capture: bool = True,
    timeout: int | None = None,
    env: dict[str, str] | None = None,
) -> subprocess.CompletedProcess[str]:
    res = subprocess.run(
        cmd,
        cwd=cwd,
        env=env,
        text=True,
        capture_output=capture,
        timeout=timeout,
    )
    if check and res.returncode != 0:
        out = (res.stdout or "") + (res.stderr or "")
        raise TasteError(f"command failed rc={res.returncode}: {' '.join(cmd)}\n{tail(out)}")
    return res


def git(*args: str, **kwargs: Any) -> subprocess.CompletedProcess[str]:
    kwargs.setdefault("timeout", TIMEOUTS["git"])
    return run(["git", *args], **kwargs)


def tail(text: str, limit: int = 1200) -> str:
    text = text.strip()
    return text[-limit:] if len(text) > limit else text


def load_config() -> dict[str, Any]:
    raw = read_json(CONFIG_FILE, {})
    cfg = dict(DEFAULT_CONFIG)
    if isinstance(raw, dict):
        cfg.update(raw)
    for key, default in DEFAULT_CONFIG.items():
        if key == "version":
            continue
        if isinstance(default, bool):
            cfg[key] = bool(cfg.get(key, default))
        elif isinstance(default, int) and not isinstance(default, bool):
            try:
                cfg[key] = int(cfg.get(key, default))
            except Exception:
                cfg[key] = default
        elif isinstance(default, float):
            try:
                cfg[key] = float(cfg.get(key, default))
            except Exception:
                cfg[key] = default
    return cfg


def load_allowlist() -> dict[str, Any]:
    data = read_json(ALLOWLIST_FILE, {"version": 1, "capstone_approvals": [], "flag_exemptions": []})
    if not isinstance(data, dict):
        return {"version": 1, "capstone_approvals": [], "flag_exemptions": []}
    data.setdefault("capstone_approvals", [])
    data.setdefault("flag_exemptions", [])
    return data


def load_approvals() -> dict[str, Any]:
    data = read_json(APPROVALS_FILE, {"version": 1, "approvals": []})
    if not isinstance(data, dict):
        return {"version": 1, "approvals": []}
    data.setdefault("approvals", [])
    return data


def load_state() -> dict[str, Any]:
    data = read_json(STATE_FILE, {"version": 1})
    if not isinstance(data, dict):
        data = {"version": 1}
    data.setdefault("version", 1)
    data.setdefault("theorem_first_seen", {})
    return data


def save_state(state: dict[str, Any], dry_run: bool) -> None:
    write_json(STATE_FILE, state, dry_run=dry_run)


def load_cooldown() -> dict[str, Any]:
    data = read_json(COOLDOWN_FILE, {"version": 1, "entries": {}})
    if not isinstance(data, dict):
        data = {"version": 1, "entries": {}}
    data.setdefault("version", 1)
    data.setdefault("entries", {})
    return data


def save_cooldown(data: dict[str, Any], dry_run: bool) -> None:
    write_json(COOLDOWN_FILE, data, dry_run=dry_run)


def append_alert(category: str, details: dict[str, Any], dry_run: bool = False) -> None:
    line = (
        f"TASTE ALERT category={category} ts={utc_now()}\n"
        f"{json.dumps(details, sort_keys=True)}\n"
    )
    if dry_run:
        print("[taste] dry-run alert:", line.rstrip(), file=sys.stderr)
        return
    ALERT_LOG.parent.mkdir(parents=True, exist_ok=True)
    with ALERT_LOG.open("a", encoding="utf-8") as fh:
        fh.write(line)


def existing_queue_entries() -> dict[str, dict[str, Any]]:
    entries: dict[str, dict[str, Any]] = {}
    if not QUEUE_FILE.exists():
        return entries
    for line in QUEUE_FILE.read_text(encoding="utf-8", errors="ignore").splitlines():
        if not line.strip():
            continue
        try:
            item = json.loads(line)
        except Exception:
            continue
        qid = item.get("id")
        if isinstance(qid, str):
            entries[qid] = item
    return entries


def append_queue(entry: dict[str, Any], dry_run: bool = False) -> bool:
    qid = entry.get("id")
    if not isinstance(qid, str):
        return False
    if qid in existing_queue_entries():
        print(f"[taste] queue already has {qid}", flush=True)
        return False
    if dry_run:
        print(f"[taste] dry-run queue {qid} {entry.get('flag')}", flush=True)
        return True
    with QUEUE_FILE.open("a", encoding="utf-8") as fh:
        fh.write(json.dumps(entry, sort_keys=True) + "\n")
    print(f"[taste] queued {qid}", flush=True)
    return True


@contextlib.contextmanager
def pid_lock(enabled: bool = True):
    if not enabled:
        yield
        return
    pid = os.getpid()
    if PID_FILE.exists():
        try:
            old = int(PID_FILE.read_text().strip())
            os.kill(old, 0)
        except ProcessLookupError:
            pass
        except Exception:
            pass
        else:
            raise TasteError(f"taste curator already running with pid {old}")
    PID_FILE.write_text(str(pid), encoding="utf-8")
    try:
        yield
    finally:
        try:
            if PID_FILE.read_text().strip() == str(pid):
                PID_FILE.unlink()
        except Exception:
            pass


def tracked_dirty_paths() -> list[str]:
    out = git("status", "--porcelain", capture=True).stdout
    dirty: list[str] = []
    for raw in out.splitlines():
        if not raw or raw[:2] == "??":
            continue
        path = raw[3:] if len(raw) > 3 else ""
        if path == ".pipeline_parallel.json":
            continue
        dirty.append(raw)
    return dirty


def current_branch() -> str:
    return git("rev-parse", "--abbrev-ref", "HEAD", capture=True).stdout.strip()


def initial_diff_base(head: str) -> str:
    try:
        return git("rev-parse", "HEAD~25", capture=True).stdout.strip()
    except Exception:
        return head


def sync_phase(state: dict[str, Any], dry_run: bool) -> ChangedArtifacts | None:
    if dry_run:
        concrete = sorted((REPO_ROOT / "papers" / "bedc" / "parts" / "concrete_instances").glob("*.tex"))
        lean = sorted((REPO_ROOT / "lean4" / "BEDC" / "Derived").rglob("*.lean"))
        return ChangedArtifacts("dryrun", "dryrun", concrete[:200], lean[:400], [], 0)

    branch = current_branch()
    if branch != BASE_BRANCH:
        print(f"[taste] not on {BASE_BRANCH} (on {branch}); skipping", file=sys.stderr)
        return None

    dirty = tracked_dirty_paths()
    if dirty:
        print(f"[taste] tracked working tree dirt; skipping cycle: {dirty[:5]}", file=sys.stderr)
        return None

    git("fetch", "origin", BASE_BRANCH, check=False)
    merge = git("merge", "--ff-only", f"origin/{BASE_BRANCH}", check=False, capture=True)
    if merge.returncode != 0:
        append_alert("sync_failed", {"stderr": tail(merge.stderr or merge.stdout or "")})
        return None

    head = git("rev-parse", "HEAD", capture=True).stdout.strip()
    base = str(state.get("last_seen_sha") or "")
    if not base:
        base = initial_diff_base(head)
    diff = git("diff", "--name-status", f"{base}..{head}", check=False, capture=True)
    paths: list[str] = []
    for line in (diff.stdout or "").splitlines():
        parts = line.split("\t")
        if not parts:
            continue
        status = parts[0]
        path = parts[-1]
        if status.startswith("D"):
            continue
        paths.append(path)
    concrete = [
        REPO_ROOT / p for p in paths
        if p.startswith("papers/bedc/parts/concrete_instances/") and p.endswith(".tex")
    ]
    lean = [
        REPO_ROOT / p for p in paths
        if p.startswith("lean4/BEDC/Derived/") and p.endswith(".lean")
    ]
    log = git("log", "--format=%s", f"{base}..{head}", check=False, capture=True)
    subjects = [s for s in (log.stdout or "").splitlines() if s.strip()]
    return ChangedArtifacts(head, base, concrete, lean, subjects, max(len(subjects), 0))


def chapter_slug_from_path(path: Path) -> str:
    relp = rel(path)
    prefix = "papers/bedc/parts/concrete_instances/"
    rest = relp[len(prefix):] if relp.startswith(prefix) else path.name
    parts = rest.split("/")
    if len(parts) > 1:
        return parts[0]
    name = Path(parts[0]).stem
    m = re.match(r"^\d+_(.+?)_namecert_construction$", name)
    if m:
        return m.group(1)
    return re.sub(r"_namecert_construction$", "", name)


def extract_origin(text: str) -> str | None:
    m = re.search(r"\\origin\{([^}]+)\}", text)
    return m.group(1).strip() if m else None


def is_hub_only_tex(text: str) -> bool:
    if "\\begin{theorem}" in text or "\\begin{definition}" in text or "\\chapter{" in text:
        return False
    meaningful = [
        line.strip() for line in text.splitlines()
        if line.strip() and not line.strip().startswith("%")
    ]
    if not meaningful:
        return True
    structural = 0
    for line in meaningful:
        if (
            line.startswith("\\input{")
            or line.startswith("\\closureat{")
            or line.startswith("\\label{")
            or line.startswith("\\section{")
            or line.startswith("\\subsection{")
        ):
            structural += 1
    return structural >= max(1, len(meaningful) - 2)


def is_origin_bearing_chapter(path: Path, text: str) -> bool:
    name = path.name
    if "\\origin{" in text:
        return True
    if "\\chapter{" in text:
        return True
    if name.endswith("_namecert_construction.tex"):
        return True
    return False


def load_carrier_iso(dry_run: bool = False) -> dict[str, Any]:
    if dry_run:
        return {"phase1_buckets": [], "phase2_buckets": [], "phase3_clusters": []}
    res = run(
        ["python3", "lean4/scripts/bedc_ci.py", "carrier-isomorphism", "--json"],
        check=False,
        capture=True,
        timeout=TIMEOUTS["carrier"],
    )
    if res.returncode != 0:
        append_alert("carrier_isomorphism_failed", {"stderr": tail(res.stderr or res.stdout or "")})
        return {"phase1_buckets": [], "phase2_buckets": [], "phase3_clusters": []}
    try:
        return json.loads(res.stdout)
    except Exception as exc:
        append_alert("carrier_isomorphism_parse_failed", {"error": str(exc)})
        return {"phase1_buckets": [], "phase2_buckets": [], "phase3_clusters": []}


def iter_carrier_buckets(carrier: dict[str, Any]) -> list[tuple[str, dict[str, Any]]]:
    buckets: list[tuple[str, dict[str, Any]]] = []
    for key in ("phase1_buckets", "phase2_buckets", "phase3_clusters"):
        value = carrier.get(key, [])
        if not isinstance(value, list):
            continue
        for bucket in value:
            if isinstance(bucket, dict):
                buckets.append((key, bucket))
    return buckets


def bucket_members(bucket: dict[str, Any]) -> list[dict[str, Any]]:
    members = bucket.get("members") or bucket.get("cluster") or bucket.get("carriers") or []
    return [m for m in members if isinstance(m, dict)]


def carrier_member_index(carrier: dict[str, Any]) -> dict[str, list[tuple[str, dict[str, Any], dict[str, Any]]]]:
    index: dict[str, list[tuple[str, dict[str, Any], dict[str, Any]]]] = {}
    for phase, bucket in iter_carrier_buckets(carrier):
        for member in bucket_members(bucket):
            name = str(member.get("name") or "")
            if not name:
                continue
            index.setdefault(slug_key(name), []).append((phase, bucket, member))
    return index


def detect_origin_classification(
    artifacts: ChangedArtifacts,
    carrier: dict[str, Any],
    cfg: dict[str, Any],
) -> list[Finding]:
    findings: list[Finding] = []
    index = carrier_member_index(carrier)
    member_min = int(cfg["MISLABELED_COMPOSITE_BUCKET_MEMBER_MIN"])
    overlap_min = int(cfg["MISLABELED_COMPOSITE_FIELD_OVERLAP_MIN"])
    seen: set[tuple[str, str]] = set()
    for path in artifacts.concrete_files:
        if not path.exists():
            continue
        text = read_text(path)
        if is_hub_only_tex(text):
            continue
        if not is_origin_bearing_chapter(path, text):
            continue
        origin = extract_origin(text)
        slug = chapter_slug_from_path(path)
        if origin is None:
            findings.append(Finding(
                "missing_origin",
                slug,
                "medium",
                {"detected_origin": None},
                "add a valid origin tag after checking the chapter lineage",
                paper_file=rel(path),
                commit=artifacts.head,
            ))
            continue
        if origin not in {"human", "ai", "ai-composite"}:
            findings.append(Finding(
                "invalid_origin",
                slug,
                "medium",
                {"detected_origin": origin},
                "replace the origin tag with human, ai, or ai-composite",
                paper_file=rel(path),
                commit=artifacts.head,
            ))
            continue
        if origin != "ai":
            continue
        candidates = index.get(slug_key(slug), [])
        for phase, bucket, member in candidates:
            members = bucket_members(bucket)
            if len(members) < member_min:
                continue
            fields = set(str(x) for x in member.get("field_names", []) if x)
            max_overlap = 0
            peers: list[str] = []
            for peer in members:
                pname = str(peer.get("name") or "")
                if pname == member.get("name"):
                    continue
                overlap = len(fields & set(str(x) for x in peer.get("field_names", []) if x))
                max_overlap = max(max_overlap, overlap)
                peers.append(pname)
            same_shape = len(members) >= member_min
            if max_overlap >= overlap_min or same_shape:
                key = ("mislabeled_composite", slug)
                if key in seen:
                    continue
                seen.add(key)
                findings.append(Finding(
                    "mislabeled_composite",
                    slug,
                    "high" if phase in {"phase2_buckets", "phase3_clusters"} else "medium",
                    {
                        "origin": origin,
                        "carrier_name": member.get("name"),
                        "carrier_file": member.get("file"),
                        "bucket_phase": phase,
                        "bucket_member_count": len(members),
                        "shared_field_overlap_max": max_overlap,
                        "bucket_members": peers[:12],
                        "target_origin": "ai-composite",
                    },
                    "review whether the chapter is a composite carrier surface; likely origin ai-composite",
                    paper_file=rel(path),
                    lean_files=[str(member.get("file"))] if member.get("file") else [],
                    commit=artifacts.head,
                ))
                break
    return findings


def capstone_allowlisted(slug: str, allowlist: dict[str, Any]) -> bool:
    for rec in allowlist.get("capstone_approvals", []):
        if not isinstance(rec, dict):
            continue
        if slug_key(str(rec.get("chapter_slug", ""))) == slug_key(slug):
            return True
    return False


def flag_exempted(flag: str, target: str, allowlist: dict[str, Any]) -> bool:
    now = datetime.now(timezone.utc)
    for rec in allowlist.get("flag_exemptions", []):
        if not isinstance(rec, dict):
            continue
        if rec.get("flag") != flag:
            continue
        rec_target = str(rec.get("target", ""))
        if rec_target and slug_key(rec_target) not in slug_key(target):
            continue
        expires = rec.get("expires_at")
        if expires:
            try:
                expires_dt = datetime.fromisoformat(str(expires).replace("Z", "+00:00"))
                if expires_dt < now:
                    continue
            except Exception:
                pass
        return True
    return False


def detect_capstone_source(
    artifacts: ChangedArtifacts,
    allowlist: dict[str, Any],
) -> list[Finding]:
    findings: list[Finding] = []
    subject_blob = "\n".join(artifacts.subjects).lower()
    subject_hit = "carrier-isomorphism" in subject_blob or "capstone" in subject_blob
    for path in artifacts.concrete_files:
        if not path.exists():
            continue
        slug = chapter_slug_from_path(path)
        name_hit = "capstone" in slug.lower() or "carrier_isomorphism" in slug.lower()
        if not (subject_hit or name_hit):
            continue
        if capstone_allowlisted(slug, allowlist):
            continue
        findings.append(Finding(
            "unauthorized_capstone",
            slug,
            "high",
            {
                "subject_hit": subject_hit,
                "name_hit": name_hit,
                "allowlist_hit": False,
                "recent_subjects": artifacts.subjects[:8],
            },
            "operator approve in taste_allowlist.json or stage through review",
            paper_file=rel(path),
            commit=artifacts.head,
        ))
    return findings


def load_inventory(dry_run: bool = False) -> dict[str, Any]:
    if dry_run:
        return {"declarations": []}
    res = run(
        ["python3", "lean4/scripts/bedc_ci.py", "inventory", "--json"],
        check=False,
        capture=True,
        timeout=TIMEOUTS["inventory"],
    )
    if res.returncode != 0:
        append_alert("inventory_failed", {"stderr": tail(res.stderr or res.stdout or "")})
        return {"declarations": []}
    try:
        return json.loads(res.stdout)
    except Exception as exc:
        append_alert("inventory_parse_failed", {"error": str(exc)})
        return {"declarations": []}


def changed_public_theorems(artifacts: ChangedArtifacts, inventory: dict[str, Any]) -> list[dict[str, Any]]:
    changed = {rel(p) for p in artifacts.lean_files}
    out: list[dict[str, Any]] = []
    for decl in inventory.get("declarations", []):
        if not isinstance(decl, dict):
            continue
        if decl.get("kind") != "theorem" or decl.get("is_private"):
            continue
        file = str(decl.get("file", ""))
        if file in changed:
            out.append(decl)
    return out


def gather_reference_corpus() -> list[tuple[str, str]]:
    files: list[Path] = []
    files.extend((REPO_ROOT / "papers" / "bedc" / "parts").rglob("*.tex"))
    files.extend((REPO_ROOT / "lean4" / "BEDC").rglob("*.lean"))
    corpus: list[tuple[str, str]] = []
    for path in files:
        try:
            corpus.append((rel(path), read_text(path)))
        except Exception:
            continue
    return corpus


def count_downstream_refs(target: str, own_file: str, corpus: list[tuple[str, str]]) -> int:
    short = target.split(".")[-1]
    count = 0
    for path, text in corpus:
        hits = text.count(target) + text.count(short)
        if path == own_file:
            hits = max(0, hits - 1)
        count += hits
    return count


def detect_isolated_theorems(
    artifacts: ChangedArtifacts,
    inventory: dict[str, Any],
    state: dict[str, Any],
    allowlist: dict[str, Any],
    cfg: dict[str, Any],
) -> list[Finding]:
    findings: list[Finding] = []
    grace = int(cfg["ISOLATED_THEOREM_GRACE_ROUNDS"])
    first_seen = state.setdefault("theorem_first_seen", {})
    corpus = gather_reference_corpus()
    for decl in changed_public_theorems(artifacts, inventory):
        target = str(decl.get("qualified_name") or "")
        if not target:
            continue
        if target not in first_seen:
            first_seen[target] = {
                "commit": artifacts.head,
                "round": int(state.get("round_counter", 0)),
                "first_seen_at": utc_now(),
                "file": decl.get("file"),
            }
        seen_round = int(first_seen[target].get("round", 0))
        age = max(0, int(state.get("round_counter", 0)) - seen_round)
        refs = count_downstream_refs(target, str(decl.get("file", "")), corpus)
        if refs > 0 or age < grace:
            continue
        if flag_exempted("isolated_theorem", target, allowlist):
            continue
        findings.append(Finding(
            "isolated_theorem",
            chapter_slug=Path(str(decl.get("file", ""))).parent.name.replace("Up", "").lower(),
            severity="medium",
            evidence={"downstream_refs": refs, "file": decl.get("file"), "line": decl.get("line")},
            recommended_action="review whether theorem is staging-only or needs a downstream consumer",
            lean_target=target,
            round_age=age,
            commit=artifacts.head,
        ))
    return findings


def label_set(text: str) -> set[str]:
    return set(re.findall(r"\\label\{([^}]+)\}", text))


def ref_targets(text: str) -> list[str]:
    targets: list[str] = []
    for m in re.finditer(r"\\(?:auto)?ref\{([^}]+)\}|\\cref\{([^}]+)\}", text):
        value = next((g for g in m.groups() if g), "")
        targets.extend(t.strip() for t in value.split(",") if t.strip())
    return targets


def target_stem(label: str) -> str:
    if ":" in label:
        label = label.split(":", 1)[1]
    parts = [p for p in re.split(r"[-_]+", label) if p]
    return "-".join(parts[:2]) if parts else label


def entropy(values: list[str]) -> float:
    if not values:
        return 0.0
    counts: dict[str, int] = {}
    for v in values:
        counts[v] = counts.get(v, 0) + 1
    total = len(values)
    return -sum((c / total) * math.log2(c / total) for c in counts.values())


def boilerplate_score(text: str) -> float:
    low = re.sub(r"\s+", " ", text.lower())
    phrase_hits = sum(1 for phrase in BOILERPLATE_PHRASES if phrase in low)
    phrase_score = min(1.0, phrase_hits / 6.0)
    paras = [p.strip() for p in re.split(r"\n\s*\n", low) if len(p.strip()) > 80]
    sim = 0.0
    for para in paras[:20]:
        for template in TEMPLATE_PARAGRAPHS:
            sim = max(sim, difflib.SequenceMatcher(None, para[:600], template.lower()).ratio())
    return round(max(phrase_score, sim), 3)


def detect_low_entropy_templates(
    artifacts: ChangedArtifacts,
    allowlist: dict[str, Any],
    cfg: dict[str, Any],
) -> list[Finding]:
    findings: list[Finding] = []
    min_targets = int(cfg["LOW_ENTROPY_AUTOREF_MIN_TARGETS"])
    min_entropy = float(cfg["LOW_ENTROPY_SHANNON_MIN"])
    min_boiler = float(cfg["LOW_ENTROPY_BOILERPLATE_SCORE_MIN"])
    seen: set[str] = set()
    for path in artifacts.concrete_files:
        if not path.exists() or rel(path) in seen:
            continue
        seen.add(rel(path))
        text = read_text(path)
        if is_hub_only_tex(text):
            continue
        own = label_set(text)
        refs = [r for r in ref_targets(text) if r not in own]
        stems = [target_stem(r) for r in refs]
        distinct = len(set(stems))
        h = entropy(stems)
        score = boilerplate_score(text)
        slug = chapter_slug_from_path(path)
        if flag_exempted("low_entropy_template", slug, allowlist):
            continue
        if distinct < min_targets and h < min_entropy and score >= min_boiler:
            findings.append(Finding(
                "low_entropy_template",
                slug,
                "medium",
                {
                    "distinct_autoref_targets": distinct,
                    "entropy": round(h, 3),
                    "boilerplate_score": score,
                    "autoref_targets": refs[:12],
                },
                "human review for wrapper/template multiplication",
                paper_file=rel(path),
                commit=artifacts.head,
            ))
    return findings


def assign_ids(findings: list[Finding], commit: str) -> None:
    short = commit[:8] if commit and commit != "dryrun" else "dryrun"
    for finding in findings:
        finding.commit = finding.commit or commit
        finding.id = f"{finding.flag}:{finding.chapter_slug}:{short}"


def cooldown_action(finding: Finding, cfg: dict[str, Any], dry_run: bool) -> str:
    data = load_cooldown()
    entries = data.setdefault("entries", {})
    key = f"{finding.flag}:{finding.chapter_slug}"
    now = utc_now()
    rec = entries.get(key)
    if not isinstance(rec, dict):
        entries[key] = {
            "first_seen": now,
            "last_seen": now,
            "count": 1,
            "last_action": "queued_review",
            "last_commit": finding.commit,
        }
        save_cooldown(data, dry_run)
        return "queue"
    rec["last_seen"] = now
    rec["count"] = int(rec.get("count", 0)) + 1
    rec["last_commit"] = finding.commit
    save_cooldown(data, dry_run)
    last = str(rec.get("last_seen", now))
    try:
        last_dt = datetime.fromisoformat(last.replace("Z", "+00:00"))
        age_hours = (datetime.now(timezone.utc) - last_dt).total_seconds() / 3600.0
    except Exception:
        age_hours = 0.0
    if age_hours <= float(cfg["COOLDOWN_HOURS"]) and int(rec.get("count", 0)) >= 2:
        rec["last_action"] = "alert_only"
        save_cooldown(data, dry_run)
        return "alert"
    rec["last_action"] = "queued_review"
    save_cooldown(data, dry_run)
    return "queue"


def finding_to_evidence(finding: Finding) -> dict[str, Any]:
    payload: dict[str, Any] = {
        "id": finding.id,
        "flag": finding.flag,
        "chapter_slug": finding.chapter_slug,
        "paper_file": finding.paper_file,
        "lean_files": finding.lean_files,
        "evidence": finding.evidence,
    }
    if finding.lean_target:
        payload["lean_target"] = finding.lean_target
    if finding.round_age is not None:
        payload["round_age"] = finding.round_age
    if finding.commit:
        payload["commit"] = finding.commit
    return payload


def entry_to_evidence(entry: dict[str, Any]) -> dict[str, Any]:
    payload: dict[str, Any] = {
        "id": entry.get("id"),
        "flag": entry.get("flag"),
        "chapter_slug": entry.get("chapter_slug"),
        "paper_file": entry.get("paper_file"),
        "lean_files": entry.get("lean_files", []),
        "evidence": entry.get("evidence", {}),
    }
    if entry.get("lean_target"):
        payload["lean_target"] = entry.get("lean_target")
    if entry.get("round_age") is not None:
        payload["round_age"] = entry.get("round_age")
    if entry.get("commit"):
        payload["commit"] = entry.get("commit")
    return payload


def rule_evolution_done_ids(state: dict[str, Any]) -> set[str]:
    raw = state.setdefault("rule_evolution_done_ids", [])
    if not isinstance(raw, list):
        state["rule_evolution_done_ids"] = []
        return set()
    return {str(x) for x in raw if x}


def mark_rule_evolution_done(state: dict[str, Any], entries: list[dict[str, Any]], commit_sha: str | None) -> None:
    done = rule_evolution_done_ids(state)
    for entry in entries:
        qid = str(entry.get("id") or "")
        if qid:
            done.add(qid)
    state["rule_evolution_done_ids"] = sorted(done)[-5000:]
    state["last_rule_evolution_at"] = utc_now()
    state["last_rule_evolution_commit"] = commit_sha


def top_entry_cluster(entries: list[dict[str, Any]], state: dict[str, Any]) -> tuple[str, list[dict[str, Any]]] | None:
    done = rule_evolution_done_ids(state)
    clusters: dict[str, list[dict[str, Any]]] = {}
    for entry in entries:
        qid = str(entry.get("id") or "")
        if qid and qid in done:
            continue
        flag = str(entry.get("flag") or "")
        if flag in AUTO_FIXABLE_FLAGS:
            clusters.setdefault(flag, []).append(entry)
    if not clusters:
        return None
    flag, cluster = max(clusters.items(), key=lambda item: (len(item[1]), item[0]))
    return flag, cluster[:MAX_RULE_EVOLUTION_CLUSTER_SIZE]


def build_rule_evolution_prompt(flag: str, evidence: list[dict[str, Any]]) -> str:
    cluster = {
        "flag": flag,
        "finding_count": len(evidence),
        "findings": evidence,
    }
    return (
        META_PROMPT_RULE_EVOLUTION
        + "\nCluster evidence:\n```json\n"
        + json.dumps(cluster, indent=2, sort_keys=True)
        + "\n```\n"
    )


def dispatch_autofix_queue(
    entries: list[dict[str, Any]],
    cfg: dict[str, Any],
    state: dict[str, Any],
    dry_run: bool = False,
) -> bool:
    if not cfg.get("AUTO_FIX_WITHOUT_CONFIRMATION", False):
        print("[taste] rule evolution disabled", flush=True)
        return False
    if int(cfg.get("MAX_AUTO_FIXES_PER_CYCLE", 1)) <= 0:
        print("[taste] rule evolution cap is zero", flush=True)
        return False
    cluster = top_entry_cluster(entries, state)
    if cluster is None:
        if dry_run:
            print("[taste] dry-run: no rule evolution cluster available", flush=True)
        return False
    flag, cluster_entries = cluster
    evidence = [entry_to_evidence(entry) for entry in cluster_entries]
    if dry_run:
        print(
            f"[taste] dry-run: would dispatch rule evolution for {flag} "
            f"with {len(evidence)} finding(s)",
            flush=True,
        )
        return False
    ok, msg, _commit_sha = dispatch_rule_evolution(flag, evidence, approval_ids=[])
    if not ok:
        append_alert("rule_evolution_failed", {"flag": flag, "failure_reason": msg})
        print(f"[taste] rule evolution failed for {flag}: {msg}", flush=True)
        return False
    mark_rule_evolution_done(state, cluster_entries, _commit_sha)
    print(f"[taste] rule evolution completed for {flag}: {msg}", flush=True)
    return True


def triage_findings(findings: list[Finding], cfg: dict[str, Any], state: dict[str, Any], dry_run: bool) -> None:
    ts = utc_now()
    queue_entries: list[dict[str, Any]] = list(existing_queue_entries().values())
    for finding in findings:
        action = cooldown_action(finding, cfg, dry_run)
        entry = finding.to_queue_entry(ts)
        if action == "alert":
            append_alert(finding.flag, entry, dry_run=dry_run)
            continue
        append_queue(entry, dry_run=dry_run)
        queue_entries.append(entry)
    dispatch_autofix_queue(queue_entries, cfg, state, dry_run=dry_run)


def command_output_ok(cmd: list[str], cwd: Path, timeout: int) -> tuple[bool, str]:
    try:
        res = run(cmd, cwd=cwd, check=False, capture=True, timeout=timeout)
    except subprocess.TimeoutExpired as exc:
        out = (exc.stdout or "") + (exc.stderr or "")
        if isinstance(out, bytes):
            out = out.decode("utf-8", errors="ignore")
        return False, f"timeout after {timeout}s: {' '.join(cmd)}\n{tail(out)}"
    except Exception as exc:
        return False, f"failed to run {' '.join(cmd)}: {exc}"
    if res.returncode != 0:
        return False, f"rc={res.returncode}: {' '.join(cmd)}\n{tail((res.stdout or '') + (res.stderr or ''))}"
    return True, tail((res.stdout or "") + (res.stderr or ""), 400)


def command_output_no_crash(cmd: list[str], cwd: Path, timeout: int) -> tuple[bool, str]:
    try:
        res = run(cmd, cwd=cwd, check=False, capture=True, timeout=timeout)
    except subprocess.TimeoutExpired as exc:
        out = (exc.stdout or "") + (exc.stderr or "")
        if isinstance(out, bytes):
            out = out.decode("utf-8", errors="ignore")
        return False, f"timeout after {timeout}s: {' '.join(cmd)}\n{tail(out)}"
    except Exception as exc:
        return False, f"failed to run {' '.join(cmd)}: {exc}"
    out = (res.stdout or "") + (res.stderr or "")
    if "Traceback (most recent call last)" in out:
        return False, f"crash: {' '.join(cmd)}\n{tail(out)}"
    return True, f"rc={res.returncode}: {tail(out, 400)}"


def verify_rule_evolution(worktree: Path, touched: list[str]) -> tuple[bool, str]:
    checks: list[tuple[list[str], Path, int]] = [
        (["python3", "-m", "py_compile", "lean4/scripts/bedc_ci.py"], worktree, 60),
    ]
    if "papers/bedc/scripts/phase_paper_gates.py" in touched:
        checks.append((["python3", "-m", "py_compile", "papers/bedc/scripts/phase_paper_gates.py"], worktree, 60))
    if "lean4/scripts/phase_d_lint.py" in touched:
        checks.append((["python3", "-m", "py_compile", "lean4/scripts/phase_d_lint.py"], worktree, 60))
    paper_changed = any(
        p.startswith("papers/bedc/scripts/prompts/") or p == "papers/bedc/scripts/phase_paper_gates.py"
        for p in touched
    )
    lean_changed = any(
        p.startswith("lean4/scripts/prompts/") or p == "lean4/scripts/phase_d_lint.py"
        for p in touched
    )
    if paper_changed:
        checks.append((["make", "check"], worktree / "papers" / "bedc", TIMEOUTS["verify"]))
    if lean_changed:
        checks.append((["lake", "build"], worktree / "lean4", TIMEOUTS["verify"]))
    for cmd, cwd, timeout in checks:
        ok, msg = command_output_ok(cmd, cwd, timeout)
        if not ok:
            return False, msg
    ok, msg = command_output_no_crash(
        ["python3", "lean4/scripts/bedc_ci.py", "audit"],
        worktree,
        TIMEOUTS["verify"],
    )
    if not ok:
        return False, msg
    return True, "verification passed"


def update_approval_status(
    approval_id: str,
    status: str,
    *,
    commit_sha: str | None = None,
    failure_reason: str | None = None,
    push: bool = True,
) -> bool:
    data = load_approvals()
    changed = False
    for rec in data.get("approvals", []):
        if isinstance(rec, dict) and rec.get("id") == approval_id:
            rec["status"] = status
            if status == "done":
                rec["done_at"] = utc_now()
                rec["commit_sha"] = commit_sha
                rec["failure_reason"] = None
            elif status == "failed":
                rec["failure_reason"] = failure_reason
            changed = True
            break
    if not changed:
        append_alert("approval_update_missing", {"id": approval_id, "status": status})
        return False
    write_json(APPROVALS_FILE, data)
    git("add", rel(APPROVALS_FILE))
    msg = f"taste: mark approval {status} {short_hash(approval_id)}"
    commit = git("commit", "-m", msg, check=False, capture=True)
    if commit.returncode != 0:
        append_alert("approval_status_commit_failed", {"id": approval_id, "stderr": tail(commit.stderr)})
        return False
    if push:
        pushed = git("push", "origin", BASE_BRANCH, check=False, capture=True)
        if pushed.returncode != 0:
            append_alert("approval_status_push_failed", {"id": approval_id, "stderr": tail(pushed.stderr)})
            return False
    return True


def existing_rule_evolution_files(worktree: Path) -> set[str]:
    allowed = set(RULE_EVOLUTION_ALLOWED_FILES)
    for path in RULE_EVOLUTION_OPTIONAL_FILES:
        if (worktree / path).exists():
            allowed.add(path)
    return allowed


def touched_files_since(worktree: Path, base_sha: str) -> list[str]:
    diff = run(["git", "diff", "--name-only", f"{base_sha}..HEAD"], cwd=worktree, check=False, capture=True, timeout=30)
    touched = {p for p in diff.stdout.splitlines() if p.strip()}
    status = run(["git", "status", "--porcelain"], cwd=worktree, check=False, capture=True, timeout=30)
    for raw in status.stdout.splitlines():
        if not raw.strip():
            continue
        path = raw[3:] if len(raw) > 3 else raw
        if " -> " in path:
            _old, path = path.split(" -> ", 1)
        touched.add(path.strip())
    return sorted(touched)


def validate_rule_evolution_touched(worktree: Path, touched: list[str]) -> tuple[bool, str]:
    allowed = existing_rule_evolution_files(worktree)
    bad: list[str] = []
    for path in touched:
        if any(path == prefix or path.startswith(prefix) for prefix in RULE_EVOLUTION_FORBIDDEN_PREFIXES):
            bad.append(path)
            continue
        if path not in allowed:
            bad.append(path)
    if bad:
        return False, "rule evolution touched forbidden path(s): " + ", ".join(bad[:20])
    return True, "whitelist passed"


def merge_rule_evolution_worktree(worktree: Path, branch: str, flag: str, cluster_key: str) -> tuple[bool, str, str | None]:
    fetch = git("fetch", "origin", BASE_BRANCH, check=False, capture=True)
    if fetch.returncode != 0:
        return False, f"fetch failed: {tail(fetch.stderr)}", None
    merge_base = git("merge", f"origin/{BASE_BRANCH}", check=False, capture=True)
    if merge_base.returncode != 0:
        return False, f"base merge failed: {tail(merge_base.stderr or merge_base.stdout)}", None
    merge = git(
        "merge",
        "--no-ff",
        branch,
        "-m",
        f"taste: rule evolution {sanitize_branch_piece(flag)} {cluster_key}",
        check=False,
        capture=True,
    )
    if merge.returncode != 0:
        git("merge", "--abort", check=False, capture=True)
        return False, f"worktree merge failed: {tail(merge.stderr or merge.stdout)}", None
    commit_sha = git("rev-parse", "HEAD", capture=True).stdout.strip()
    push = git("push", "origin", BASE_BRANCH, check=False, capture=True)
    if push.returncode != 0:
        return False, f"push failed: {tail(push.stderr or push.stdout)}", commit_sha
    return True, "merged and pushed", commit_sha


def dispatch_rule_evolution(
    flag: str,
    evidence: list[dict[str, Any]],
    *,
    approval_ids: list[str],
) -> tuple[bool, str, str | None]:
    cluster_key = short_hash(json.dumps({"flag": flag, "evidence": evidence}, sort_keys=True))
    piece = sanitize_branch_piece(f"taste-evolve-{flag}-{cluster_key}")
    worktree = Path("/tmp") / f"wt-{piece}"
    branch = f"taste/evolve-{sanitize_branch_piece(flag)}-{cluster_key}"
    if worktree.exists():
        shutil.rmtree(worktree)
    base_sha = git("rev-parse", "HEAD", capture=True).stdout.strip()
    add = git("worktree", "add", "-b", branch, str(worktree), base_sha, check=False, capture=True)
    if add.returncode != 0:
        return False, f"worktree add failed: {tail(add.stderr or add.stdout)}", None
    try:
        prompt = build_rule_evolution_prompt(flag, evidence)
        if approval_ids:
            prompt += "\nConfirmed approval ids:\n```json\n" + json.dumps(approval_ids, indent=2) + "\n```\n"
        res = run(
            [CODEX_PATH, "exec", "--dangerously-bypass-approvals-and-sandbox", "-C", str(worktree), prompt],
            cwd=worktree,
            check=False,
            capture=True,
            timeout=TIMEOUTS["codex"],
        )
        if res.returncode != 0:
            return False, f"codex failed rc={res.returncode}: {tail((res.stdout or '') + (res.stderr or ''))}", None
        touched = touched_files_since(worktree, base_sha)
        if not touched:
            dirty = run(["git", "status", "--porcelain"], cwd=worktree, check=False, capture=True, timeout=30).stdout
            return False, f"codex made no committed changes; dirty={tail(dirty)}", None
        dirty = run(["git", "status", "--porcelain"], cwd=worktree, check=False, capture=True, timeout=30).stdout
        if dirty.strip():
            return False, f"codex left uncommitted changes: {tail(dirty)}", None
        ok, msg = validate_rule_evolution_touched(worktree, touched)
        if not ok:
            return False, msg, None
        ok, msg = verify_rule_evolution(worktree, touched)
        if not ok:
            return False, msg, None
        ok, msg, commit_sha = merge_rule_evolution_worktree(worktree, branch, flag, cluster_key)
        return ok, msg, commit_sha
    finally:
        git("worktree", "remove", "--force", str(worktree), check=False, capture=True)
        git("branch", "-D", branch, check=False, capture=True)


def process_confirmed_approvals(cfg: dict[str, Any], dry_run: bool) -> int:
    if dry_run:
        print("[taste] dry-run: skipping confirmed rule evolution execution", flush=True)
        return 0
    data = load_approvals()
    queue = existing_queue_entries()
    cap = int(cfg["MAX_AUTO_FIXES_PER_CYCLE"])
    confirmed: list[tuple[dict[str, Any], dict[str, Any]]] = []
    for approval in data.get("approvals", []):
        if not isinstance(approval, dict) or approval.get("status") != "confirmed":
            continue
        qid = str(approval.get("id") or "")
        if not qid:
            continue
        entry = queue.get(qid)
        if not entry:
            reason = "queue entry id not found"
            update_approval_status(qid, "failed", failure_reason=reason, push=False)
            append_alert("confirmed_rule_evolution_failed", {"id": qid, "failure_reason": reason})
            continue
        flag = str(entry.get("flag") or approval.get("flag") or "")
        if flag not in AUTO_FIXABLE_FLAGS:
            reason = f"flag is not rule-evolution auto-fixable: {flag}"
            update_approval_status(qid, "failed", failure_reason=reason, push=False)
            append_alert("confirmed_rule_evolution_failed", {"id": qid, "failure_reason": reason})
            continue
        confirmed.append((entry, approval))
    if not confirmed or cap <= 0:
        return 0
    clusters: dict[str, list[tuple[dict[str, Any], dict[str, Any]]]] = {}
    for entry, approval in confirmed:
        flag = str(entry.get("flag") or approval.get("flag") or "")
        clusters.setdefault(flag, []).append((entry, approval))
    flag, cluster = max(clusters.items(), key=lambda item: (len(item[1]), item[0]))
    cluster = cluster[:MAX_RULE_EVOLUTION_CLUSTER_SIZE]
    approval_ids = [str(approval.get("id") or entry.get("id") or "") for entry, approval in cluster]
    evidence = [entry_to_evidence(entry) for entry, _approval in cluster]
    print(f"[taste] executing confirmed rule evolution {flag} count={len(cluster)}", flush=True)
    ok, msg, commit_sha = dispatch_rule_evolution(flag, evidence, approval_ids=approval_ids)
    for qid in approval_ids:
        if not qid:
            continue
        if ok:
            update_approval_status(qid, "done", commit_sha=commit_sha, push=False)
        else:
            update_approval_status(qid, "failed", failure_reason=msg, push=False)
            append_alert("confirmed_rule_evolution_failed", {"id": qid, "failure_reason": msg})
    if ok:
        pushed = git("push", "origin", BASE_BRANCH, check=False, capture=True)
        if pushed.returncode != 0:
            append_alert("approval_status_push_failed", {"ids": approval_ids, "stderr": tail(pushed.stderr)})
    return min(1, cap)


def detect_all(
    artifacts: ChangedArtifacts,
    state: dict[str, Any],
    cfg: dict[str, Any],
    dry_run: bool,
) -> list[Finding]:
    allowlist = load_allowlist()
    carrier = load_carrier_iso(dry_run=dry_run)
    inventory = load_inventory(dry_run=dry_run)
    findings: list[Finding] = []
    findings.extend(detect_origin_classification(artifacts, carrier, cfg))
    findings.extend(detect_capstone_source(artifacts, allowlist))
    findings.extend(detect_isolated_theorems(artifacts, inventory, state, allowlist, cfg))
    with ThreadPoolExecutor(max_workers=4) as pool:
        future = pool.submit(detect_low_entropy_templates, artifacts, allowlist, cfg)
        findings.extend(future.result(timeout=TIMEOUTS["scan"]))
    assign_ids(findings, artifacts.head)
    return findings


def cycle(dry_run: bool = False) -> None:
    cfg = load_config()
    state = load_state()
    print(f"[taste] {utc_now()} tick dry_run={dry_run}", flush=True)
    artifacts = sync_phase(state, dry_run)
    if artifacts is None:
        return
    state["round_counter"] = int(state.get("round_counter", 0)) + max(1, artifacts.local_round)
    findings = detect_all(artifacts, state, cfg, dry_run)
    print(f"[taste] detected {len(findings)} finding(s)", flush=True)
    executed = process_confirmed_approvals(cfg, dry_run)
    if executed:
        print(f"[taste] confirmed rule evolution count={executed}; new finding triage deferred", flush=True)
    else:
        triage_findings(findings, cfg, state, dry_run)
    if not dry_run:
        state["last_seen_sha"] = artifacts.head
        state["last_success_sha"] = artifacts.head
        state["last_cycle_at"] = utc_now()
        save_state(state, dry_run=False)


def main() -> int:
    parser = argparse.ArgumentParser(description="BEDC taste curator daemon")
    parser.add_argument("--once", action="store_true", help="run one cycle and exit")
    parser.add_argument("--dry-run", action="store_true", help="no writes, no git sync, no codex")
    parser.add_argument("--cycle", type=int, default=None, help="run N cycles and exit")
    parser.add_argument("--interval", type=int, default=None, help="cycle interval seconds")
    args = parser.parse_args()

    cfg = load_config()
    interval = int(os.environ.get(
        "TASTE_CURATOR_INTERVAL_SECONDS",
        args.interval if args.interval is not None else cfg["CYCLE_INTERVAL_SECONDS"],
    ))
    cycles = 1 if args.once else args.cycle
    lock_enabled = not args.dry_run
    with pid_lock(enabled=lock_enabled):
        if cycles is not None:
            for i in range(max(0, cycles)):
                print(f"[taste] cycle {i + 1}/{cycles}", flush=True)
                cycle(dry_run=args.dry_run)
                if i + 1 < cycles:
                    time.sleep(interval)
            return 0
        print(f"[taste] starting daemon interval={interval}s", flush=True)
        while True:
            try:
                cycle(dry_run=args.dry_run)
            except Exception as exc:
                append_alert("cycle_exception", {"error": str(exc)}, dry_run=args.dry_run)
                print(f"[taste] cycle exception: {exc}", file=sys.stderr, flush=True)
            time.sleep(interval)


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except KeyboardInterrupt:
        signal.signal(signal.SIGINT, signal.SIG_DFL)
        raise
