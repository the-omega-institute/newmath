#!/usr/bin/env python3
"""Window6<->codon-Q6 bridge daemon supervisor (lean engine).

One cycle:
  1. load bridge registries (claims + experiments)
  2. for each open/needs_rerun claim: run its derivation experiment -> verdict
       certified / refuted / coincidence / needs_derivation
  3. write back registries (atomic) + append to bridge_ledger.jsonl
  4. commit changed files on this branch (lean keep lane), then sleep

Verdict discipline (anti-numerology): a numeric match alone is 'coincidence', never
'certified'. 'certified' requires the experiment to assert a structural forcing argument.

Flags: --once (single cycle, no sleep), --interval-seconds N.
Stop sentinel: tools/window_codon_bridge/.stop
"""
from __future__ import annotations
import argparse, hashlib, json, os, subprocess, sys, tempfile, time
import fcntl
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent           # tools/window_codon_bridge
REPO_ROOT = SCRIPT_DIR.parents[1]                       # bridge worktree root
BIO_REALITY_DIR = REPO_ROOT / "tools" / "bio_reality"
CLAIMS = SCRIPT_DIR / "registries" / "claims.json"
EXPS = SCRIPT_DIR / "registries" / "experiments.json"
SYNC_MANIFEST = SCRIPT_DIR / "registries" / "sync_manifest.json"
SYNCED_DIR = SCRIPT_DIR / "synced"
LEDGER = REPO_ROOT / "papers" / "window_codon_bridge" / "bridge_ledger.jsonl"
STOP = SCRIPT_DIR / ".stop"
STATE_DIR = SCRIPT_DIR / "state"
LOCK = STATE_DIR / "supervisor.lock"
ORACLE_STATE = STATE_DIR / "chatgpt_oracle_state.json"
ORACLE_CONSULTATIONS = SCRIPT_DIR / "oracle_inbox" / "chatgpt_consultations.jsonl"
SELECTION_PACKET = REPO_ROOT / "papers" / "window_codon_bridge" / "data" / "codon_q6_selection_vectors.json"
DEFAULT_INTERVAL = 600.0
ORACLE_COOLDOWN_SECONDS = 21600

sys.path.insert(0, str(SCRIPT_DIR))
import runner  # noqa: E402
sys.path.insert(0, str(BIO_REALITY_DIR))
import oracle_consultation  # noqa: E402


def now_iso() -> str:
    return subprocess.run(["date", "-u", "+%Y-%m-%dT%H:%M:%S+00:00"], capture_output=True, text=True).stdout.strip()


def load(path):
    return json.loads(path.read_text(encoding="utf-8"))


def atomic_write(path: Path, obj):
    fd, tmp = tempfile.mkstemp(dir=str(path.parent), suffix=".tmp")
    with os.fdopen(fd, "w", encoding="utf-8") as fh:
        json.dump(obj, fh, indent=1, ensure_ascii=False)
        fh.write("\n")
    os.replace(tmp, str(path))


def append_ledger(entry: dict):
    LEDGER.parent.mkdir(parents=True, exist_ok=True)
    with open(LEDGER, "a", encoding="utf-8") as fh:
        fh.write(json.dumps(entry, ensure_ascii=False) + "\n")


def append_jsonl(path: Path, entry: dict):
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "a", encoding="utf-8") as fh:
        fh.write(json.dumps(entry, ensure_ascii=False, sort_keys=True) + "\n")


def git(*args) -> subprocess.CompletedProcess:
    return subprocess.run(["git", "-C", str(REPO_ROOT), *args], capture_output=True, text=True)


def git_busy() -> bool:
    return subprocess.run(["pgrep", "-x", "git"], capture_output=True).returncode == 0


def sync_lane() -> dict:
    if git_busy():
        print("[sync] skipped (git busy)", flush=True)
        return {"skipped": "git_busy"}

    manifest = load(SYNC_MANIFEST)
    fetch_branches = [str(b) for b in manifest.get("fetch_branches", [])]
    summary = {"fetched": False, "materialized": [], "pending": [], "fetch_error": False}

    if fetch_branches:
        r = git("fetch", "origin", *fetch_branches)
        summary["fetched"] = r.returncode == 0
        if r.returncode != 0:
            summary["fetch_error"] = True
            print(f"[sync] fetch failed: {((r.stderr or r.stdout) or '').strip()[-300:]}", flush=True)

    for item in manifest.get("materialize", []):
        branch = str(item.get("branch") or "")
        src = str(item.get("src") or "")
        dest = str(item.get("dest") or "")
        if not branch or not src or not dest:
            continue
        r = git("show", f"origin/{branch}:{src}")
        if r.returncode != 0:
            summary["pending"].append(dest)
            print(f"[sync] pending: {branch}:{src}", flush=True)
            continue
        out = r.stdout or ""
        target = SYNCED_DIR / dest
        old = target.read_text(encoding="utf-8") if target.exists() else None
        if old != out:
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(out, encoding="utf-8")
            summary["materialized"].append(dest)
            print(f"[sync] materialized {dest}", flush=True)
    return summary


def publish_lane() -> dict:
    if git_busy():
        print("[publish] skipped (git busy)", flush=True)
        return {"skipped": "git_busy"}

    manifest = load(SYNC_MANIFEST)
    publish_branch = str(manifest.get("publish_branch") or "")
    if not publish_branch:
        return {"pushed": False, "reason": "no_publish_branch"}

    rev = git("rev-parse", "--verify", f"origin/{publish_branch}")
    if rev.returncode != 0:
        count = git("rev-list", "--count", "HEAD")
        ahead = int((count.stdout or "1").strip() or "1") if count.returncode == 0 else 1
    else:
        count = git("rev-list", "--count", f"origin/{publish_branch}..HEAD")
        if count.returncode != 0:
            return {"pushed": False, "error": (count.stderr or count.stdout)[-200:]}
        ahead = int((count.stdout or "0").strip() or "0")
    if ahead <= 0:
        return {"pushed": False, "ahead": 0}

    r = git("push", "origin", f"HEAD:{publish_branch}")
    if r.returncode != 0:
        print(f"[publish] push failed, merging origin/{publish_branch}: {((r.stderr or r.stdout) or '').strip()[-300:]}", flush=True)
        git("fetch", "origin", publish_branch)
        merge = git("merge", "--no-edit", f"origin/{publish_branch}")
        if merge.returncode != 0:
            print(f"[publish] merge failed: {((merge.stderr or merge.stdout) or '').strip()[-300:]}", flush=True)
            return {"pushed": False, "ahead": ahead, "merge_error": True}
        r = git("push", "origin", f"HEAD:{publish_branch}")
    if r.returncode != 0:
        print(f"[publish] push failed: {((r.stderr or r.stdout) or '').strip()[-300:]}", flush=True)
        return {"pushed": False, "ahead": ahead, "push_error": True}
    print(f"[publish] pushed {ahead} commits to origin/{publish_branch}", flush=True)
    return {"pushed": True, "ahead": ahead}


def run_cycle() -> dict:
    cdoc = load(CLAIMS)
    edoc = load(EXPS)
    exp_by_id = {e.get("experiment_id"): e for e in edoc.get("experiments", []) if e.get("experiment_id")}
    summary = {"ts": now_iso(), "executed": 0, "verdicts": {}}
    changed = False
    for claim in cdoc.get("claims", []):
        status = str(claim.get("status") or "open")
        if status not in ("open", "needs_rerun"):
            continue
        spec = exp_by_id.get(str(claim.get("experiment_id") or ""))
        if spec is None:
            continue
        result = runner.run_experiment(spec, REPO_ROOT, int(spec.get("timeout_seconds") or 600))
        verdict = result.get("status", "needs_derivation")
        summary["executed"] += 1
        summary["verdicts"][claim.get("claim_id")] = verdict
        if claim.get("status") != verdict:
            changed = True
        claim["status"] = verdict
        claim.setdefault("history", []).append({
            "ts": summary["ts"], "status": verdict,
            "reason": result.get("reason") or result.get("note") or "derivation verdict",
        })
        append_ledger({
            "id": claim.get("claim_id"), "direction": "bridge->verdict", "item": claim.get("statement", ""),
            "status": verdict, "linked_certificate": None,
            "note": (result.get("reason") or result.get("note") or "")[:500], "ts": summary["ts"],
        })
    if changed:
        atomic_write(CLAIMS, cdoc)
    return summary


def _load_optional_json(path: Path) -> dict:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    return data if isinstance(data, dict) else {}


def _all_claims_terminal(cdoc: dict) -> bool:
    claims = cdoc.get("claims") or []
    return bool(claims) and all(str(claim.get("status") or "open") not in {"open", "needs_rerun"} for claim in claims)


def _latest_reason(claim: dict) -> str:
    history = claim.get("history") or []
    if not history:
        return ""
    latest = history[-1] or {}
    return str(latest.get("reason") or latest.get("note") or "")[:800]


def _selection_packet_summary() -> dict:
    if not SELECTION_PACKET.exists():
        return {"available": False, "path": str(SELECTION_PACKET.relative_to(REPO_ROOT))}
    try:
        data = json.loads(SELECTION_PACKET.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return {"available": False, "path": str(SELECTION_PACKET.relative_to(REPO_ROOT)), "error": "invalid_json"}
    rows = data.get("vectors") if isinstance(data.get("vectors"), list) else []
    fields: dict[str, int] = {}
    for row in rows:
        if not isinstance(row, dict):
            continue
        for key, value in row.items():
            if value is not None:
                fields[str(key)] = fields.get(str(key), 0) + 1
    return {
        "available": True,
        "path": str(SELECTION_PACKET.relative_to(REPO_ROOT)),
        "schema": data.get("schema"),
        "rows": len(rows),
        "has_d_resid4_loading": fields.get("d_resid4_loading", 0) > 0,
        "non_null_fields": dict(sorted(fields.items())),
    }


def _oracle_context(cdoc: dict) -> dict:
    claims = cdoc.get("claims") or []
    status_counts: dict[str, int] = {}
    rows = []
    for claim in claims:
        status = str(claim.get("status") or "open")
        status_counts[status] = status_counts.get(status, 0) + 1
        rows.append(
            {
                "claim_id": claim.get("claim_id"),
                "status": status,
                "statement": claim.get("statement"),
                "latest_reason": _latest_reason(claim),
            }
        )
    edge_claim = next((claim for claim in claims if claim.get("claim_id") == "bridge.genetic_code.edge_defect_axis_cert"), {})
    return {
        "branch": "feat/window-codon-bridge",
        "claim_count": len(claims),
        "status_counts": status_counts,
        "claims": rows,
        "edge_defect_claim": {
            "claim_id": edge_claim.get("claim_id"),
            "status": edge_claim.get("status"),
            "statement": edge_claim.get("statement"),
            "latest_reason": _latest_reason(edge_claim),
        },
        "selection_packet": _selection_packet_summary(),
    }


def _build_chatgpt_oracle_prompt(cdoc: dict) -> tuple[str, str]:
    context = _oracle_context(cdoc)
    topic = "window-codon.edge-defect-independent-residual-axis"
    prompt = "\n".join(
        [
            "You are the ChatGPT oracle deep-reasoning agent for the Window6--Codon-Q6 bridge branch.",
            "This is a candidate-generation consultation, not a truth source. Do not assert final scientific verdicts.",
            "Local deterministic scripts alone assign certified/refuted/coincidence verdicts.",
            "",
            "Current local hard fact:",
            "- Standard genetic code local-edge-hiding deficit is exact: e_in=69, e_max=72.",
            "- The entire deficit is Stop:1 plus Ser:2.",
            "- Stop is treated as a punctuation defect; Ser is the sense-side split defect.",
            "- The current local verdict is coincidence because no independent d_resid4_loading is present and SerSplitDefect does not certify projection onto available axes.",
            "",
            "Task:",
            "Deeply reason about concrete, finite, auditable routes to construct an independent codon-level fourth residual axis d_resid4 for the 61 sense codons.",
            "The route must be explicitly not explained by tRNA supply, f3/ramp, d_perp, GC, wobble, codon-pair effects, mRNA stability, or ribosome dwell.",
            "Focus on routes that can become deterministic local experiment scripts in this repository.",
            "",
            "Required output shape:",
            "1. Give the single strongest next experiment proposal first.",
            "2. Specify data sources, required fields, normalization, exclusion controls, and null model.",
            "3. Specify the exact projection test for u_SerSplit and success/failure criteria.",
            "4. State how the proposal should become a local run_*.py experiment and a claim_id/experiment_id pair.",
            "5. Separate hard graph facts from biological hypotheses.",
            "",
            "Current branch context JSON:",
            json.dumps(context, ensure_ascii=False, sort_keys=True, indent=2),
        ]
    )
    return topic, prompt


def chatgpt_oracle_lane() -> dict:
    cdoc = load(CLAIMS)
    if not _all_claims_terminal(cdoc):
        return {"ran": False, "reason": "claims_not_terminal"}
    state = _load_optional_json(ORACLE_STATE)
    topic, prompt = _build_chatgpt_oracle_prompt(cdoc)
    prompt_hash = hashlib.sha256(prompt.encode("utf-8")).hexdigest()
    last_hash = str(state.get("last_prompt_hash") or "")
    last_epoch = float(state.get("last_attempt_epoch") or 0.0)
    if last_hash == prompt_hash and time.time() - last_epoch < ORACLE_COOLDOWN_SECONDS:
        return {"ran": False, "reason": f"cooldown_active:{int(ORACLE_COOLDOWN_SECONDS - (time.time() - last_epoch))}s"}

    result = oracle_consultation.run_oracle_consultation(
        REPO_ROOT,
        "window-codon",
        topic,
        prompt,
        intended_claim_id="bridge.genetic_code.edge_defect_axis_cert",
        pdf_path=REPO_ROOT / "papers" / "window_codon_bridge" / "main.pdf",
        max_turns=8,
        persist_dir=STATE_DIR / "oracle_sessions",
        server_url="http://127.0.0.1:8769",
        poll_timeout=14400,
        codex_judge_timeout=300,
        existing_conversation_id=str(state.get("conversation_id") or ""),
        close_on_exit=False,
    )
    record = {
        "record_schema": "window_codon_chatgpt_oracle_consultation.v1",
        "ts": now_iso(),
        "source": "chatgpt_oracle_consultation",
        "lane": "window-codon",
        "topic": topic,
        "prompt_sha256": prompt_hash,
        "claim_update_allowed": False,
        "verdict_update_allowed": False,
        "promotion_rule": "extract proposal, then implement deterministic local experiment before changing claim verdict",
        "conversation_id": result.get("conversation_id"),
        "turns": len(result.get("turns") if isinstance(result.get("turns"), list) else []),
        "closed_reason": result.get("closed_reason"),
        "max_turns_reached": result.get("max_turns_reached"),
        "judge_calls": result.get("judge_calls"),
        "transcript_jsonl": result.get("transcript_jsonl"),
        "transcript_md": result.get("transcript_md"),
    }
    append_jsonl(ORACLE_CONSULTATIONS, record)
    ORACLE_STATE.parent.mkdir(parents=True, exist_ok=True)
    ORACLE_STATE.write_text(
        json.dumps(
            {
                "last_attempt_ts": record["ts"],
                "last_attempt_epoch": time.time(),
                "last_prompt_hash": prompt_hash,
                "last_topic": topic,
                "conversation_id": result.get("conversation_id"),
                "last_transcript_jsonl": result.get("transcript_jsonl"),
                "last_transcript_md": result.get("transcript_md"),
            },
            ensure_ascii=False,
            indent=1,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )
    return {"ran": True, "topic": topic, "turns": record["turns"], "closed_reason": record["closed_reason"]}


def paper_lane() -> dict:
    gen = subprocess.run(
        [sys.executable, str(SCRIPT_DIR / "paper_gen.py")],
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
    )
    gate = subprocess.run(
        [sys.executable, str(SCRIPT_DIR / "paper_gate.py")],
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
    )
    result = {
        "generated": gen.returncode == 0,
        "gate_ok": gate.returncode == 0,
    }
    if gen.returncode != 0:
        result["gen_error"] = ((gen.stderr or gen.stdout) or "")[-300:]
    if gate.returncode != 0:
        result["gate_error"] = ((gate.stderr or gate.stdout) or "")[-300:]
    print(f"[paper] generated={result['generated']} gate_ok={result['gate_ok']}", flush=True)
    return result


def keep_lane():
    """Lean commit lane: commit changed bridge files on this branch."""
    tracked_paths = (
        "tools/window_codon_bridge/registries",
        "tools/window_codon_bridge/experiments",
        "tools/window_codon_bridge/oracle_inbox",
        "tools/window_codon_bridge/state/oracle_sessions",
        "tools/window_codon_bridge/synced",
        "papers/window_codon_bridge",
    )
    st = git("status", "--porcelain", *tracked_paths).stdout.strip()
    if not st:
        return {"committed": False}
    git("add", *tracked_paths)
    r = git("commit", "-m", f"Bridge cycle {now_iso()}: derivation verdicts + ledger")
    return {"committed": r.returncode == 0, "out": (r.stdout or r.stderr)[-200:]}


def should_stop() -> bool:
    return STOP.exists()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--once", action="store_true")
    ap.add_argument("--interval-seconds", type=float, default=DEFAULT_INTERVAL)
    ap.add_argument("--no-commit", action="store_true")
    ap.add_argument("--no-oracle", action="store_true")
    args = ap.parse_args()
    STATE_DIR.mkdir(parents=True, exist_ok=True)
    with LOCK.open("w", encoding="utf-8") as lock_fh:
        try:
            fcntl.flock(lock_fh.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            print("[supervisor] another window-codon bridge supervisor is running", flush=True)
            return
        lock_fh.write(str(os.getpid()))
        lock_fh.flush()
        while not should_stop():
            sync = sync_lane()
            summary = run_cycle()
            oracle = {"ran": False, "reason": "disabled_by_flag"} if args.no_oracle else chatgpt_oracle_lane()
            paper = paper_lane()
            keep = {} if args.no_commit else keep_lane()
            publish = {} if args.no_commit else publish_lane()
            print(f"[{summary['ts']}] bridge cycle executed={summary['executed']} verdicts={summary['verdicts']} sync={sync} oracle={oracle} paper={paper} keep={keep} publish={publish}", flush=True)
            if args.once:
                break
            time.sleep(max(1.0, float(args.interval_seconds)))


if __name__ == "__main__":
    main()
