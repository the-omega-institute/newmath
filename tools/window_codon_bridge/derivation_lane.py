#!/usr/bin/env python3
"""Autonomous derivation lane for assimilated oracle plans.

The lane dispatches at most one Codex worker to author a new deterministic
bridge experiment, verifies the authored script before merge, then registers
the claim for the normal supervisor run_cycle.
"""
from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import Any


SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[1]
STATE_PATH = SCRIPT_DIR / "state" / "derivation_lane_state.json"
ASSIMILATION_DIR = SCRIPT_DIR / "state" / "oracle_assimilation"
CLAIMS = SCRIPT_DIR / "registries" / "claims.json"
EXPS = SCRIPT_DIR / "registries" / "experiments.json"
VALID_STATUSES = {"certified", "coincidence", "refuted", "needs_derivation"}
VALID_RETURN_CODES = {0, 2, 3}
DEFAULT_COOLDOWN_SECONDS = 3600
DEFAULT_TIMEOUT_SECONDS = 3600


def load_json(path: Path, default: Any = None) -> Any:
    if not path.exists():
        return default
    return json.loads(path.read_text(encoding="utf-8"))


def write_json(path: Path, obj: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, tmp = tempfile.mkstemp(dir=str(path.parent), suffix=".tmp")
    with os.fdopen(fd, "w", encoding="utf-8") as fh:
        json.dump(obj, fh, ensure_ascii=False, indent=1)
        fh.write("\n")
    os.replace(tmp, path)


def default_state() -> dict[str, Any]:
    return {
        "in_flight": None,
        "last_dispatch_epoch": 0.0,
        "derived_experiment_ids": [],
        "failed_experiment_ids": [],
    }


def load_state() -> dict[str, Any]:
    state = load_json(STATE_PATH, default_state())
    if not isinstance(state, dict):
        state = default_state()
    base = default_state()
    base.update(state)
    if not isinstance(base.get("derived_experiment_ids"), list):
        base["derived_experiment_ids"] = []
    if not isinstance(base.get("failed_experiment_ids"), list):
        base["failed_experiment_ids"] = []
    return base


def save_state(state: dict[str, Any]) -> None:
    write_json(STATE_PATH, state)


def git_busy() -> bool:
    return subprocess.run(["pgrep", "-x", "git"], capture_output=True).returncode == 0


def run_git(args: list[str], *, cwd: Path = REPO_ROOT) -> subprocess.CompletedProcess[str]:
    if git_busy():
        raise RuntimeError("git busy")
    return subprocess.run(["git", "-C", str(cwd), *args], capture_output=True, text=True)


def tail(text: str, limit: int = 400) -> str:
    return (text or "")[-limit:]


def slugify(value: str, *, sep: str = "_") -> str:
    text = value.lower()
    text = re.sub(r"[^a-z0-9]+", sep, text)
    text = re.sub(re.escape(sep) + r"+", sep, text).strip(sep)
    text = re.sub(r"\bv[0-9]+\b|\br[0-9]+\b", "", text)
    text = re.sub(re.escape(sep) + r"+", sep, text).strip(sep)
    return text or "derived_axis"


def stable_hash(obj: Any, size: int = 10) -> str:
    raw = json.dumps(obj, ensure_ascii=False, sort_keys=True)
    return hashlib.sha256(raw.encode("utf-8")).hexdigest()[:size]


def latest_plan_path() -> Path | None:
    paths = sorted(ASSIMILATION_DIR.glob("latest_*_plan.json"), key=lambda path: path.stat().st_mtime, reverse=True)
    return paths[0] if paths else None


def existing_experiment_ids() -> set[str]:
    doc = load_json(EXPS, {})
    return {
        str(item.get("experiment_id"))
        for item in doc.get("experiments", [])
        if isinstance(item, dict) and item.get("experiment_id")
    }


def external_data_required(route: dict[str, Any]) -> bool:
    source = " ".join(
        str(route.get(key) or "")
        for key in ("finite_data_source", "finite_data_sources", "required_fields", "construction")
    ).lower()
    external_markers = (
        "gnomad",
        "gencode",
        "rmbase",
        "modomics",
        "brenda",
        "sabio",
        "gtrnadb",
        "trnadb",
        "ncbi genetic codes",
        "codetta",
        "mavedb",
        "proteingym",
        "public",
        "published",
        "synthesize",
        "bounded",
        "reporter panel",
    )
    return any(marker in source for marker in external_markers)


def route_ready(plan: dict[str, Any], route: dict[str, Any]) -> tuple[bool, str]:
    if external_data_required(route):
        return False, "requires_external_data"
    if not str(plan.get("exact_projection_test") or "").strip():
        return False, "missing_exact_projection_test"
    if not str(plan.get("common_admissibility_contract") or "").strip():
        return False, "missing_admissibility_contract"
    return True, "ready"


def synthetic_negative_control_route(plan: dict[str, Any]) -> dict[str, Any]:
    return {
        "rank": 0,
        "name": "Synthetic negative-control axis pack",
        "route_id": "synthetic_negative_control_axis_pack",
        "summary": (
            "Use only in-repo deterministic codon features and seeded synthetic "
            "vectors to audit the common projection harness before any external "
            "candidate axis is attempted."
        ),
        "finite_data_source": "in-repo codon table plus deterministic seeded synthetic vectors",
        "construction": (
            "Generate random Gaussian, GC-only, wobble-only, tAI-like, and "
            "codon-pair-like 61-vectors. Residualize through the common forbidden "
            "matrix and require exact nulls to reject numerical coincidences."
        ),
        "why_it_is_not_explained_by_forbidden_axes": (
            "The vectors are negative controls, not biological measurements; any "
            "apparent projection must be classified as coincidence unless forced by "
            "structure and rejected by the null ledger."
        ),
        "exclusion_controls": "Seeded nulls, label-free construction, no q6 labels, no SerSplit in raw vector construction.",
        "failure_mode": "A projection that survives for forbidden or random controls marks the harness as too permissive.",
        "plan_sha256": stable_hash(plan),
    }


def ready_routes(plan: dict[str, Any]) -> list[dict[str, Any]]:
    routes: list[dict[str, Any]] = []
    order_text = "\n".join(str(item) for item in plan.get("recommended_execution_order") or [])
    local_artifacts = {str(item) for item in plan.get("local_next_artifacts") or []}
    harness_exists = "tools/window_codon_bridge/experiments/run_edge_defect_projection_harness.py" in local_artifacts
    if "synthetic negative-control" in order_text.lower() and harness_exists:
        routes.append(synthetic_negative_control_route(plan))
    for route in plan.get("candidate_routes") or []:
        if not isinstance(route, dict):
            continue
        ok, _reason = route_ready(plan, route)
        if ok:
            routes.append(route)
    return routes


def choose_route(state: dict[str, Any]) -> tuple[dict[str, Any] | None, dict[str, Any] | None, str]:
    path = latest_plan_path()
    if path is None:
        return None, None, "no_plan"
    plan = load_json(path, {})
    if not isinstance(plan, dict):
        return None, None, "bad_plan"
    seen = set(str(item) for item in state.get("derived_experiment_ids", []))
    seen.update(str(item) for item in state.get("failed_experiment_ids", []))
    seen.update(existing_experiment_ids())
    for route in ready_routes(plan):
        route_id = str(route.get("route_id") or route.get("name") or "")
        experiment_id = experiment_id_for_route(route_id)
        if experiment_id in seen:
            continue
        return plan, route, "ready"
    return plan, None, "no_ready_route"


def experiment_id_for_route(route_id: str) -> str:
    base = slugify(route_id)
    if base.startswith("run_"):
        base = base[4:]
    if len(base) > 72:
        base = base[:72].rstrip("_")
    return base


def claim_id_for_experiment(experiment_id: str) -> str:
    return "bridge.genetic_code." + experiment_id.replace("_", ".")


def branch_for_experiment(experiment_id: str) -> str:
    return "deriv-" + experiment_id.replace("_", "-")


def worktree_for_experiment(experiment_id: str) -> Path:
    return Path("/tmp") / f"wt-deriv-{experiment_id.replace('_', '-')}"


def script_relpath(experiment_id: str) -> str:
    return f"tools/window_codon_bridge/experiments/run_{experiment_id}.py"


def build_prompt(plan: dict[str, Any], route: dict[str, Any], experiment_id: str, claim_id: str) -> str:
    route_packet = {
        "route": route,
        "common_admissibility_contract": plan.get("common_admissibility_contract"),
        "exact_projection_test": plan.get("exact_projection_test"),
        "hard_rejection_rules": plan.get("hard_rejection_rules"),
        "minimal_data_requests": plan.get("minimal_data_requests"),
        "local_next_artifacts": plan.get("local_next_artifacts"),
    }
    script = script_relpath(experiment_id)
    return f"""你是 Window6 ↔ codon-Q6 桥 autonomous derivation worker。

项目不变量:
- 工作语言中文；代码注释从简。
- 不改 Lean、不改 paper、不改 registries、不 push remote。
- 只新建 `{script}`，并在通过自检后 commit。
- 禁止 axiom/sorry 语义占位；本任务通常只写 Python 实验。
- 命名按内容主题，不使用版本号、轮次号或过程履历词。

实验身份:
- EXPERIMENT_ID = "{experiment_id}"
- CLAIM_ID = "{claim_id}"
- 只写一个可独立运行的 Python 脚本，路径严格为 `{script}`。

反 numerology 铁律:
- 数字吻合只能输出 `coincidence`，绝不能输出 `certified`。
- `certified` 只允许在脚本给出结构 forcing、label-free 构造、严格 null/negative-control 通过时使用。
- raw axis 构造不得使用 Stop/Ser edge-defect support、u_SerSplit、q6_label、q6_bits 或任何后验标签。
- 若结果依赖标签选择、外部未获取数据、单一批次/来源、或 forbidden controls 可预测 residual，输出 `needs_derivation` 或 `coincidence`，不要硬证。

输出契约:
- 脚本最后一行必须是 JSON object。
- `status` 必须是 `certified` / `coincidence` / `refuted` / `needs_derivation` 之一。
- JSON 至少包含 `status`, `experiment_id`, `claim_id`, `reason` 或 `note`, `checks`。
- 退出码: certified/coincidence -> 0, refuted -> 2, needs_derivation -> 3。
- 脚本必须有 self-check；self-check 失败不得 certified。

计划包:
```json
{json.dumps(route_packet, ensure_ascii=False, indent=2)}
```

完成步骤:
1. 新建 `{script}`，不要碰其它文件。
2. 运行 `python3 {script}`，确认退出码在 0/2/3 且最后一行 JSON 合法。
3. `git add {script} && git commit -m "Derive {experiment_id} experiment"`。
4. 不 push，不改 registries，不改 state。
"""


def dispatch_worker(plan: dict[str, Any], route: dict[str, Any], state: dict[str, Any]) -> dict[str, Any]:
    if shutil.which("codex") is None:
        return {"ran": False, "reason": "codex_not_found"}
    experiment_id = experiment_id_for_route(str(route.get("route_id") or route.get("name") or "derived_axis"))
    claim_id = claim_id_for_experiment(experiment_id)
    branch = branch_for_experiment(experiment_id)
    worktree = worktree_for_experiment(experiment_id)
    if worktree.exists():
        return {"ran": False, "reason": "worktree_exists", "worktree": str(worktree)}
    add = run_git(["worktree", "add", "-b", branch, str(worktree), "HEAD"])
    if add.returncode != 0:
        return {"ran": False, "reason": "worktree_add_failed", "error": tail(add.stderr or add.stdout)}

    prompt_path = worktree / ".derivation_prompt.txt"
    log_path = SCRIPT_DIR / "state" / "derivation_logs" / f"{experiment_id}.log"
    prompt_path.write_text(build_prompt(plan, route, experiment_id, claim_id), encoding="utf-8")
    log_path.parent.mkdir(parents=True, exist_ok=True)
    log_fh = log_path.open("ab")
    prompt_fh = prompt_path.open("rb")
    try:
        subprocess.Popen(
            [
                "codex",
                "exec",
                "--dangerously-bypass-approvals-and-sandbox",
                "-C",
                str(worktree),
            ],
            stdin=prompt_fh,
            stdout=log_fh,
            stderr=subprocess.STDOUT,
            cwd=str(REPO_ROOT),
            start_new_session=True,
        )
    finally:
        prompt_fh.close()
        log_fh.close()

    now = time.time()
    state["in_flight"] = {
        "task_log": str(log_path),
        "branch": branch,
        "worktree": str(worktree),
        "experiment_id": experiment_id,
        "claim_id": claim_id,
        "script_path": script_relpath(experiment_id),
        "route": route,
        "started_epoch": now,
    }
    state["last_dispatch_epoch"] = now
    save_state(state)
    return {
        "ran": True,
        "reason": "dispatched",
        "experiment_id": experiment_id,
        "claim_id": claim_id,
        "branch": branch,
        "worktree": str(worktree),
        "task_log": str(log_path),
    }


def branch_has_script_commit(in_flight: dict[str, Any]) -> tuple[bool, str]:
    worktree = Path(str(in_flight.get("worktree") or ""))
    script = str(in_flight.get("script_path") or "")
    if not worktree.exists() or not script:
        return False, "missing_worktree_or_script"
    log = run_git(["log", "--oneline", "--", script], cwd=worktree)
    if log.returncode != 0:
        return False, tail(log.stderr or log.stdout)
    return bool((log.stdout or "").strip()), "script_commit_present" if (log.stdout or "").strip() else "no_script_commit"


def last_json_line(stdout: str) -> dict[str, Any] | None:
    lines = (stdout or "").strip().splitlines()
    if not lines:
        return None
    last = lines[-1].strip()
    if not (last.startswith("{") and last.endswith("}")):
        return None
    try:
        parsed = json.loads(last)
    except json.JSONDecodeError:
        return None
    return parsed if isinstance(parsed, dict) else None


def self_checks_ok(verdict: dict[str, Any]) -> tuple[bool, str]:
    checks = verdict.get("checks")
    if checks is None:
        return False, "missing_checks"
    if isinstance(checks, list):
        for index, item in enumerate(checks):
            if isinstance(item, dict) and item.get("ok") is False:
                return False, f"check_failed:{index}:{item.get('name') or 'unnamed'}"
        return True, "checks_ok"
    if isinstance(checks, dict):
        for key, value in checks.items():
            if value is False:
                return False, f"check_failed:{key}"
            if isinstance(value, dict) and value.get("ok") is False:
                return False, f"check_failed:{key}"
        return True, "checks_ok"
    return False, "checks_not_structured"


def verify_script(in_flight: dict[str, Any]) -> tuple[bool, dict[str, Any]]:
    worktree = Path(str(in_flight.get("worktree") or ""))
    script = str(in_flight.get("script_path") or "")
    path = worktree / script
    if not path.exists():
        return False, {"reason": "script_missing", "script_path": script}
    try:
        proc = subprocess.run(
            [sys.executable, str(path)],
            cwd=str(worktree),
            capture_output=True,
            text=True,
            timeout=600,
        )
    except subprocess.TimeoutExpired:
        return False, {"reason": "script_timeout", "script_path": script}
    parsed = last_json_line(proc.stdout or "")
    if parsed is None:
        return False, {
            "reason": "bad_or_missing_last_json",
            "returncode": proc.returncode,
            "stdout_tail": tail(proc.stdout),
            "stderr_tail": tail(proc.stderr),
        }
    status = str(parsed.get("status") or "")
    expected_return = 0 if status in {"certified", "coincidence"} else (2 if status == "refuted" else 3)
    if status not in VALID_STATUSES:
        return False, {"reason": "invalid_status", "status": status, "verdict": parsed}
    if proc.returncode not in VALID_RETURN_CODES:
        return False, {"reason": "invalid_returncode", "returncode": proc.returncode, "verdict": parsed}
    if proc.returncode != expected_return:
        return False, {
            "reason": "returncode_status_mismatch",
            "returncode": proc.returncode,
            "expected_returncode": expected_return,
            "verdict": parsed,
        }
    if str(parsed.get("experiment_id") or "") != str(in_flight.get("experiment_id") or ""):
        return False, {"reason": "experiment_id_mismatch", "verdict": parsed}
    if str(parsed.get("claim_id") or "") != str(in_flight.get("claim_id") or ""):
        return False, {"reason": "claim_id_mismatch", "verdict": parsed}
    checks_ok, checks_reason = self_checks_ok(parsed)
    if not checks_ok:
        return False, {"reason": checks_reason, "verdict": parsed}
    return True, {"reason": "verified", "returncode": proc.returncode, "verdict": parsed}


def verify_branch_scope(in_flight: dict[str, Any]) -> tuple[bool, dict[str, Any]]:
    branch = str(in_flight.get("branch") or "")
    script = str(in_flight.get("script_path") or "")
    diff = run_git(["diff", "--name-only", f"HEAD...{branch}"])
    if diff.returncode != 0:
        return False, {"reason": "branch_diff_failed", "error": tail(diff.stderr or diff.stdout)}
    paths = [line.strip() for line in (diff.stdout or "").splitlines() if line.strip()]
    if paths != [script]:
        return False, {"reason": "branch_scope_violation", "paths": paths, "expected": [script]}
    return True, {"reason": "branch_scope_ok", "paths": paths}


def remove_worktree_and_branch(in_flight: dict[str, Any]) -> None:
    worktree = str(in_flight.get("worktree") or "")
    branch = str(in_flight.get("branch") or "")
    if worktree:
        run_git(["worktree", "remove", "--force", worktree])
    if branch:
        run_git(["branch", "-D", branch])


def append_unique(items: list[Any], value: Any) -> None:
    if value not in items:
        items.append(value)


def register_experiment(in_flight: dict[str, Any], verdict: dict[str, Any]) -> None:
    claim_id = str(in_flight.get("claim_id") or "")
    experiment_id = str(in_flight.get("experiment_id") or "")
    script_path = str(in_flight.get("script_path") or "")
    route = in_flight.get("route") if isinstance(in_flight.get("route"), dict) else {}
    claim_statement = (
        str(route.get("summary") or route.get("name") or experiment_id).strip()
        + " This autonomous bridge claim is evaluated only by its registered deterministic experiment."
    )
    claims_doc = load_json(CLAIMS, {"version": "window-codon-bridge-claims", "claims": []})
    claims = claims_doc.setdefault("claims", [])
    existing_claim = next((item for item in claims if item.get("claim_id") == claim_id), None)
    if existing_claim is None:
        claims.append(
            {
                "claim_id": claim_id,
                "statement": claim_statement,
                "status": "needs_rerun",
                "experiment_id": experiment_id,
                "history": [
                    {
                        "ts": time.strftime("%Y-%m-%dT%H:%M:%S+00:00", time.gmtime()),
                        "status": "needs_rerun",
                        "reason": "autonomous derivation registered after verify-before-merge",
                    }
                ],
            }
        )
    else:
        existing_claim["status"] = "needs_rerun"
        existing_claim["experiment_id"] = experiment_id
        existing_claim.setdefault("history", []).append(
            {
                "ts": time.strftime("%Y-%m-%dT%H:%M:%S+00:00", time.gmtime()),
                "status": "needs_rerun",
                "reason": "autonomous derivation verified and ready for run_cycle",
            }
        )

    exps_doc = load_json(EXPS, {"version": "window-codon-bridge-experiments", "experiments": []})
    exps = exps_doc.setdefault("experiments", [])
    existing_exp = next((item for item in exps if item.get("experiment_id") == experiment_id), None)
    note = "Autonomously derived from oracle assimilation plan; verified locally before merge."
    if isinstance(verdict.get("verdict"), dict):
        note = str(verdict["verdict"].get("reason") or verdict["verdict"].get("note") or note)[:500]
    if existing_exp is None:
        exps.append(
            {
                "experiment_id": experiment_id,
                "claim_id": claim_id,
                "script_path": script_path,
                "status": "open",
                "timeout_seconds": 600,
                "note": note,
            }
        )
    else:
        existing_exp.update(
            {
                "claim_id": claim_id,
                "script_path": script_path,
                "status": "open",
                "timeout_seconds": int(existing_exp.get("timeout_seconds") or 600),
                "note": note,
            }
        )
    write_json(CLAIMS, claims_doc)
    write_json(EXPS, exps_doc)


def finish_in_flight(state: dict[str, Any], timeout_seconds: int) -> dict[str, Any]:
    in_flight = state.get("in_flight")
    if not isinstance(in_flight, dict):
        state["in_flight"] = None
        save_state(state)
        return {"ran": False, "reason": "bad_in_flight_state"}
    experiment_id = str(in_flight.get("experiment_id") or "")
    started = float(in_flight.get("started_epoch") or 0.0)

    committed, commit_reason = branch_has_script_commit(in_flight)
    if not committed:
        age = time.time() - started
        if age > timeout_seconds:
            try:
                remove_worktree_and_branch(in_flight)
            finally:
                append_unique(state["failed_experiment_ids"], experiment_id)
                state["in_flight"] = None
                save_state(state)
            return {"ran": True, "reason": "abandoned_timeout", "experiment_id": experiment_id, "age_seconds": int(age)}
        return {
            "ran": False,
            "reason": "derivation_in_flight",
            "experiment_id": experiment_id,
            "detail": commit_reason,
            "age_seconds": int(age),
            "task_log": in_flight.get("task_log"),
        }

    ok, verification = verify_script(in_flight)
    if not ok:
        try:
            remove_worktree_and_branch(in_flight)
        finally:
            append_unique(state["failed_experiment_ids"], experiment_id)
            state["in_flight"] = None
            save_state(state)
        return {"ran": True, "reason": "abandoned_verification_failed", "experiment_id": experiment_id, "verification": verification}

    scope_ok, scope = verify_branch_scope(in_flight)
    if not scope_ok:
        try:
            remove_worktree_and_branch(in_flight)
        finally:
            append_unique(state["failed_experiment_ids"], experiment_id)
            state["in_flight"] = None
            save_state(state)
        return {"ran": True, "reason": "abandoned_scope_failed", "experiment_id": experiment_id, "scope": scope}

    branch = str(in_flight.get("branch") or "")
    merge = run_git(["merge", "--no-ff", branch, "-m", f"Merge autonomous derivation {experiment_id}"])
    if merge.returncode != 0:
        return {
            "ran": False,
            "reason": "merge_failed",
            "experiment_id": experiment_id,
            "error": tail(merge.stderr or merge.stdout),
        }
    register_experiment(in_flight, verification)
    remove_worktree_and_branch(in_flight)
    append_unique(state["derived_experiment_ids"], experiment_id)
    state["in_flight"] = None
    save_state(state)
    return {
        "ran": True,
        "reason": "merged_registered",
        "experiment_id": experiment_id,
        "claim_id": in_flight.get("claim_id"),
        "script_path": in_flight.get("script_path"),
        "verification": verification,
    }


def cooldown_ready(state: dict[str, Any], cooldown_seconds: int) -> tuple[bool, int]:
    elapsed = int(time.time() - float(state.get("last_dispatch_epoch") or 0.0))
    remaining = max(0, cooldown_seconds - elapsed)
    return remaining == 0, remaining


def run_derivation_lane() -> dict[str, Any]:
    if os.environ.get("WINDOW_CODON_ALLOW_AUTONOMOUS_DERIVATION") != "1":
        return {"ran": False, "reason": "disabled"}
    state = load_state()
    cooldown_seconds = int(os.environ.get("WINDOW_CODON_DERIVATION_COOLDOWN_SECONDS") or DEFAULT_COOLDOWN_SECONDS)
    timeout_seconds = int(os.environ.get("WINDOW_CODON_DERIVATION_TIMEOUT_SECONDS") or DEFAULT_TIMEOUT_SECONDS)

    if state.get("in_flight"):
        try:
            return finish_in_flight(state, timeout_seconds)
        except RuntimeError as exc:
            return {"ran": False, "reason": str(exc)}

    ready, remaining = cooldown_ready(state, cooldown_seconds)
    if not ready:
        return {"ran": False, "reason": "cooldown_active", "remaining_seconds": remaining}
    plan, route, reason = choose_route(state)
    if route is None:
        return {"ran": False, "reason": reason}
    try:
        return dispatch_worker(plan or {}, route, state)
    except RuntimeError as exc:
        return {"ran": False, "reason": str(exc)}


if __name__ == "__main__":
    print(json.dumps(run_derivation_lane(), ensure_ascii=False))
