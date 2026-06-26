#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import math
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"

DEFAULT_REMOTE_HOST = "zwlexa@zlogin1.ddns.comp.nus.edu.sg"
DEFAULT_REMOTE_ROOT = "/mnt/rna01/zwlexa/scratch/lewm_alloc_derisk"
DEFAULT_LOCAL_LATENTS = ROOT / "tworooms_latent_large.npz"
DEFAULT_ALT_LATENTS = Path("C:/OMEGA/le-wm-survey/tworooms_latent_large.npz")

REMOTE_ARTIFACTS = {
    "hrto_json": "out/g2n_HRTO_scores.json",
    "hrto_scores": "out/g2n_HRTO_scores.npz",
    "permutation_json": "out/g2n_perm_fixed_wrap.json",
}

LOCAL_ARTIFACTS = {
    "hrto_json": REPORT_DIR / "g2n_integrated_a100_HRTO_scores.json",
    "hrto_scores": REPORT_DIR / "g2n_integrated_a100_scores.npz",
    "permutation_json": REPORT_DIR / "g2n_integrated_a100_perm.json",
    "strongest_paired_json": REPORT_DIR / "g2n_integrated_a100_strongest_paired.json",
    "selective_sweep_json": REPORT_DIR / "g2n_integrated_a100_selective_sweep.json",
    "closure_status_json": REPORT_DIR / "g2n_integrated_a100_closure_status.json",
}


def clean_float(value: float) -> float:
    out = float(value)
    if out == 0.0:
        return 0.0
    if not math.isfinite(out):
        raise ValueError(f"non-finite JSON float: {out!r}")
    return out


def clean_json(value: Any) -> Any:
    if isinstance(value, dict):
        return {str(k): clean_json(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [clean_json(v) for v in value]
    if isinstance(value, float):
        return clean_float(value)
    return value


def run_cmd(cmd: list[str], *, timeout: int = 120) -> tuple[int, str, str]:
    proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
    return int(proc.returncode), proc.stdout, proc.stderr


def remote_path(remote_root: str, rel_path: str) -> str:
    return remote_root.rstrip("/") + "/" + rel_path.lstrip("/")


def remote_exists(host: str, remote_file: str) -> bool:
    rc, _out, _err = run_cmd(["ssh", "-o", "BatchMode=yes", "-o", "ConnectTimeout=15", host, "test", "-f", remote_file], timeout=30)
    return rc == 0


def copy_remote(host: str, remote_file: str, local_file: Path) -> dict[str, Any]:
    local_file.parent.mkdir(parents=True, exist_ok=True)
    rc, out, err = run_cmd(
        [
            "scp",
            "-o",
            "BatchMode=yes",
            "-o",
            "ConnectTimeout=15",
            f"{host}:{remote_file}",
            str(local_file),
        ],
        timeout=180,
    )
    return {
        "remote": remote_file,
        "local": str(local_file),
        "copied": rc == 0,
        "returncode": rc,
        "stdout_tail": out[-800:],
        "stderr_tail": err[-800:],
    }


def maybe_pull_remote(args: argparse.Namespace) -> list[dict[str, Any]]:
    if not bool(args.pull_remote):
        return []
    host = str(args.remote_host)
    root = str(args.remote_root)
    results: list[dict[str, Any]] = []
    for key, rel_path in REMOTE_ARTIFACTS.items():
        remote_file = remote_path(root, rel_path)
        local_file = LOCAL_ARTIFACTS[key]
        if remote_exists(host, remote_file):
            results.append(copy_remote(host, remote_file, local_file))
        else:
            results.append({"remote": remote_file, "local": str(local_file), "copied": False, "reason": "missing_remote_file"})
    return results


def resolve_latents(args: argparse.Namespace) -> Path | None:
    candidates = [Path(args.latents), DEFAULT_LOCAL_LATENTS, DEFAULT_ALT_LATENTS]
    for path in candidates:
        if path.exists():
            return path
    return None


def run_analysis(script: Path, args: list[str], out_path: Path) -> dict[str, Any]:
    cmd = [sys.executable, str(script), *args]
    rc, stdout, stderr = run_cmd(cmd, timeout=1800)
    return {
        "script": str(script),
        "out": str(out_path),
        "ran": rc == 0,
        "returncode": rc,
        "stdout_tail": stdout[-1200:],
        "stderr_tail": stderr[-1200:],
        "exists": out_path.exists(),
    }


def read_json(path: Path) -> dict[str, Any] | None:
    if not path.exists():
        return None
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ValueError(f"expected JSON object: {path}")
    return data


def maybe_run_closure_analyses(args: argparse.Namespace) -> list[dict[str, Any]]:
    if not bool(args.run_analyses):
        return []
    score_dump = LOCAL_ARTIFACTS["hrto_scores"]
    outputs: list[dict[str, Any]] = []
    if not score_dump.exists():
        return [{"analysis": "g2n_closure", "ran": False, "reason": "missing_score_dump", "path": str(score_dump)}]
    latents = resolve_latents(args)
    if latents is None:
        outputs.append({"analysis": "strongest_paired", "ran": False, "reason": "missing_latents"})
    else:
        strongest_out = LOCAL_ARTIFACTS["strongest_paired_json"]
        outputs.append(
            run_analysis(
                ROOT / "_g2n_strongest_paired.py",
                ["--latents", str(latents), "--score-dump", str(score_dump), "--out", str(strongest_out), "--seed", str(int(args.seed))],
                strongest_out,
            )
        )
    selective_out = LOCAL_ARTIFACTS["selective_sweep_json"]
    outputs.append(
        run_analysis(
            ROOT / "_g2n_selective_sweep.py",
            ["--score-dump", str(score_dump), "--out", str(selective_out)],
            selective_out,
        )
    )
    return outputs


def strongest_summary(path: Path) -> dict[str, Any]:
    data = read_json(path)
    if data is None:
        return {"status": "pending", "reason": "missing_strongest_paired_json"}
    ci = data.get("ci") if isinstance(data.get("ci"), dict) else {}
    return {
        "status": str(data.get("status") or "unknown"),
        "metric_value": data.get("metric_value"),
        "ci": {"low": ci.get("low"), "high": ci.get("high")},
        "claim": str(data.get("reported_claim") or ""),
    }


def selective_summary(path: Path) -> dict[str, Any]:
    data = read_json(path)
    if data is None:
        return {"status": "pending", "reason": "missing_selective_sweep_json"}
    rows = data.get("rows") if isinstance(data.get("rows"), list) else []
    passing = [row for row in rows if isinstance(row, dict) and row.get("risk_le_alpha") is True]
    best = max(passing, key=lambda row: float(row.get("coverage", 0.0)), default=None)
    return {
        "status": str(data.get("status") or "unknown"),
        "target": data.get("target"),
        "best_passing": best,
        "claim": str(data.get("reported_claim") or ""),
    }


def permutation_summary(path: Path) -> dict[str, Any]:
    data = read_json(path)
    if data is None:
        return {"status": "pending", "reason": "missing_permutation_json"}
    health = data.get("health") if isinstance(data.get("health"), dict) else {}
    detection = data.get("detection") if isinstance(data.get("detection"), dict) else {}
    per_h = detection.get("per_h_auroc") if isinstance(detection.get("per_h_auroc"), dict) else {}
    h1 = per_h.get("h1")
    accepted = str(health.get("status") or "") == "ok" and isinstance(h1, (int, float)) and float(h1) < 0.60
    return {
        "status": "accepted" if accepted else "fail-closed",
        "health_status": health.get("status"),
        "h1_auroc": h1,
        "criterion": "accepted when shuffled-label h1 AUROC is finite and below 0.60",
        "claim": str(data.get("reported_claim") or ""),
    }


def build_status(args: argparse.Namespace, pull_results: list[dict[str, Any]], analysis_results: list[dict[str, Any]]) -> dict[str, Any]:
    artifacts = {
        key: {"path": str(path), "exists": path.exists(), "bytes": path.stat().st_size if path.exists() else 0}
        for key, path in LOCAL_ARTIFACTS.items()
        if key != "closure_status_json"
    }
    status = {
        "schema_id": "g2n.a100.closure_pipeline",
        "remote": {"enabled": bool(args.pull_remote), "host": str(args.remote_host), "root": str(args.remote_root)},
        "artifacts": artifacts,
        "pull_results": pull_results,
        "analysis_results": analysis_results,
        "closures": {
            "strongest_paired": strongest_summary(LOCAL_ARTIFACTS["strongest_paired_json"]),
            "selective_sweep": selective_summary(LOCAL_ARTIFACTS["selective_sweep_json"]),
            "permutation_guard": permutation_summary(LOCAL_ARTIFACTS["permutation_json"]),
        },
    }
    ready = [
        item
        for item in status["closures"].values()
        if isinstance(item, dict) and str(item.get("status")) not in {"pending", "unknown"}
    ]
    status["overall"] = {
        "finite_closures": len(ready),
        "all_closures_finite": len(ready) == 3,
        "claim_boundary": (
            "direct paired, selective sweep, and permutation guard are research closures only after finite artifacts exist; "
            "missing artifacts remain pending and do not change the paper claim."
        ),
    }
    return clean_json(status)


def main() -> int:
    parser = argparse.ArgumentParser(description="Monitor and close G2N A100 research artifacts")
    parser.add_argument("--remote-host", default=DEFAULT_REMOTE_HOST)
    parser.add_argument("--remote-root", default=DEFAULT_REMOTE_ROOT)
    parser.add_argument("--latents", default=str(DEFAULT_LOCAL_LATENTS))
    parser.add_argument("--out", default=str(LOCAL_ARTIFACTS["closure_status_json"]))
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--pull-remote", action="store_true")
    parser.add_argument("--no-analyses", dest="run_analyses", action="store_false")
    parser.set_defaults(run_analyses=True)
    args = parser.parse_args()

    pull_results = maybe_pull_remote(args)
    analysis_results = maybe_run_closure_analyses(args)
    status = build_status(args, pull_results, analysis_results)
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(status, ensure_ascii=False, sort_keys=False, separators=(",", ":")) + "\n", encoding="utf-8")
    print(json.dumps(status["overall"], ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
