from __future__ import annotations

import json
import math
import time
from pathlib import Path
from typing import Any

import numpy as np

from _phase1c_gap_ledger import auroc_rank, flatten_transition_rows, predict_logistic_head
from _phase2a_brittleness_gap import NPZ_PATH, fit_clean_protocol, perturbation_grid
from _phase2c_ood_aware_gap import (
    cache_path as phase2c_cache_path,
    fit_gap_head_for_parts,
    load_part_cache,
    materialize_clean_split,
)
from _lat_lewm_ood import build_perturbed_windows, load_emb_cache, strength_token
from _lat_lewm_ood_aware import mse_cache_path, score_lat, split_emb_cache_path, train_lat
from _lat_lewm_port import (
    DYNAMICS_WEIGHT,
    NPZ_PATH as LAT_NPZ_PATH,
    PYTHON_SEED,
    REPORT_DIR,
    build_windows,
    split_episodes,
    train_arm,
)


ROOT = Path(__file__).resolve().parent
JSON_PATH = REPORT_DIR / "lewm_conformal_selective_guarantee.json"
MD_PATH = REPORT_DIR / "lewm_conformal_selective_guarantee.md"
PHASE2C_JSON = REPORT_DIR / "lewm_ood_aware_gap.json"
LAT_PORT_JSON = REPORT_DIR / "lewm_ledger_aware_transformer.json"
LAT_OOD_JSON = REPORT_DIR / "lewm_ledger_aware_transformer_ood_aware.json"
ALPHAS = (0.05, 0.10, 0.15, 0.20)
ANCHOR_TOL = 1e-9


def load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def finite_float(x: Any) -> float:
    return float(x)


def assert_anchor(name: str, got: float, expected: float) -> dict[str, Any]:
    diff = abs(float(got) - float(expected))
    if diff > ANCHOR_TOL:
        raise SystemExit(f"anchor mismatch for {name}: got {got:.17g}, expected {expected:.17g}, diff={diff:.3g}")
    return {
        "name": name,
        "observed": float(got),
        "committed": float(expected),
        "abs_diff": float(diff),
        "tolerance": ANCHOR_TOL,
        "status": "passed",
    }


def wilson_ci(k: int, n: int, z: float = 1.959963984540054) -> dict[str, float | None]:
    if n <= 0:
        return {"low": None, "high": None}
    phat = k / n
    denom = 1.0 + z * z / n
    center = (phat + z * z / (2.0 * n)) / denom
    half = z * math.sqrt((phat * (1.0 - phat) / n) + (z * z / (4.0 * n * n))) / denom
    return {"low": float(max(0.0, center - half)), "high": float(min(1.0, center + half))}


def calibrate_threshold(score: np.ndarray, y: np.ndarray, alpha: float) -> dict[str, Any]:
    score = np.asarray(score, dtype=np.float64)
    y = np.asarray(y, dtype=np.int8)
    order = np.argsort(score, kind="mergesort")
    s_sorted = score[order]
    y_sorted = y[order]
    cum_fail = np.cumsum(y_sorted, dtype=np.int64)
    n = np.arange(1, len(y_sorted) + 1, dtype=np.int64)
    conservative_risk = (1.0 + cum_fail) / (1.0 + n)
    feasible = conservative_risk <= alpha
    if not np.any(feasible):
        return {
            "status": "fail_closed",
            "reason": "no usable threshold",
            "threshold": None,
            "covered_calibration_rows": 0,
            "calibration_failures_covered": 0,
            "conservative_calibration_risk": None,
        }
    idx = int(np.flatnonzero(feasible)[-1])
    return {
        "status": "ok",
        "threshold": float(s_sorted[idx]),
        "covered_calibration_rows": int(n[idx]),
        "calibration_failures_covered": int(cum_fail[idx]),
        "conservative_calibration_risk": float(conservative_risk[idx]),
    }


def evaluate_selective(score: np.ndarray, y: np.ndarray, tau: float | None, alpha: float) -> dict[str, Any]:
    score = np.asarray(score, dtype=np.float64)
    y = np.asarray(y, dtype=np.int8)
    n = int(len(y))
    if tau is None:
        ok = np.zeros(n, dtype=bool)
    else:
        ok = score <= float(tau)
    ok_n = int(ok.sum())
    fail_ok = int(y[ok].sum()) if ok_n else 0
    risk = (fail_ok / ok_n) if ok_n else None
    ci = wilson_ci(fail_ok, ok_n)
    violated = bool(ci["low"] is not None and ci["low"] > alpha)
    return {
        "n": n,
        "failure_rate": float(np.mean(y)) if n else None,
        "ok_count": ok_n,
        "ok_rate": float(ok_n / n) if n else None,
        "failures_among_ok": fail_ok,
        "realized_p_fail_given_ok": None if risk is None else float(risk),
        "wilson95": ci,
        "violated": violated,
        "violation_rule": "ci_low > alpha",
    }


def score_logistic(head: Any, part: dict[str, Any]) -> np.ndarray:
    score, _ = predict_logistic_head(head, part["x"].astype(np.float64))
    return score.astype(np.float64)


def load_phase2c_eval_part(family: str, strength: float) -> dict[str, Any]:
    part = load_part_cache(
        phase2c_cache_path(family, strength, "eval"),
        family,
        strength,
        "eval",
        "phase2c_materialized_cache",
    )
    if part is None:
        raise SystemExit(f"missing phase2c eval cache for {family} {strength}")
    return part


def build_logistic_monitors(data: dict[str, np.ndarray], rows: dict[str, np.ndarray]) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    phase2c = load_json(PHASE2C_JSON)
    protocol = fit_clean_protocol(data, rows)
    clean_train = materialize_clean_split(protocol, rows, "train")
    clean_cal = materialize_clean_split(protocol, rows, "calibration")
    clean_eval = materialize_clean_split(protocol, rows, "eval")

    clean_head, clean_info = fit_gap_head_for_parts([clean_train])
    clean_eval_score = score_logistic(clean_head, clean_eval)
    anchors = [
        assert_anchor(
            "logistic_clean_only.clean_eval.auroc",
            auroc_rank(clean_eval["y"], clean_eval_score),
            phase2c["arms"]["clean_only"]["clean_eval"]["observed"]["failure_detection_auroc"],
        )
    ]

    grids = perturbation_grid()
    train_parts = [clean_train]
    for family, strengths in grids.items():
        for strength in strengths:
            if float(strength) == 0.0:
                continue
            part = load_part_cache(
                phase2c_cache_path(family, float(strength), "train"),
                family,
                float(strength),
                "train",
                "phase2c_materialized_cache",
            )
            if part is None:
                raise SystemExit(f"missing phase2c train cache for {family} {strength}")
            train_parts.append(part)
    ood_head, ood_info = fit_gap_head_for_parts(train_parts)
    ood_eval_score = score_logistic(ood_head, clean_eval)
    anchors.append(
        assert_anchor(
            "logistic_ood_aware.clean_eval.auroc",
            auroc_rank(clean_eval["y"], ood_eval_score),
            phase2c["arms"]["ood_aware"]["clean_eval"]["observed"]["failure_detection_auroc"],
        )
    )

    monitors = {
        "logistic_clean_only": {
            "type": "logistic_gap_head",
            "fit_info": clean_info,
            "score_part": lambda part, head=clean_head: score_logistic(head, part),
            "calibration": {"score": score_logistic(clean_head, clean_cal), "y": clean_cal["y"]},
            "clean_eval": {"score": clean_eval_score, "y": clean_eval["y"], "episode": clean_eval["episode"]},
        },
        "logistic_ood_aware": {
            "type": "logistic_gap_head",
            "fit_info": ood_info,
            "score_part": lambda part, head=ood_head: score_logistic(head, part),
            "calibration": {"score": score_logistic(ood_head, clean_cal), "y": clean_cal["y"]},
            "clean_eval": {"score": ood_eval_score, "y": clean_eval["y"], "episode": clean_eval["episode"]},
        },
    }
    return monitors, anchors


def load_lat_eval_slice(
    data: dict[str, np.ndarray],
    rows1c: dict[str, np.ndarray],
    family: str,
    strength: float,
    tau_err: float,
) -> dict[str, Any]:
    emb_path = split_emb_cache_path("eval", family, strength)
    pert_emb_by_ep = load_emb_cache(emb_path)
    if pert_emb_by_ep is None:
        raise SystemExit(f"missing LAT eval embedding cache {emb_path}")
    mse_path = mse_cache_path("eval", family, strength)
    if not mse_path.exists():
        raise SystemExit(f"missing LAT eval mse cache {mse_path}")
    raw = np.load(mse_path)
    valid_idx = raw["row_idx"].astype(np.int64)
    mse = raw["mse"].astype(np.float64)
    episodes = rows1c["episode"][valid_idx].astype(np.int64)
    ts = rows1c["t"][valid_idx].astype(np.int64)
    win_emb, win_act = build_perturbed_windows(pert_emb_by_ep, data["action"].astype(np.float32), episodes, ts)
    return {
        "win_emb": win_emb,
        "win_act": win_act,
        "y": (mse > tau_err).astype(np.int8),
        "episode": episodes,
    }


def load_lat_train_slice(
    data: dict[str, np.ndarray],
    rows1c: dict[str, np.ndarray],
    family: str,
    strength: float,
    tau_err: float,
) -> dict[str, Any]:
    emb_path = split_emb_cache_path("train", family, strength)
    pert_emb_by_ep = load_emb_cache(emb_path)
    if pert_emb_by_ep is None:
        raise SystemExit(f"missing LAT train embedding cache {emb_path}")
    mse_path = mse_cache_path("train", family, strength)
    if not mse_path.exists():
        raise SystemExit(f"missing LAT train mse cache {mse_path}")
    raw = np.load(mse_path)
    valid_idx = raw["row_idx"].astype(np.int64)
    mse = raw["mse"].astype(np.float64)
    episodes = rows1c["episode"][valid_idx].astype(np.int64)
    ts = rows1c["t"][valid_idx].astype(np.int64)
    win_emb, win_act = build_perturbed_windows(pert_emb_by_ep, data["action"].astype(np.float32), episodes, ts)
    dyn_target = np.stack([pert_emb_by_ep[int(ep)][int(t) + 1] for ep, t in zip(episodes, ts)]).astype(np.float32)
    return {
        "win_emb": win_emb,
        "win_act": win_act,
        "y": (mse > tau_err).astype(np.int8),
        "episode": episodes,
        "dyn_target": dyn_target,
    }


def build_lat_monitors(data: dict[str, np.ndarray]) -> tuple[dict[str, Any], list[dict[str, Any]], dict[str, Any]]:
    lat_port = load_json(LAT_PORT_JSON)
    lat_ood = load_json(LAT_OOD_JSON)

    win_rows = build_windows(data)
    n_ep = data["emb"].shape[0]
    splits = split_episodes(n_ep)
    masks = {name: np.isin(win_rows["episode"], eps) for name, eps in splits.items()}
    train_mask = masks["train"]
    cal_mask = masks["calibration"]
    eval_mask = masks["eval"]
    tau_err = float(np.percentile(win_rows["mse"][train_mask], 75))
    y_clean = (win_rows["mse"] > tau_err).astype(np.int8)

    clean_scores, clean_info, clean_model, clean_norm = train_arm(
        win_rows,
        train_mask,
        y_clean,
        seed=PYTHON_SEED,
        dynamics_weight=DYNAMICS_WEIGHT,
        label_permutation_seed=None,
        return_artifacts=True,
    )
    anchors = [
        assert_anchor(
            "lat_clean.clean_eval.auroc",
            auroc_rank(y_clean[eval_mask], clean_scores[eval_mask]),
            lat_port["arms"]["lat_learned"]["metrics_eval_episode_bootstrap"]["failure_detection_auroc"]["observed"],
        )
    ]

    rows1c = flatten_transition_rows(data)
    clean_train = {
        "win_emb": win_rows["win_emb"][train_mask],
        "win_act": win_rows["win_act"][train_mask],
        "y": y_clean[train_mask],
        "dyn_target": win_rows["next_emb"][train_mask],
    }
    grids = perturbation_grid()
    ood_train_parts = [clean_train]
    for family, strengths in grids.items():
        for strength in strengths:
            if float(strength) == 0.0:
                continue
            ood_train_parts.append(load_lat_train_slice(data, rows1c, family, float(strength), tau_err))
    ood_train = {
        "win_emb": np.concatenate([p["win_emb"] for p in ood_train_parts], axis=0),
        "win_act": np.concatenate([p["win_act"] for p in ood_train_parts], axis=0),
        "y": np.concatenate([p["y"] for p in ood_train_parts], axis=0),
        "dyn_target": np.concatenate([p["dyn_target"] for p in ood_train_parts], axis=0),
    }
    ood_model, ood_norm, ood_info = train_lat(
        ood_train["win_emb"],
        ood_train["win_act"],
        ood_train["y"],
        ood_train["dyn_target"],
        seed=PYTHON_SEED,
    )
    ood_clean_eval_score = score_lat(ood_model, ood_norm, win_rows["win_emb"][eval_mask], win_rows["win_act"][eval_mask])
    anchors.append(
        assert_anchor(
            "lat_ood_aware.clean_eval.auroc",
            auroc_rank(y_clean[eval_mask], ood_clean_eval_score),
            lat_ood["arms"]["lat_ood_aware"]["clean_eval"]["metrics"]["failure_detection_auroc"]["observed"],
        )
    )

    monitors = {
        "lat_clean": {
            "type": "ledger_aware_transformer",
            "fit_info": clean_info,
            "model": clean_model,
            "norm": clean_norm,
            "calibration": {
                "score": clean_scores[cal_mask].astype(np.float64),
                "y": y_clean[cal_mask].astype(np.int8),
            },
            "clean_eval": {
                "score": clean_scores[eval_mask].astype(np.float64),
                "y": y_clean[eval_mask].astype(np.int8),
                "episode": win_rows["episode"][eval_mask].astype(np.int64),
            },
        },
        "lat_ood_aware": {
            "type": "ledger_aware_transformer",
            "fit_info": ood_info,
            "model": ood_model,
            "norm": ood_norm,
            "calibration": {
                "score": score_lat(ood_model, ood_norm, win_rows["win_emb"][cal_mask], win_rows["win_act"][cal_mask]),
                "y": y_clean[cal_mask].astype(np.int8),
            },
            "clean_eval": {
                "score": ood_clean_eval_score,
                "y": y_clean[eval_mask].astype(np.int8),
                "episode": win_rows["episode"][eval_mask].astype(np.int64),
            },
        },
    }
    lat_context = {
        "win_rows": win_rows,
        "rows1c": rows1c,
        "tau_err": tau_err,
    }
    return monitors, anchors, lat_context


def slice_id(family: str, strength: float) -> str:
    return f"{family}:{strength_token(strength)}"


def md_num(x: Any, digits: int = 3) -> str:
    if x is None:
        return "NA"
    return f"{float(x):.{digits}f}"


def representative_table(report: dict[str, Any], alpha: str = "0.10") -> str:
    slices = ["clean", "background_tint:0p15", "color_shift:0p1"]
    rows = [
        "| monitor | slice | risk | OK rate | Wilson 95% | violated |",
        "|---|---:|---:|---:|---:|---:|",
    ]
    for monitor, mrep in report["monitors"].items():
        for sid in slices:
            ev = mrep["alphas"][alpha]["slices"][sid]
            ci = ev["wilson95"]
            ci_s = f"[{md_num(ci['low'])}, {md_num(ci['high'])}]" if ci["low"] is not None else "NA"
            rows.append(
                f"| {monitor} | {sid} | {md_num(ev['realized_p_fail_given_ok'])} | "
                f"{md_num(ev['ok_rate'])} | {ci_s} | {ev['violated']} |"
            )
    return "\n".join(rows)


def build_markdown(report: dict[str, Any]) -> str:
    lines = [
        "# LeWM conformal-style selective guarantee",
        "",
        "This report replaces the bare 0.5 declared-OK rule with monitor-specific thresholds calibrated on the clean calibration split.",
        "",
        "Declared-OK is `gap_score <= tau_alpha`. The threshold is the largest calibration score whose conservative empirical failure ratio `(1 + failures_OK) / (1 + OK)` is at most alpha.",
        "",
        "## Anchors",
        "",
        "| anchor | observed | committed | diff |",
        "|---|---:|---:|---:|",
    ]
    for a in report["anchors"]:
        lines.append(f"| {a['name']} | {a['observed']:.12f} | {a['committed']:.12f} | {a['abs_diff']:.3g} |")
    lines.extend(
        [
            "",
            "## Representative alpha=0.10 slices",
            "",
            representative_table(report, "0.10"),
            "",
            "## Full matrix",
            "",
        ]
    )
    for monitor, mrep in report["monitors"].items():
        lines.extend([f"### {monitor}", ""])
        for alpha, arep in mrep["alphas"].items():
            cal = arep["calibration"]
            lines.append(
                f"- alpha={alpha}: threshold={md_num(cal['threshold'], 6)}; "
                f"calibration_status={cal['status']}; covered={cal['covered_calibration_rows']}"
            )
            lines.extend(
                [
                    "",
                    "| slice | n | fail rate | OK rate | risk | Wilson 95% | violated |",
                    "|---|---:|---:|---:|---:|---:|---:|",
                ]
            )
            for sid, ev in arep["slices"].items():
                ci = ev["wilson95"]
                ci_s = f"[{md_num(ci['low'])}, {md_num(ci['high'])}]" if ci["low"] is not None else "NA"
                lines.append(
                    f"| {sid} | {ev['n']} | {md_num(ev['failure_rate'])} | {md_num(ev['ok_rate'])} | "
                    f"{md_num(ev['realized_p_fail_given_ok'])} | {ci_s} | {ev['violated']} |"
                )
            lines.append("")
    lines.extend(
        [
            "## Conclusion",
            "",
            report["conclusion"]["text"],
            "",
            "## Not claimed",
            "",
            report["not_claimed"],
            "",
        ]
    )
    return "\n".join(lines)


def summarize_conclusion(report: dict[str, Any]) -> dict[str, Any]:
    by_slice: dict[str, dict[str, int]] = {}
    for mrep in report["monitors"].values():
        for arep in mrep["alphas"].values():
            for sid, ev in arep["slices"].items():
                stats = by_slice.setdefault(sid, {"total": 0, "violated": 0, "zero_ok": 0})
                stats["total"] += 1
                stats["violated"] += int(ev["violated"])
                stats["zero_ok"] += int(ev["ok_count"] == 0)

    clean_ok = by_slice.get("clean", {})
    bg = {k: v for k, v in by_slice.items() if k.startswith("background_tint:")}
    strong = {k: v for k, v in by_slice.items() if not (k == "clean" or k.startswith("background_tint:"))}
    bg_viol = sum(v["violated"] for v in bg.values())
    strong_viol = sum(v["violated"] for v in strong.values())
    strong_zero = sum(v["zero_ok"] for v in strong.values())
    text = (
        f"Clean slice violations: {clean_ok.get('violated', 0)}/{clean_ok.get('total', 0)} monitor-alpha cells. "
        f"Background_tint violations: {bg_viol}/{sum(v['total'] for v in bg.values())} cells. "
        f"Non-background OOD violations: {strong_viol}/{sum(v['total'] for v in strong.values())} cells; "
        f"zero-OK fail-closed cells among them: {strong_zero}. "
        "Interpretation: clean calibration carries the intended finite-sample selective-risk meaning only where exchangeability is plausible; OOD slices are coverage mapping, not a theorem transfer."
    )
    return {
        "by_slice": by_slice,
        "text": text,
    }


def main() -> None:
    t0 = time.perf_counter()
    print("[conformal] loading data", flush=True)
    np.random.seed(PYTHON_SEED)
    data = dict(np.load(NPZ_PATH))
    if Path(NPZ_PATH) != Path(LAT_NPZ_PATH):
        raise SystemExit(f"NPZ path mismatch: {NPZ_PATH} vs {LAT_NPZ_PATH}")
    rows1c = flatten_transition_rows(data)

    print("[conformal] rebuilding logistic monitors", flush=True)
    logistic_monitors, logistic_anchors = build_logistic_monitors(data, rows1c)
    print(f"[conformal] logistic monitors ready in {time.perf_counter() - t0:.1f}s", flush=True)
    print("[conformal] rebuilding LAT monitors", flush=True)
    lat_monitors, lat_anchors, lat_context = build_lat_monitors(data)
    print(f"[conformal] LAT monitors ready in {time.perf_counter() - t0:.1f}s", flush=True)

    monitors = {**logistic_monitors, **lat_monitors}
    grids = perturbation_grid()

    report: dict[str, Any] = {
        "schema_id": "lewm.conformal_selective_guarantee",
        "protocol": {
            "alphas": list(ALPHAS),
            "calibration_split": "clean calibration episodes from split_episodes",
            "threshold_rule": "largest tau with (1 + failures among score <= tau) / (1 + rows with score <= tau) <= alpha",
            "declared_ok": "score <= tau_alpha",
            "violation_flag": "Wilson 95% CI lower bound for realized P(fail | OK) exceeds alpha",
            "anchor_tolerance": ANCHOR_TOL,
        },
        "not_claimed": (
            "This is selective risk control by finite-sample conservative calibration, not a full split-conformal alpha-bound theorem. "
            "Exchangeability naturally breaks under perturbation slices; that break is the object being mapped."
        ),
        "anchors": logistic_anchors + lat_anchors,
        "monitors": {},
    }

    for monitor_name, monitor in monitors.items():
        print(f"[conformal] evaluating {monitor_name}", flush=True)
        m_out: dict[str, Any] = {
            "type": monitor["type"],
            "fit_info": monitor.get("fit_info", {}),
            "calibration_sample_count": int(len(monitor["calibration"]["y"])),
            "calibration_failure_rate": float(np.mean(monitor["calibration"]["y"])),
            "alphas": {},
        }
        thresholds = {alpha: calibrate_threshold(monitor["calibration"]["score"], monitor["calibration"]["y"], alpha) for alpha in ALPHAS}

        eval_slices: dict[str, dict[str, Any]] = {
            "clean": {
                "score": monitor["clean_eval"]["score"],
                "y": monitor["clean_eval"]["y"],
            }
        }
        for family, strengths in grids.items():
            for strength in strengths:
                if float(strength) == 0.0:
                    continue
                sid = slice_id(family, float(strength))
                if monitor["type"] == "logistic_gap_head":
                    part = load_phase2c_eval_part(family, float(strength))
                    eval_slices[sid] = {"score": monitor["score_part"](part), "y": part["y"]}
                else:
                    sl = load_lat_eval_slice(data, lat_context["rows1c"], family, float(strength), lat_context["tau_err"])
                    eval_slices[sid] = {
                        "score": score_lat(monitor["model"], monitor["norm"], sl["win_emb"], sl["win_act"]),
                        "y": sl["y"],
                    }

        for alpha in ALPHAS:
            alpha_key = f"{alpha:.2f}"
            cal = thresholds[alpha]
            tau = cal["threshold"] if cal["status"] == "ok" else None
            m_out["alphas"][alpha_key] = {
                "calibration": cal,
                "slices": {
                    sid: evaluate_selective(sl["score"], sl["y"], tau, alpha)
                    for sid, sl in eval_slices.items()
                },
            }
        report["monitors"][monitor_name] = m_out

    report["conclusion"] = summarize_conclusion(report)

    REPORT_DIR.mkdir(exist_ok=True)
    JSON_PATH.write_text(json.dumps(report, indent=2, sort_keys=True), encoding="utf-8")
    MD_PATH.write_text(build_markdown(report), encoding="utf-8")
    print(f"wrote {JSON_PATH}")
    print(f"wrote {MD_PATH}")
    print(f"[conformal] done in {time.perf_counter() - t0:.1f}s", flush=True)


if __name__ == "__main__":
    main()
