from __future__ import annotations

import json
import math
import os
from collections import defaultdict
from pathlib import Path
from typing import Any

import numpy as np
import torch

import _g2n_native_ledger as native
from _g2n_horizon_labels import (
    MAX_PERT_H,
    QUANTILES as LABEL_QUANTILES,
    ROLL_BATCH,
    build_split_anchors,
    load_predictor,
    load_perturbed_emb,
    rollout_predictions,
)
from _lat_lewm_port import NPZ_PATH, REPORT_DIR, split_episodes
from _phase1c_gap_ledger import flatten_transition_rows
from _phase2a_brittleness_gap import clean_json


ROOT = Path(__file__).resolve().parent
PERT_PREDZ_PATH = REPORT_DIR / "g2n_labels_perturbed_predz.npz"
JSON_PATH = REPORT_DIR / "g2n_addendum.json"
MD_PATH = REPORT_DIR / "g2n_addendum.md"

PREDZ_ANCHOR_TOL = 1e-6
CLEAN_REPRO_TOL = 1e-12
EXPECTED_CLEAN_H1_Q75_AUROC = {
    "E": 0.7385152058598745,
    "F": 0.6916604239025977,
}


def require_inputs() -> None:
    missing = [
        p
        for p in (
            native.JSON_PATH,
            native.CLEAN_LABELS,
            native.PERT_LABELS,
            ROOT / "_g2n_native_ledger.py",
            ROOT / "_g2n_horizon_labels.py",
        )
        if not p.exists()
    ]
    if missing:
        raise SystemExit("missing required precursor(s): " + ", ".join(str(p) for p in missing))


def assert_new_outputs_absent() -> None:
    existing = [p for p in (PERT_PREDZ_PATH, JSON_PATH, MD_PATH) if p.exists()]
    if existing:
        raise SystemExit(
            "refusing to overwrite existing addendum output(s): " + ", ".join(str(p) for p in existing)
        )


def metric_observed_fail_closed(y: np.ndarray, prob: np.ndarray) -> dict[str, Any]:
    y = y.astype(np.int8)
    prob = prob.astype(np.float64)
    single = bool(np.unique(y).size < 2)
    return {
        "failure_detection_auroc": None if single else float(native.auroc_rank(y, prob)),
        "unlogged_error_rate": float(np.mean((y > 0) & (prob < 0.5))) if len(y) else None,
        "declared_gap_rate": float(np.mean(prob >= 0.5)) if len(y) else None,
        "failure_rate": float(np.mean(y)) if len(y) else None,
        "positive_count": int(np.sum(y > 0)),
        "negative_count": int(np.sum(y <= 0)),
        "single_class_truth": single,
    }


def summarize_bootstrap_metric(name: str, obs: Any, samples: list[Any]) -> dict[str, Any]:
    finite = np.asarray([v for v in samples if v is not None and math.isfinite(float(v))], dtype=np.float64)
    if obs is None:
        return {"observed": None, "bootstrap_mean": None, "ci95_low": None, "ci95_high": None}
    return {
        "observed": float(obs),
        "bootstrap_mean": float(np.mean(finite)) if len(finite) else None,
        "ci95_low": float(np.percentile(finite, 2.5)) if len(finite) else None,
        "ci95_high": float(np.percentile(finite, 97.5)) if len(finite) else None,
    }


def bootstrap_failure_metrics_fail_closed(
    y: np.ndarray,
    prob: np.ndarray,
    episode: np.ndarray,
    *,
    seed: int = native.BOOTSTRAP_SEED,
    n_boot: int = native.BOOTSTRAPS,
) -> dict[str, Any]:
    observed = metric_observed_fail_closed(y, prob)
    unique_ep = np.unique(episode)
    by_ep = [np.where(episode == ep)[0] for ep in unique_ep]
    rng = np.random.default_rng(seed)
    values: dict[str, list[Any]] = {
        "failure_detection_auroc": [],
        "unlogged_error_rate": [],
        "declared_gap_rate": [],
        "failure_rate": [],
    }
    for _ in range(n_boot):
        sampled = rng.integers(0, len(by_ep), size=len(by_ep))
        idx = np.concatenate([by_ep[i] for i in sampled])
        m = metric_observed_fail_closed(y[idx], prob[idx])
        for key in values:
            values[key].append(m[key])
    out = {k: summarize_bootstrap_metric(k, observed[k], values[k]) for k in values}
    out["positive_count"] = observed["positive_count"]
    out["negative_count"] = observed["negative_count"]
    out["single_class_truth"] = observed["single_class_truth"]
    out["fail_closed"] = bool(observed["single_class_truth"])
    out["bootstrap_seed"] = seed
    out["bootstrap_resamples"] = n_boot
    return out


def make_perturbed_predz(data: dict[str, np.ndarray], pert: np.lib.npyio.NpzFile) -> tuple[dict[str, np.ndarray], dict[str, Any]]:
    device = torch.device("cpu")
    model, config, checkpoint_path, config_path, loader_source = load_predictor(device)
    splits = split_episodes(data["emb"].shape[0])
    eval_anchors = build_split_anchors(data, splits["eval"])
    if not np.array_equal(eval_anchors, pert[f"{str(pert['slice_keys'][0])}_anchor_ep_t0"].astype(np.int64)):
        raise SystemExit("eval anchor order mismatch between rebuilt anchors and perturbed label npz")

    npz: dict[str, np.ndarray] = {
        "horizons": np.arange(1, MAX_PERT_H + 1, dtype=np.int64),
        "slice_keys": pert["slice_keys"].copy(),
        "families": pert["families"].copy(),
        "strength_tokens": pert["strength_tokens"].copy(),
        "strengths": pert["strengths"].copy(),
    }
    rows: list[dict[str, Any]] = []
    max_delta = 0.0
    for key_raw in pert["slice_keys"]:
        key = str(key_raw)
        print(f"[pred_z] slice={key}", flush=True)
        pert_emb = load_perturbed_emb(native.OOD_EMB_CACHE_DIR / f"eval_{key}.npz")
        part = rollout_predictions(
            model,
            data,
            eval_anchors,
            device=device,
            max_h=MAX_PERT_H,
            pert_emb_by_ep=pert_emb,
            batch_size=ROLL_BATCH,
        )
        ref = pert[f"{key}_err_at_h"][:, 0].astype(np.float64)
        got = part["err_at_h"][:, 0].astype(np.float64)
        valid = pert[f"{key}_valid"][:, 0].astype(bool)
        delta = float(np.nanmax(np.abs(got[valid] - ref[valid]))) if np.any(valid) else float("nan")
        if not math.isfinite(delta) or delta >= PREDZ_ANCHOR_TOL:
            raise SystemExit(f"perturbed pred_z h=1 anchor failed for {key}: max_delta={delta:.17g}")
        max_delta = max(max_delta, delta)
        if not np.array_equal(part["valid"], pert[f"{key}_valid"].astype(bool)):
            raise SystemExit(f"valid mask mismatch while generating perturbed pred_z for {key}")

        npz[f"{key}_anchor_ep_t0"] = eval_anchors.astype(np.int64)
        npz[f"{key}_valid"] = part["valid"].astype(bool)
        npz[f"{key}_pred_z"] = part["pred_z"].astype(np.float32)
        npz[f"{key}_err_at_h"] = part["err_at_h"].astype(np.float64)
        rows.append(
            {
                "key": key,
                "anchors": int(len(eval_anchors)),
                "valid_h1": int(part["valid"][:, 0].sum()),
                "valid_h3": int(part["valid"][:, 2].sum()),
                "valid_h5": int(part["valid"][:, 4].sum()),
                "h1_err_at_h_max_abs_delta": delta,
            }
        )

    meta = {
        "status": "ok",
        "path": str(PERT_PREDZ_PATH),
        "loader_source": loader_source,
        "checkpoint_path": checkpoint_path,
        "config_path": config_path,
        "config_history_size": int(config["predictor"]["num_frames"]),
        "max_h": MAX_PERT_H,
        "anchor_tolerance": PREDZ_ANCHOR_TOL,
        "h1_err_at_h_max_abs_delta": float(max_delta),
        "slices": rows,
    }
    return npz, meta


def build_train_eval_context(data: dict[str, np.ndarray], clean: np.lib.npyio.NpzFile) -> dict[str, Any]:
    rows = flatten_transition_rows(data)
    pair_for_row = native.row_index_to_pair(rows)
    phase2c_report = json.loads(native.PHASE2C_JSON.read_text(encoding="utf-8"))
    parts_by_key, train_pert_keys = native.load_phase2c_perturb_train_parts(phase2c_report)
    teachers = native.rebuild_teachers(data, rows, parts_by_key, train_pert_keys)
    clean_train_ex = native.build_clean_examples(data, clean, "train", teachers["teacher_clean_by_pair"])
    clean_eval_ex = native.build_clean_examples(data, clean, "eval", None)
    pert_train_ex = native.build_perturbed_examples(
        data,
        clean["tau"][0].astype(np.float64),
        pair_for_row,
        parts_by_key,
        teachers["teacher_pert_by_key_row"],
        split="train",
        keys=train_pert_keys,
        labels=None,
    )
    return {
        "rows": rows,
        "teachers": teachers,
        "clean_train_ex": clean_train_ex,
        "clean_eval_ex": clean_eval_ex,
        "pert_train_ex": pert_train_ex,
    }


def build_corrected_perturbed_examples(
    data: dict[str, np.ndarray],
    pert: np.lib.npyio.NpzFile,
    predz: dict[str, np.ndarray] | np.lib.npyio.NpzFile,
    key: str,
) -> dict[str, np.ndarray]:
    ex = native.build_perturbed_examples(
        data,
        np.zeros(3, dtype=np.float64),
        {},
        {},
        {},
        split="eval",
        keys=[key],
        labels=pert,
    )
    anchors = pert[f"{key}_anchor_ep_t0"].astype(np.int64)
    pred_z = predz[f"{key}_pred_z"][:, : native.MAX_FUTURE_TOKENS].astype(np.float32)
    valid = predz[f"{key}_valid"][:, : native.MAX_FUTURE_TOKENS].astype(bool)
    clean_emb = data["emb"].astype(np.float32)
    ex["future_z"][:] = 0.0
    ex["future_delta"][:] = 0.0
    ex["future_avail"][:] = False
    for i, (ep_raw, t0_raw) in enumerate(anchors):
        ep = int(ep_raw)
        t0 = int(t0_raw)
        previous = clean_emb[ep, t0]
        for k in range(native.MAX_FUTURE_TOKENS):
            if valid[i, k] and np.isfinite(pred_z[i, k]).all():
                ex["future_z"][i, k] = pred_z[i, k]
                ex["future_delta"][i, k] = pred_z[i, k] - previous
                ex["future_avail"][i, k] = True
                previous = pred_z[i, k]
    return ex


def evaluate_ood_corrected(
    model: native.NativeLedgerTransformer,
    norm: dict[str, np.ndarray],
    data: dict[str, np.ndarray],
    pert: np.lib.npyio.NpzFile,
    predz: dict[str, np.ndarray] | np.lib.npyio.NpzFile,
    keys: list[str],
) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for key in keys:
        print(f"[ood-corrected] slice={key}", flush=True)
        ex = build_corrected_perturbed_examples(data, pert, predz, key)
        logits = native.predict_logits(model, ex, norm)
        probs = native.sigmoid_np(logits)
        by_h: dict[str, Any] = {}
        for h in (1, 3, 5):
            h_i = native.HORIZONS.index(h)
            src_i = native.PERT_H_TO_LABEL_IDX[h]
            q_i = native.Q_TO_IDX[75]
            m = pert[f"{key}_valid"][:, src_i].astype(bool)
            y = pert[f"{key}_y"][:, src_i, q_i].astype(np.int8)
            by_h[f"h{h}_q75"] = bootstrap_failure_metrics_fail_closed(
                y[m],
                probs[m, native.output_col(h, 75)],
                ex["episode"][m],
            )
        out[key] = by_h
    return out


def train_e_f_and_anchor(
    data: dict[str, np.ndarray],
    clean: np.lib.npyio.NpzFile,
    context: dict[str, Any],
) -> tuple[dict[str, native.NativeLedgerTransformer], dict[str, dict[str, np.ndarray]], dict[str, np.ndarray], dict[str, Any]]:
    train_sets = {
        "E": context["clean_train_ex"],
        "F": native.concat_examples([context["clean_train_ex"], context["pert_train_ex"]]),
    }
    configs = {
        "E": dict(include_future=True, action_only=False, use_teacher=False, use_unlogged=False, use_budget=False, label_permutation_seed=None),
        "F": dict(include_future=True, action_only=False, use_teacher=True, use_unlogged=True, use_budget=True, label_permutation_seed=None),
    }
    models: dict[str, native.NativeLedgerTransformer] = {}
    norms: dict[str, dict[str, np.ndarray]] = {}
    clean_logits: dict[str, np.ndarray] = {}
    clean_eval: dict[str, Any] = {}
    anchors: dict[str, Any] = {}
    main_report = json.loads(native.JSON_PATH.read_text(encoding="utf-8"))

    for arm in ("E", "F"):
        print(f"[train] arm={arm} rows={len(train_sets[arm]['episode'])}", flush=True)
        model, info, norm = native.train_arm(arm, train_sets[arm], **configs[arm])
        logits = native.predict_logits(model, context["clean_eval_ex"], norm)
        metrics = native.evaluate_clean(logits, context["clean_eval_ex"])
        observed = float(metrics["h1_q75"]["failure_detection_auroc"]["observed"])
        expected = EXPECTED_CLEAN_H1_Q75_AUROC[arm]
        main_observed = float(main_report["arms"][arm]["clean_eval"]["h1_q75"]["failure_detection_auroc"]["observed"])
        delta_expected = abs(observed - expected)
        delta_main = abs(observed - main_observed)
        anchors[arm] = {
            "observed": observed,
            "expected": expected,
            "main_report_observed": main_observed,
            "abs_delta_vs_expected": delta_expected,
            "abs_delta_vs_main_report": delta_main,
            "tolerance": CLEAN_REPRO_TOL,
        }
        if delta_expected > CLEAN_REPRO_TOL or delta_main > CLEAN_REPRO_TOL:
            raise SystemExit(
                f"clean reproduction anchor failed for arm {arm}: "
                f"observed={observed:.17g}, expected={expected:.17g}, main={main_observed:.17g}"
            )
        models[arm] = model
        norms[arm] = norm
        clean_logits[arm] = logits
        clean_eval[arm] = {"info": info, "clean_eval": metrics}

    return models, norms, clean_logits, {"anchors": anchors, "clean_eval": clean_eval}


def exploratory_e_allocation(
    clean: np.lib.npyio.NpzFile,
    clean_eval_ex: dict[str, np.ndarray],
    e_clean_logits: np.ndarray,
) -> dict[str, Any]:
    anchors, errors_h5 = native.build_budget_anchors(clean_eval_ex, clean)
    anchors_by_ep: dict[int, list[int]] = defaultdict(list)
    for i, anchor in enumerate(anchors):
        anchors_by_ep[int(anchor["episode"])].append(i)
    uniform_h = native.allocation_uniform(anchors_by_ep)
    uniform_alloc = native.summarize_allocation("uniform", uniform_h, errors_h5, anchors)
    valid_h5 = clean["eval_valid"][:, native.H_TO_LABEL_IDX[5]].astype(bool)
    score = e_clean_logits[valid_h5, native.output_col(5, 75)]
    e_alloc = native.budget_eval_for_score("E_exploratory", score, anchors, anchors_by_ep, errors_h5, uniform_alloc)
    oracle_score = np.mean(errors_h5, axis=1)
    oracle_alloc = native.budget_eval_for_score("oracle", oracle_score, anchors, anchors_by_ep, errors_h5, uniform_alloc)
    delta = e_alloc["delta_vs_uniform"]
    verdict = "positive" if delta["ci95_high"] < 0.0 else "negative_or_inconclusive"
    return {
        "status": "ok",
        "exploratory": True,
        "score": "arm E clean eval h=5,q=75 logit",
        "protocol": "same as _ledger_gated_rollout: eval h=5 anchors, per-episode 5/1 split, h=3 uniform, same budget, oracle same rule",
        "allocation_rule": {
            "uniform": f"h={native.UNIFORM_H} for every anchor",
            "score_sorted": f"low score half h={native.LOW_H}, high score half h={native.HIGH_H}, odd median h={native.MID_H}",
            "oracle": "same 5/1/3 rule, sorted by true h=5 mean per-step rollout error",
        },
        "allocations": {
            "uniform": {"allocation": uniform_alloc},
            "E_exploratory": e_alloc,
            "oracle": oracle_alloc,
        },
        "delta_E_minus_uniform": delta,
        "oracle_minus_uniform_per_step_mse": float(
            oracle_alloc["allocation"]["per_emitted_step_mse"] - uniform_alloc["per_emitted_step_mse"]
        ),
        "verdict": verdict,
        "positive_rule": "positive iff paired episode-bootstrap CI for delta=E_exploratory-uniform is entirely < 0",
        "not_claimed": [
            "This is outside predeclared Outcome 2.",
            "Arm E is not the predeclared primary budget-allocation arm.",
            "This exploratory result does not modify the accepted main report outcome.",
        ],
    }


def representative_slices(keys: list[str]) -> list[str]:
    preferred = ["background_tint_0p15", "brightness_0p2", "color_shift_0p2", "gaussian_noise_10", "occlusion_0p2"]
    return [k for k in preferred if k in keys] or keys[: min(5, len(keys))]


def write_markdown(report: dict[str, Any]) -> None:
    main = report["corrected_ood"]["comparison"]
    reps = report["corrected_ood"]["representative_slices"]

    def au(m: dict[str, Any]) -> str:
        a = m["failure_detection_auroc"]
        if a["observed"] is None:
            return "fail-closed"
        return f"{a['observed']:.6f} [{a['ci95_low']:.6f}, {a['ci95_high']:.6f}]"

    lines = [
        "# G2N Addendum",
        "",
        f"- status: `{report['status']}`",
        "- scope: exploratory addendum; no accepted report files were modified.",
        "- corrected OOD fixes future-token availability for perturb eval and does not overturn the main report.",
        "",
        "## Perturbed pred_z Cache",
        "",
        f"- output: `{report['perturbed_pred_z']['path']}`",
        f"- h=1 max |delta| vs `g2n_labels_perturbed.npz` err_at_h: `{report['perturbed_pred_z']['h1_err_at_h_max_abs_delta']:.9g}`",
        f"- tolerance: `{report['perturbed_pred_z']['anchor_tolerance']:.9g}`",
        "",
        "## Corrected OOD",
        "",
        "- masked column is the accepted main report value with zero/masked future tokens.",
        "- corrected column uses true perturbed rollout future tokens from this addendum.",
        "- single-class truth is fail-closed for AUROC.",
        "",
        "| arm | slice | h | masked AUROC | corrected AUROC |",
        "|---|---|---:|---:|---:|",
    ]
    for arm in ("E", "F"):
        for key in reps:
            for h in ("h1_q75", "h3_q75", "h5_q75"):
                masked = main[arm][key][h]["masked"]["failure_detection_auroc"]
                corr = main[arm][key][h]["corrected"]["failure_detection_auroc"]
                masked_str = (
                    "fail-closed"
                    if masked["observed"] is None
                    else f"{masked['observed']:.6f} [{masked['ci95_low']:.6f}, {masked['ci95_high']:.6f}]"
                )
                corr_str = (
                    "fail-closed"
                    if corr["observed"] is None
                    else f"{corr['observed']:.6f} [{corr['ci95_low']:.6f}, {corr['ci95_high']:.6f}]"
                )
                lines.append(f"| `{arm}` | `{key}` | {h[1]} | {masked_str} | {corr_str} |")

    d = report["exploratory_allocation"]["delta_E_minus_uniform"]
    lines.extend(
        [
            "",
            "## Exploratory Allocation",
            "",
            "- exploratory: true; outside predeclared Outcome 2 because E was not the predeclared main arm.",
            f"- delta E-uniform per emitted-step MSE: `{d['observed']:.9f}`",
            f"- 95% CI ({d['resamples']} episode bootstraps, seed {d['seed']}): `[{d['ci95_low']:.9f}, {d['ci95_high']:.9f}]`",
            f"- verdict: `{report['exploratory_allocation']['verdict']}`",
            "",
            "## Anchors",
            "",
            f"- perturbed pred_z h=1 max |delta|: `{report['anchors']['perturbed_pred_z_h1_max_abs_delta']:.9g}`",
            f"- E clean h=1,q75 AUROC: `{report['anchors']['clean_reproduction']['E']['observed']:.15f}`",
            f"- F clean h=1,q75 AUROC: `{report['anchors']['clean_reproduction']['F']['observed']:.15f}`",
            "",
            "## Not Claimed",
            "",
        ]
    )
    for item in report["not_claimed"]:
        lines.append(f"- {item}")
    MD_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    require_inputs()
    assert_new_outputs_absent()
    np.random.seed(native.PYTHON_SEED)
    torch.manual_seed(native.TORCH_SEED)
    torch.set_num_threads(int(os.environ.get("G2N_TORCH_THREADS", "4")))
    REPORT_DIR.mkdir(exist_ok=True)

    raw = np.load(NPZ_PATH)
    data = {k: raw[k] for k in raw.files}
    clean = np.load(native.CLEAN_LABELS)
    pert = np.load(native.PERT_LABELS)
    main_report = json.loads(native.JSON_PATH.read_text(encoding="utf-8"))
    keys = [str(k) for k in pert["slice_keys"].tolist()]
    if len(keys) != 20:
        raise SystemExit(f"expected 20 perturbed eval slices, got {len(keys)}")

    predz_npz, predz_meta = make_perturbed_predz(data, pert)
    context = build_train_eval_context(data, clean)
    models, norms, clean_logits, train_meta = train_e_f_and_anchor(data, clean, context)

    corrected: dict[str, Any] = {}
    for arm in ("E", "F"):
        corrected[arm] = evaluate_ood_corrected(models[arm], norms[arm], data, pert, predz_npz, keys)

    comparison: dict[str, Any] = {}
    for arm in ("E", "F"):
        comparison[arm] = {}
        for key in keys:
            comparison[arm][key] = {}
            for h in ("h1_q75", "h3_q75", "h5_q75"):
                comparison[arm][key][h] = {
                    "masked": main_report["arms"][arm]["ood_eval"][key][h],
                    "corrected": corrected[arm][key][h],
                }

    exploratory = exploratory_e_allocation(clean, context["clean_eval_ex"], clean_logits["E"])
    reps = representative_slices(keys)
    report = {
        "status": "ok",
        "schema_id": "g2n.exploratory_addendum",
        "protocol": {
            "deterministic": True,
            "seeds": {
                "numpy": native.PYTHON_SEED,
                "torch": native.TORCH_SEED,
                "split": native.SPLIT_SEED,
                "bootstrap": native.BOOTSTRAP_SEED,
            },
            "bootstrap_resamples": native.BOOTSTRAPS,
            "quantile": 75,
            "corrected_ood_horizons": [1, 3, 5],
            "single_class_auroc_policy": "fail-closed",
        },
        "precursors": {
            "main_report": str(native.JSON_PATH),
            "clean_labels": str(native.CLEAN_LABELS),
            "perturbed_labels": str(native.PERT_LABELS),
        },
        "perturbed_pred_z": predz_meta,
        "corrected_ood": {
            "status": "ok",
            "input_artifact": "true perturbed rollout future tokens from g2n_labels_perturbed_predz.npz",
            "masked_reference": "reports/g2n_native_ledger.json arms E/F ood_eval, generated with zero/masked future tokens",
            "representative_slices": reps,
            "corrected": corrected,
            "comparison": comparison,
            "not_claimed": [
                "Corrected OOD fixes an input availability artifact only.",
                "Corrected OOD does not modify or overturn the accepted main report.",
            ],
        },
        "exploratory_allocation": exploratory,
        "anchors": {
            "perturbed_pred_z_h1_max_abs_delta": predz_meta["h1_err_at_h_max_abs_delta"],
            "perturbed_pred_z_tolerance": PREDZ_ANCHOR_TOL,
            "clean_reproduction": train_meta["anchors"],
        },
        "training": {
            "E": train_meta["clean_eval"]["E"]["info"],
            "F": train_meta["clean_eval"]["F"]["info"],
            "teacher_anchor_checks": context["teachers"]["anchor_checks"],
        },
        "not_claimed": [
            "This is an exploratory addendum and a separate report.",
            "No existing accepted report or label file is modified.",
            "The exploratory allocation test is outside predeclared Outcome 2; arm E was not the predeclared primary arm.",
            "Corrected OOD repairs future-token availability for perturb eval and does not overturn the main report.",
            "Results are reported regardless of direction.",
        ],
        "outputs": {
            "perturbed_pred_z_npz": str(PERT_PREDZ_PATH),
            "json": str(JSON_PATH),
            "md": str(MD_PATH),
        },
    }

    np.savez_compressed(PERT_PREDZ_PATH, **predz_npz)
    clean_report = clean_json(report)
    JSON_PATH.write_text(json.dumps(clean_report, indent=2, ensure_ascii=False), encoding="utf-8")
    write_markdown(clean_report)
    print(json.dumps(clean_json(report["anchors"]), indent=2, ensure_ascii=False), flush=True)
    print(json.dumps(clean_json(report["exploratory_allocation"]["delta_E_minus_uniform"]), indent=2, ensure_ascii=False), flush=True)
    print(f"wrote {PERT_PREDZ_PATH}", flush=True)
    print(f"wrote {JSON_PATH}", flush=True)
    print(f"wrote {MD_PATH}", flush=True)


if __name__ == "__main__":
    main()
