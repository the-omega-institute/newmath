#!/usr/bin/env python3
"""评估 GSE165177 human senescence/SASP transcription marker 方向。"""

from __future__ import annotations

import hashlib
import json
import math
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
CELLSTATE_ROOT = REPO_ROOT / "tools" / "cellstate_reality"
DATA_PATH = CELLSTATE_ROOT / "data" / "gse165177_function_signature_inputs.json"
OUT_DIR = CELLSTATE_ROOT / "out"
EXPERIMENT_ID = "gse165177-function-signature"
CLAIM_ID = "cellstate.function-signature-shift.gse165177-mptr-human"
CONTACT_ID = "k-f.gse165177-mptr-human"
CONJECTURE_ID = "function-signature-shift.gse165177-mptr-human"
PROBE_ID = "function-signature-shift.gse165177-mptr-human"
MIN_N_PER_GROUP = 3
NULL_TRIALS = 64
SENESCENCE = ["CDKN2A", "CDKN1A", "TP53", "GLB1", "SERPINE1"]
LMNB1_REVERSE = "LMNB1"
SASP = ["IL6", "IL1A", "IL1B", "CXCL8", "CXCL1", "CXCL2", "MMP3", "MMP1", "CCL2", "TNF"]


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def mean(values: list[float]) -> float:
    return sum(values) / float(len(values)) if values else float("nan")


def finite(value: float) -> bool:
    return not math.isnan(value) and not math.isinf(value)


def check(name: str, passed: bool, reason: str, value: Any | None = None) -> dict[str, Any]:
    row: dict[str, Any] = {"name": name, "passed": bool(passed), "reason": reason}
    if value is not None:
        row["value"] = value
    return row


def load_inputs() -> dict[str, Any]:
    return json.loads(DATA_PATH.read_text(encoding="utf-8"))


def marker_value(payload: dict[str, Any], marker: str, sample: str) -> float | None:
    gene = payload.get("genes", {}).get(marker)
    if not isinstance(gene, dict):
        return None
    values = gene.get("log2_rpm")
    if not isinstance(values, dict) or sample not in values:
        return None
    value = float(values[sample])
    return value if finite(value) else None


def paired_marker_delta(payload: dict[str, Any], marker: str, pair: dict[str, Any], *, reverse: bool = False) -> dict[str, Any]:
    treated_sample = str(pair["treated_sample"])
    control_sample = str(pair["control_sample"])
    treated = marker_value(payload, marker, treated_sample)
    control = marker_value(payload, marker, control_sample)
    if treated is None or control is None:
        return {
            "marker": marker,
            "donor": pair.get("donor"),
            "covered": False,
            "control_sample": control_sample,
            "treated_sample": treated_sample,
        }
    raw_delta = treated - control
    directional_delta = -raw_delta if reverse else raw_delta
    return {
        "marker": marker,
        "donor": pair.get("donor"),
        "covered": True,
        "reverse_direction": reverse,
        "control_sample": control_sample,
        "treated_sample": treated_sample,
        "control_log2_rpm": control,
        "treated_log2_rpm": treated,
        "raw_treated_minus_control": raw_delta,
        "directional_delta": directional_delta,
    }


def panel_rows(payload: dict[str, Any], markers: list[str], pairs: list[dict[str, Any]], *, reverse_marker: str | None = None) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for pair in pairs:
        for marker in markers:
            rows.append(paired_marker_delta(payload, marker, pair, reverse=marker == reverse_marker))
    return rows


def donor_panel_means(rows: list[dict[str, Any]]) -> dict[str, float]:
    by_donor: dict[str, list[float]] = {}
    for row in rows:
        if row.get("covered") is True:
            by_donor.setdefault(str(row.get("donor")), []).append(float(row["directional_delta"]))
    return {donor: mean(values) for donor, values in sorted(by_donor.items()) if values}


def deterministic_sign_patterns(donors: list[str], max_trials: int) -> list[dict[str, int]]:
    all_patterns: list[dict[str, int]] = []
    for mask in range(1 << len(donors)):
        pattern: dict[str, int] = {}
        for index, donor in enumerate(donors):
            pattern[donor] = -1 if (mask >> index) & 1 else 1
        all_patterns.append(pattern)
    ranked = sorted(
        all_patterns,
        key=lambda pattern: hashlib.sha256(json.dumps(pattern, sort_keys=True).encode("utf-8")).hexdigest(),
    )
    return ranked[: min(max_trials, len(ranked))]


def empirical_direction_p(donor_means: dict[str, float], observed: float) -> dict[str, Any]:
    donors = sorted(donor_means)
    if not donors or not finite(observed):
        return {"p_empirical": None, "trial_count": 0, "extreme_count": 0}
    patterns = deterministic_sign_patterns(donors, NULL_TRIALS)
    null_values: list[float] = []
    for pattern in patterns:
        null_values.append(mean([donor_means[donor] * float(pattern[donor]) for donor in donors]))
    extreme = sum(1 for value in null_values if value <= observed)
    return {
        "p_empirical": (extreme + 1) / float(len(null_values) + 1),
        "trial_count": len(null_values),
        "extreme_count": extreme,
        "min_null": min(null_values),
        "max_null": max(null_values),
    }


def sample_evidence(payload: dict[str, Any]) -> list[dict[str, Any]]:
    annotations = payload.get("sample_annotations", {})
    evidence: list[dict[str, Any]] = []
    for pair in payload.get("paired_tests", []):
        if not isinstance(pair, dict):
            continue
        for role, key in [("control", "control_sample"), ("treated", "treated_sample")]:
            sample = str(pair[key])
            annotation = annotations.get(sample, {}) if isinstance(annotations, dict) else {}
            evidence.append(
                {
                    "role": role,
                    "sample_title": sample,
                    "gsm": annotation.get("gsm", ""),
                    "organism": annotation.get("organism", ""),
                    "source_name": annotation.get("source_name", ""),
                    "characteristics": annotation.get("characteristics", []),
                    "donor": annotation.get("donor", pair.get("donor")),
                    "day": annotation.get("day", pair.get("day")),
                    "experiment": annotation.get("experiment", pair.get("experiment")),
                    "donor_age_years": annotation.get("donor_age_years"),
                }
            )
    return evidence


def main() -> int:
    started_at = now_iso()
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    data_available = DATA_PATH.exists()
    payload = load_inputs() if data_available else {}
    pairs = [pair for pair in payload.get("paired_tests", []) if isinstance(pair, dict)]
    genes = payload.get("genes", {}) if isinstance(payload.get("genes"), dict) else {}
    missing_markers = list(payload.get("missing_markers", [])) if isinstance(payload.get("missing_markers"), list) else []

    sen_rows = panel_rows(payload, SENESCENCE + [LMNB1_REVERSE], pairs, reverse_marker=LMNB1_REVERSE)
    sasp_rows = panel_rows(payload, SASP, pairs)
    sen_donor = donor_panel_means(sen_rows)
    sasp_donor = donor_panel_means(sasp_rows)
    delta_sen = mean(list(sen_donor.values()))
    delta_sasp = mean(list(sasp_donor.values()))
    sen_null = empirical_direction_p(sen_donor, delta_sen)
    sasp_null = empirical_direction_p(sasp_donor, delta_sasp)

    covered_markers = sorted(marker for marker in SENESCENCE + [LMNB1_REVERSE] + SASP if marker in genes)
    n_ok = len(pairs) >= MIN_N_PER_GROUP
    organism_ok = str(payload.get("organism")) == "Homo sapiens"
    human_samples_ok = all(row.get("organism") == "Homo sapiens" for row in sample_evidence(payload))
    marker_coverage_ok = not missing_markers and len(covered_markers) == len(SENESCENCE) + 1 + len(SASP)
    direction_ok = finite(delta_sen) and finite(delta_sasp) and delta_sen < 0.0 and delta_sasp < 0.0
    support = bool(data_available and organism_ok and human_samples_ok and n_ok and marker_coverage_ok and direction_ok)
    status = "passed" if support else "needs_data"
    verdict = "FunctionSignatureShiftUp_support" if support else "needs_data_or_mixed_direction"

    checks = [
        check(
            "input.available",
            data_available,
            "Curated human GSE165177 function marker input must exist.",
            {"data_path": str(DATA_PATH.relative_to(REPO_ROOT))},
        ),
        check(
            "human.sample.structure",
            organism_ok and human_samples_ok and n_ok,
            "Use only Homo sapiens donor-matched negative-control versus transiently reprogrammed fibroblast samples with at least three pairs.",
            {"pair_count": len(pairs), "min_n_per_group": MIN_N_PER_GROUP, "organism": payload.get("organism")},
        ),
        check(
            "marker.panel.coverage",
            marker_coverage_ok,
            "All predeclared human senescence/SASP markers, with LMNB1 handled as reverse-direction, must be present.",
            {"covered": covered_markers, "missing": missing_markers},
        ),
        check(
            "mean.delta.senescence.negative",
            finite(delta_sen) and delta_sen < 0.0,
            "Mean donor-level treated-minus-control senescence marker delta must be negative after LMNB1 reverse correction.",
            {"delta_senescence": delta_sen, "lmnb1_reverse_corrected": True, "direction_null": sen_null},
        ),
        check(
            "mean.delta.sasp.negative",
            finite(delta_sasp) and delta_sasp < 0.0,
            "Mean donor-level treated-minus-control SASP/inflammation marker delta must be negative.",
            {"delta_sasp_inflammation": delta_sasp, "direction_null": sasp_null},
        ),
        check(
            "function-signature-only.boundary",
            True,
            "Senescence/SASP transcription marker direction is not a direct functional assay and cannot be promoted.",
            {
                "direct_functional_assay": False,
                "generator_kind": payload.get("generator_kind", ""),
                "carrier_merged_with_age_or_identity": False,
            },
        ),
    ]

    certificate = {
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "conjecture_id": CONJECTURE_ID,
        "probe_id": PROBE_ID,
        "contact_id": CONTACT_ID,
        "started_at": started_at,
        "completed_at": now_iso(),
        "support": support,
        "status": status,
        "verdict": verdict,
        "summary": {
            "delta_senescence": delta_sen,
            "delta_sasp_inflammation": delta_sasp,
            "senescence_empirical_direction_p": sen_null.get("p_empirical"),
            "sasp_empirical_direction_p": sasp_null.get("p_empirical"),
            "pair_count": len(pairs),
            "min_n_per_group": MIN_N_PER_GROUP,
            "marker_coverage_count": len(covered_markers),
            "marker_total": len(SENESCENCE) + 1 + len(SASP),
            "generator_kind": payload.get("generator_kind", ""),
        },
        "donor_panel_means": {
            "senescence_lmnb1_reverse_corrected": sen_donor,
            "sasp_inflammation": sasp_donor,
        },
        "senescence_marker_rows": sen_rows,
        "sasp_inflammation_marker_rows": sasp_rows,
        "sample_evidence": sample_evidence(payload),
        "checks": checks,
        "cannot_claim": [
            "FunctionSignatureShiftUp is only a senescence/SASP transcription signature direction in this certificate.",
            "This is not direct functional rejuvenation; no proliferation, collagen, migration, mitochondrial, or other direct function assay is scored.",
            "This does not establish identity, age, safety, rejuvenation, maintenance, organismal maintenance, or immortality.",
            "The genetic MPTR OSKM generator is not merged with chemical reprogramming generators.",
        ],
    }
    certificate_path = OUT_DIR / "gse165177_function_signature_certificate.json"
    certificate_path.write_text(json.dumps(certificate, ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        json.dumps(
            {
                "status": status,
                "checks": checks,
                "result": {
                    "experiment_id": EXPERIMENT_ID,
                    "claim_id": CLAIM_ID,
                    "support": support,
                    "verdict": verdict,
                    "delta_senescence": delta_sen,
                    "delta_sasp_inflammation": delta_sasp,
                    "senescence_empirical_direction_p": sen_null.get("p_empirical"),
                    "sasp_empirical_direction_p": sasp_null.get("p_empirical"),
                    "pair_count": len(pairs),
                    "generator_kind": payload.get("generator_kind", ""),
                    "certificate_path": str(certificate_path.relative_to(REPO_ROOT)),
                    "scope_boundary": "human RNA senescence/SASP marker signature only; not a direct functional assay or promoted carrier",
                },
            },
            ensure_ascii=False,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
