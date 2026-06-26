#!/usr/bin/env python3
"""Project debt-dose levels into discovery predicates."""

from __future__ import annotations

import json
import math
import random
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.classifier_shift import ClassifierPassage, ClassifierState, classifier_surface_delta, shift_information, structural_discovery
from bedc_quality_lab.discovery import DiscoveryClaim, net_information, positive_discovery
from bedc_quality_lab.ledger import LedgerRowKey
from bedc_quality_lab.scope import CLOSED_CLAIM_SCOPE_SEAL, closed_claim_scope_seal

SOURCE_JSON_ARTIFACT = "reports/debt_dose_response.json"
SOURCE_REPORT_ARTIFACT = "reports/debt_dose_response_report.md"
JSON_ARTIFACT = "reports/dose_response_discovery.json"
REPORT_ARTIFACT = "reports/dose_response_discovery.md"
SCOPE_SEAL = CLOSED_CLAIM_SCOPE_SEAL
CONTROL_SEED = 53120260602
CONTROL_PERMUTATIONS = 200
METRICS = ("quality_q", "quality_debt", "target_score", "linear_identifiability_r2", "approx_identifiability_proxy")
def _load_source_payload(path: Path | None = None) -> dict[str, Any]:
    payload = json.loads((ROOT / SOURCE_JSON_ARTIFACT if path is None else path).read_text(encoding="utf-8"))
    by_level = payload.get("aggregate", {}).get("by_level", {})
    if not by_level:
        raise ValueError("debt-dose payload must contain aggregate.by_level")
    for key, row in by_level.items():
        missing = [name for name in METRICS if "mean" not in row.get("metrics", {}).get(name, {})]
        if missing:
            raise ValueError(f"debt-dose level {key} lacks metric means: {', '.join(missing)}")
    return payload
def _level_rows(payload: dict[str, Any]) -> list[dict[str, Any]]:
    return sorted(payload["aggregate"]["by_level"].values(), key=lambda row: float(row["debt_level"]))
def _metric_means(row: dict[str, Any]) -> dict[str, float]:
    return {name: float(row["metrics"][name]["mean"]) for name in METRICS}
def _ledger_row(pair: tuple[str, str]) -> LedgerRowKey:
    return LedgerRowKey("classifier", f"{pair[0]}->{pair[1]}")
def _state(pattern_id: str, values: dict[str, float], surface: frozenset[tuple[str, str]]) -> ClassifierState:
    source_ids = frozenset(f"metric:{name}" for name in METRICS)
    return ClassifierState(
        source_ids=source_ids,
        pattern_id=pattern_id,
        ledger_policy=frozenset(_ledger_row(pair) for pair in surface),
        relation=frozenset((f"metric:{name}", f"metric:{name}", f"{values[name]:.12g}") for name in METRICS),
        certificate={"cert_status": "certified", "source_artifact": SOURCE_JSON_ARTIFACT},
        surface_used=surface,
        verification_status="artifact-checked",
        record_count=len(source_ids),
        feature_count=len(METRICS),
        notation="metric-self-pair",
    )
def _project_level(level: dict[str, Any], baseline: dict[str, Any]) -> dict[str, Any]:
    dose, base, current = float(level["debt_level"]), _metric_means(baseline), _metric_means(level)
    surface = frozenset((f"metric:{name}", f"metric:{name}") for name in METRICS if current[name] != base[name])
    ledger_rows = frozenset(_ledger_row(pair) for pair in surface)
    passage = ClassifierPassage(_state("debt-dose-baseline", base, frozenset()), _state(f"debt-dose-{dose:.1f}", current, surface), ledger_rows)
    delta_count = len(classifier_surface_delta(passage))
    claim = DiscoveryClaim(
        passage=passage,
        benefit_terms={
            "quality_debt_signal": max(0.0, current["quality_debt"] - base["quality_debt"]),
            "target_residue_signal": max(0.0, current["target_score"] - base["target_score"]),
            "quality_drop_signal": max(0.0, base["quality_q"] - current["quality_q"]),
        },
        score_terms={"public_projection_cost": 0.01 * delta_count, "quality_cost": 0.03},
        debt_terms={"baseline_projection_floor": 0.02 if delta_count else 0.0},
        ledger_required_rows=ledger_rows,
        ledger_recorded_rows=ledger_rows,
        public_cost_protocol=True,
        scope_sealed=closed_claim_scope_seal(SCOPE_SEAL),
        not_claimed_boundary=frozenset({"formal-bedc-closure", "non-gaussian-dose-generalization"}),
        benefit_modes=frozenset({"quality_debt_signal", "target_residue_signal", "quality_drop_signal"}),
        reproducible_evidence=True,
    )
    return {"dose": dose, "metrics": current, "passage": passage, "claim": claim}
def _ranks(values: list[float]) -> list[float]:
    ordered, ranks, i = sorted(enumerate(values), key=lambda item: item[1]), [0.0] * len(values), 0
    while i < len(ordered):
        j = i + 1
        while j < len(ordered) and ordered[j][1] == ordered[i][1]:
            j += 1
        for index, _ in ordered[i:j]:
            ranks[index] = (i + 1 + j) / 2.0
        i = j
    return ranks
def _pearson(xs: list[float], ys: list[float]) -> float:
    xm, ym = sum(xs) / len(xs), sum(ys) / len(ys)
    xn, yn = math.sqrt(sum((x - xm) ** 2 for x in xs)), math.sqrt(sum((y - ym) ** 2 for y in ys))
    return math.nan if xn == 0.0 or yn == 0.0 else sum((x - xm) * (y - ym) for x, y in zip(xs, ys, strict=True)) / (xn * yn)
def _spearman(xs: list[float], ys: list[float]) -> float:
    return _pearson(_ranks(xs), _ranks(ys))
def _kendall_tau(xs: list[float], ys: list[float]) -> float:
    concordant = discordant = ties_x = ties_y = 0
    for i in range(len(xs)):
        for j in range(i + 1, len(xs)):
            dx, dy = (xs[i] > xs[j]) - (xs[i] < xs[j]), (ys[i] > ys[j]) - (ys[i] < ys[j])
            if dx == 0 and dy != 0:
                ties_x += 1
            elif dy == 0 and dx != 0:
                ties_y += 1
            elif dx == dy and dx != 0:
                concordant += 1
            elif dx != 0 and dy != 0:
                discordant += 1
    denom = math.sqrt((concordant + discordant + ties_x) * (concordant + discordant + ties_y))
    return math.nan if denom == 0.0 else (concordant - discordant) / denom
def _matched_random_baseline(doses: list[float], nets: list[float]) -> dict[str, Any]:
    rng, observed, controls = random.Random(CONTROL_SEED), _spearman(doses, nets), []
    for _ in range(CONTROL_PERMUTATIONS):
        shuffled = list(nets)
        rng.shuffle(shuffled)
        controls.append(abs(_spearman(doses, shuffled)))
    controls.sort()
    q95 = controls[min(len(controls) - 1, math.ceil(0.95 * len(controls)) - 1)]
    return {"seed": CONTROL_SEED, "permutations": CONTROL_PERMUTATIONS, "observed_spearman": observed, "mean_abs_spearman": sum(controls) / len(controls), "max_abs_spearman": max(controls), "quantile95_abs_spearman": q95, "observed_exceeds_quantile95": abs(observed) > q95}
def _monotonicity_conclusion(verdicts: list[dict[str, Any]], rank: dict[str, Any], baseline: dict[str, Any]) -> dict[str, Any]:
    positives, nets = [row["positive_discovery"] for row in verdicts], [float(row["net_information"]) for row in verdicts]
    nondecreasing = all(left <= right for left, right in zip(nets, nets[1:]))
    monotonic = nondecreasing and rank["spearman"] > 0.0 and rank["kendall_tau"] > 0.0 and abs(rank["spearman"]) >= 0.8 and baseline["observed_exceeds_quantile95"]
    result = "monotonic" if monotonic and any(positives) else "categorical" if any(positives) and positives == sorted(positives) else "mixed" if any(positives) else "not_positive"
    return {"result": result, "h1_monotonic_dose_response": result == "monotonic", "h0_categorical_or_threshold": result in {"categorical", "mixed", "not_positive"}, "net_information_nondecreasing": nondecreasing, "criterion": "monotonic iff positive exists, net information is nondecreasing, rank direction is positive, abs(Spearman) >= 0.8, and observed abs(Spearman) exceeds matched-random 95% baseline"}
def _verdict_payload(source_payload: dict[str, Any]) -> dict[str, Any]:
    levels, rows = _level_rows(source_payload), []
    for level in levels:
        projection = _project_level(level, levels[0])
        passage, claim = projection["passage"], projection["claim"]
        delta, net = classifier_surface_delta(passage), net_information(claim)
        structural, positive = structural_discovery(passage), positive_discovery(claim)
        rows.append({"dose": projection["dose"], "metrics": projection["metrics"], "surface_delta_count": len(delta), "surface_delta": [list(pair) for pair in sorted(delta)], "shift_information": shift_information(passage), "structural_discovery": structural, "net_positive_signal": net > 0.0, "net_information": net, "positive_discovery": positive, "verdict": "positive" if positive else "negative" if structural and delta and net < 0.0 else "compression"})
    doses, nets = [float(row["dose"]) for row in rows], [float(row["net_information"]) for row in rows]
    rank = {"method": "dose-level-vs-discovery-net-information", "spearman": _spearman(doses, nets), "kendall_tau": _kendall_tau(doses, nets), "pairs": [{"dose": d, "net_information": n} for d, n in zip(doses, nets, strict=True)]}
    control = _matched_random_baseline(doses, nets)
    return {"artifact": JSON_ARTIFACT, "source_artifacts": {"source_json_artifact": SOURCE_JSON_ARTIFACT, "source_report_artifact": SOURCE_REPORT_ARTIFACT, "source_runner": "scripts/run_debt_dose_response.py"}, "report": REPORT_ARTIFACT, "projection_script": "scripts/run_dose_response_discovery.py", "generated_from": {"artifact": SOURCE_JSON_ARTIFACT, "source_runner": "scripts/run_debt_dose_response.py", "record_count": source_payload.get("aggregate", {}).get("record_count")}, "scope_seal": SCOPE_SEAL, "doses": doses, "per_dose_verdicts": rows, "rank_correlation": rank, "matched_random_baseline": control, "monotonicity_conclusion": _monotonicity_conclusion(rows, rank, control), "applicability_boundary": source_payload.get("applicability_boundary", {})}
def _write_payload(payload: dict[str, Any]) -> None:
    lines = ["# Dose-response discovery projection", "", f"- Source JSON artifact: `{payload['source_artifacts']['source_json_artifact']}`", f"- Projection script: `{payload['projection_script']}`", f"- Conclusion: `{payload['monotonicity_conclusion']['result']}`", "", "## Per-dose Verdicts", "", "| dose | net information | surface delta | shift info | net positive | positive | verdict |", "| ---: | ---: | ---: | ---: | --- | --- | --- |"]
    lines += [f"| {row['dose']:.1f} | {row['net_information']:.6f} | {row['surface_delta_count']} | {row['shift_information']} | `{str(row['net_positive_signal']).lower()}` | `{str(row['positive_discovery']).lower()}` | `{row['verdict']}` |" for row in payload["per_dose_verdicts"]]
    rank, control = payload["rank_correlation"], payload["matched_random_baseline"]
    lines += ["", "## Rank Correlation", "", f"- Spearman: `{rank['spearman']:.6f}`", f"- Kendall tau: `{rank['kendall_tau']:.6f}`", "", "## Matched Random Baseline", "", f"- Seed: `{control['seed']}`", f"- Permutations: `{control['permutations']}`", f"- 95% absolute Spearman: `{control['quantile95_abs_spearman']:.6f}`", f"- Observed exceeds 95% baseline: `{str(control['observed_exceeds_quantile95']).lower()}`", "", "## Applicability Boundary", "", f"- Claim scope: `{payload['applicability_boundary'].get('claim_scope', '')}`", ""]
    (ROOT / JSON_ARTIFACT).parent.mkdir(parents=True, exist_ok=True)
    (ROOT / JSON_ARTIFACT).write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    (ROOT / REPORT_ARTIFACT).write_text("\n".join(lines), encoding="utf-8")
def main() -> None:
    payload = _verdict_payload(_load_source_payload())
    _write_payload(payload)
    print(f"wrote {JSON_ARTIFACT}")
    print(f"wrote {REPORT_ARTIFACT}")
    print(f"monotonicity={payload['monotonicity_conclusion']['result']}")
if __name__ == "__main__":
    main()
