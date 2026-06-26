#!/usr/bin/env python3
"""Project the spectral-ablation hinge report into discovery predicates."""

from __future__ import annotations

import json
import math
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.classifier_shift import (
    ClassifierPassage,
    ClassifierState,
    classifier_surface_delta,
    shift_information,
    structural_discovery,
)
from bedc_quality_lab.discovery import DiscoveryClaim, net_information, positive_discovery
from bedc_quality_lab.ledger import LedgerRowKey
from bedc_quality_lab.scope import CLOSED_CLAIM_SCOPE_SEAL, closed_claim_scope_seal


SOURCE_JSON_ARTIFACT = "reports/spectral_ablation_hinge.json"
SOURCE_REPORT_ARTIFACT = "reports/spectral_ablation_hinge.md"
JSON_ARTIFACT = "reports/spectral_ablation_discovery.json"
REPORT_ARTIFACT = "reports/spectral_ablation_discovery.md"
BEFORE_ARM = "vanilla"
SCOPE_SEAL = CLOSED_CLAIM_SCOPE_SEAL


def _load_payload(path: Path | None = None) -> dict[str, Any]:
    payload_path = ROOT / SOURCE_JSON_ARTIFACT if path is None else path
    payload = json.loads(payload_path.read_text(encoding="utf-8"))
    arms = payload.get("arms", [])
    if not arms or not any(arm.get("name") == BEFORE_ARM for arm in arms):
        raise ValueError("spectral-ablation payload must contain vanilla arm")
    metric_names = payload.get("config", {}).get("metric_names", [])
    if not metric_names:
        raise ValueError("spectral-ablation payload must contain metric_names")
    for arm in arms:
        projection = arm.get("envelope_projection", {})
        metrics = projection.get("metrics", {})
        if any(name not in metrics for name in metric_names):
            raise ValueError(f"arm lacks projected metrics: {arm.get('name')}")
    return payload


def _project_arm(
    payload: dict[str, Any],
    arm_name: str,
    *,
    observed_degradation_score: float | None = None,
    value_suffix: str = "",
) -> dict[str, Any]:
    arms = {arm["name"]: arm for arm in payload["arms"]}
    before = arms[BEFORE_ARM]
    after = arms[arm_name]
    metric_names = tuple(str(name) for name in payload["config"]["metric_names"])
    source_ids = frozenset(f"metric:{name}{value_suffix}" for name in metric_names)

    def rows(arm: dict[str, Any]) -> frozenset[tuple[str, str, str]]:
        metrics = arm["envelope_projection"]["metrics"]
        return frozenset((f"metric:{name}{value_suffix}", f"metric:{name}{value_suffix}", f"{float(metrics[name]):.12g}") for name in metric_names)

    surface = frozenset((source_id, source_id) for source_id in source_ids)
    ledger_rows = frozenset(LedgerRowKey("classifier", f"{left}->{right}") for left, right in surface)
    state_args = {"source_ids": source_ids, "certificate": {"cert_status": "certified", "source_artifact": SOURCE_JSON_ARTIFACT}, "verification_status": "artifact-checked", "record_count": len(source_ids), "feature_count": len(metric_names), "notation": "metric-self-pair"}
    source = ClassifierState(pattern_id=f"spectral-ablation-before-{BEFORE_ARM}", ledger_policy=frozenset(), relation=rows(before), surface_used=frozenset(), **state_args)
    target = ClassifierState(pattern_id=f"spectral-ablation-after-{arm_name}", ledger_policy=ledger_rows, relation=rows(after), surface_used=surface, **state_args)
    passage = ClassifierPassage(source=source, target=target, recorded_rows=ledger_rows)
    delta_count = len(classifier_surface_delta(passage))
    score = float(after["observed_degradation_score"] if observed_degradation_score is None else observed_degradation_score)
    claim = DiscoveryClaim(
        passage=passage,
        benefit_terms={"spectral_improvement": max(0.0, -score)},
        score_terms={"projection_surface": 0.01 * delta_count},
        debt_terms={"spectral_degradation": max(0.0, score), "classifier_surface_rows": 0.01 * delta_count},
        ledger_required_rows=ledger_rows,
        ledger_recorded_rows=ledger_rows,
        public_cost_protocol=True,
        scope_sealed=closed_claim_scope_seal(SCOPE_SEAL),
        not_claimed_boundary=frozenset({"formal-bedc-closure", "biological-killed-walk-coverage"}),
        benefit_modes=frozenset({"spectral_improvement"}),
        reproducible_evidence=True,
    )
    return {"arm": after, "passage": passage, "claim": claim, "score": score}


def _verdict_payload(payload: dict[str, Any]) -> dict[str, Any]:
    verdicts = []
    for arm in payload["arms"]:
        if arm["name"] == BEFORE_ARM:
            continue
        projection = _project_arm(payload, arm["name"])
        passage = projection["passage"]
        claim = projection["claim"]
        delta = classifier_surface_delta(passage)
        structural = structural_discovery(passage)
        positive = positive_discovery(claim)
        net = net_information(claim)
        if positive:
            verdict = "positive"
        elif structural and delta and net < 0.0:
            verdict = "negative"
        else:
            verdict = "compression"
        verdicts.append(
            {
                "arm": arm["name"],
                "family": arm["family"],
                "deletion_axes": arm["deletion_axes"],
                "observed_degradation_score": projection["score"],
                "surface_delta_count": len(delta),
                "surface_delta": [list(pair) for pair in sorted(delta)],
                "shift_information": shift_information(passage),
                "structural_discovery": structural,
                "net_information": net,
                "positive_discovery": positive,
                "verdict": verdict,
            }
        )

    net_by_arm = {row["arm"]: float(row["net_information"]) for row in verdicts}
    pairs = [dict(pair, net_information=net_by_arm[pair["arm"]]) for pair in payload["rank_correlation"]["pairs"] if pair["arm"] in net_by_arm]

    def ranks(values: list[float]) -> list[float]:
        indexed = sorted(enumerate(values), key=lambda item: item[1], reverse=True)
        out = [0.0] * len(values)
        for rank, (index, _) in enumerate(indexed, start=1):
            out[index] = float(rank)
        return out

    def pearson(xs: list[float], ys: list[float]) -> float:
        if len(xs) < 2:
            return math.nan
        xm = sum(xs) / len(xs)
        ym = sum(ys) / len(ys)
        xn = math.sqrt(sum((x - xm) ** 2 for x in xs))
        yn = math.sqrt(sum((y - ym) ** 2 for y in ys))
        return math.nan if xn == 0.0 or yn == 0.0 else sum((x - xm) * (y - ym) for x, y in zip(xs, ys, strict=True)) / (xn * yn)

    observed = [float(pair["observed_degradation_score"]) for pair in pairs]
    nets = [float(pair["net_information"]) for pair in pairs]
    rank_correlation = {
        "source_hinge": payload["rank_correlation"],
        "method": "hinge-observed-degradation-vs-discovery-net-information",
        "spearman": pearson(ranks(observed), ranks(nets)),
        "pairs": pairs,
    }
    return {
        "artifact": JSON_ARTIFACT,
        "source_artifacts": {"source_json_artifact": SOURCE_JSON_ARTIFACT, "source_report_artifact": SOURCE_REPORT_ARTIFACT, "source_runner": "scripts/run_spectral_ablation_hinge.py"},
        "report": REPORT_ARTIFACT,
        "projection_script": "scripts/run_spectral_ablation_discovery.py",
        "generated_from": {"artifact": SOURCE_JSON_ARTIFACT, "generated_at": payload.get("generated_at")},
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "scope_seal": SCOPE_SEAL,
        "arms": [row["name"] for row in payload["arms"]],
        "verdicts": verdicts,
        "rank_correlation": rank_correlation,
        "matched_random_baseline": {
            "source": payload["negative_control_summary"],
            "verdicts": [row for row in verdicts if row["family"] == "matched-random-control"],
        },
        "applicability_boundary": payload["applicability_boundary"],
    }


def _write_payload(payload: dict[str, Any]) -> None:
    json_path = ROOT / JSON_ARTIFACT
    report_path = ROOT / REPORT_ARTIFACT
    lines = ["# Spectral-ablation discovery projection", "", f"- Source JSON artifact: `{payload['source_artifacts']['source_json_artifact']}`", f"- Projection script: `{payload['projection_script']}`", "", "## Verdicts", "", "| arm | family | degradation | surface delta | shift info | net | structural | positive | verdict |", "| --- | --- | ---: | ---: | ---: | ---: | --- | --- | --- |"]
    for row in payload["verdicts"]:
        lines.append(
            f"| `{row['arm']}` | `{row['family']}` | {row['observed_degradation_score']:.6f} | "
            f"{row['surface_delta_count']} | {row['shift_information']} | {row['net_information']:.6f} | "
            f"`{str(row['structural_discovery']).lower()}` | `{str(row['positive_discovery']).lower()}` | `{row['verdict']}` |"
        )
    lines.extend(["", "## Rank Correlation", "", f"- Method: `{payload['rank_correlation']['method']}`", f"- Spearman: `{payload['rank_correlation']['spearman']:.6f}`", f"- Source hinge Spearman: `{payload['rank_correlation']['source_hinge']['spearman']:.6f}`", "", "## Matched Random Baseline", "", f"- Treatment score: `{payload['matched_random_baseline']['source']['treatment_score']:.6f}`", f"- Max control score: `{payload['matched_random_baseline']['source']['max_control_score']:.6f}`", f"- Treatment better than all controls: `{payload['matched_random_baseline']['source']['treatment_better_than_all_controls']}`", "", "## Applicability Boundary", "", f"- Claimed scope: `{payload['applicability_boundary']['claimed_scope']}`", f"- Not claimed: {payload['applicability_boundary']['not_claimed']}", ""])
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    report_path.write_text("\n".join(lines), encoding="utf-8")


def main() -> None:
    payload = _verdict_payload(_load_payload())
    _write_payload(payload)
    print(f"wrote {JSON_ARTIFACT}")
    print(f"wrote {REPORT_ARTIFACT}")


if __name__ == "__main__":
    main()
