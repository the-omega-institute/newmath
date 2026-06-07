#!/usr/bin/env python3
"""Project mixing-family sweep rows into discovery predicates."""

from __future__ import annotations

import json
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

SOURCE_JSON_ARTIFACT = "reports/mixing_family_sweep.json"
SOURCE_REPORT_ARTIFACT = "reports/mixing_family_sweep.md"
JSON_ARTIFACT = "reports/mixing_family_discovery.json"
REPORT_ARTIFACT = "reports/mixing_family_discovery.md"
SCOPE_SEAL = CLOSED_CLAIM_SCOPE_SEAL
CONTROL_SEED = 53320260602
CONTROL_PERMUTATIONS = 200


def _load_source_payload(path: Path | None = None) -> dict[str, Any]:
    payload = json.loads((ROOT / SOURCE_JSON_ARTIFACT if path is None else path).read_text(encoding="utf-8"))
    _validate_grid(payload)
    return payload


def _validate_grid(payload: dict[str, Any]) -> None:
    families = list(payload.get("config", {}).get("families", []))
    seeds = [int(seed) for seed in payload.get("config", {}).get("seeds", [])]
    metrics = list(payload.get("config", {}).get("metric_names", []))
    if not families or not seeds or not metrics:
        raise ValueError("mixing-family payload must declare config families, seeds, and metric_names")
    records = payload.get("records", [])
    expected = {(family, seed) for family in families for seed in seeds}
    seen = {(row.get("mixing"), int(row.get("seed"))) for row in records}
    if seen != expected or len(records) != len(expected):
        raise ValueError("mixing-family payload lacks a complete family/seed grid")
    aggregates = set(payload.get("family_aggregates", {}))
    if aggregates != set(families):
        raise ValueError("mixing-family payload lacks family aggregates for the configured families")
    for row in records:
        if row.get("status") != "ok" or row.get("source_mixing") != row.get("mixing"):
            raise ValueError("mixing-family rows must be ok and source-aligned")
        row_metrics = row.get("metrics", {})
        envelope_metrics = row.get("envelope_projection", {}).get("metrics", {})
        missing = [name for name in metrics if name not in row_metrics or name not in envelope_metrics]
        if missing:
            raise ValueError(f"mixing-family row lacks metrics: {', '.join(missing)}")
        for name in metrics:
            if float(row_metrics[name]) != float(envelope_metrics[name]):
                raise ValueError(f"mixing-family metric mismatch for {row['mixing']} seed {row['seed']} metric {name}")


def _source_id(seed: int, metric: str) -> str:
    return f"seed:{seed}:metric:{metric}"


def _ledger_row(pair: tuple[str, str]) -> LedgerRowKey:
    return LedgerRowKey("classifier", f"{pair[0]}->{pair[1]}")


def _all_certified(rows: list[dict[str, Any]]) -> bool:
    return all(row.get("envelope_projection", {}).get("classifier_spec", {}).get("cert_status") == "certified" for row in rows)


def _relation(records: list[dict[str, Any]], metrics: list[str]) -> frozenset[tuple[str, str, str]]:
    return frozenset(
        (_source_id(int(row["seed"]), metric), _source_id(int(row["seed"]), metric), f"{float(row['metrics'][metric]):.12g}")
        for row in records
        for metric in metrics
    )


def _state(family: str, records: list[dict[str, Any]], metrics: list[str], surface: frozenset[tuple[str, str]]) -> ClassifierState:
    source_ids = frozenset(_source_id(int(row["seed"]), metric) for row in records for metric in metrics)
    return ClassifierState(
        source_ids=source_ids,
        pattern_id=f"mixing-family-{family}",
        ledger_policy=frozenset(_ledger_row(pair) for pair in surface),
        relation=_relation(records, metrics),
        certificate={"cert_status": "certified" if _all_certified(records) else "not-certified", "source_artifact": SOURCE_JSON_ARTIFACT},
        surface_used=surface,
        verification_status="artifact-checked",
        record_count=len(source_ids),
        feature_count=len(metrics),
        notation="seed-metric-self-pair",
    )


def _target_debt(rows: list[dict[str, Any]]) -> float:
    values = [float(row.get("mixing_debt_item", {}).get("score", 0.0)) for row in rows]
    return float(sum(values) / len(values)) if values else 0.0


def _project_family(payload: dict[str, Any], target_family: str) -> dict[str, Any]:
    seeds, metrics = [int(seed) for seed in payload["config"]["seeds"]], list(payload["config"]["metric_names"])
    baseline = str(payload["negative_result_summary"]["baseline_family"])
    by_key = {(str(row["mixing"]), int(row["seed"])): row for row in payload["records"]}
    base_rows = [by_key[(baseline, seed)] for seed in seeds]
    target_rows = [by_key[(target_family, seed)] for seed in seeds]
    base_relation = _relation(base_rows, metrics)
    target_relation = _relation(target_rows, metrics)
    changed = frozenset((left, right) for left, right, value in target_relation if (left, right, value) not in base_relation)
    ledger_rows = frozenset(_ledger_row(pair) for pair in changed)
    passage = ClassifierPassage(_state(baseline, base_rows, metrics, frozenset()), _state(target_family, target_rows, metrics, changed), ledger_rows)
    delta_count = len(classifier_surface_delta(passage))
    benefit = max(0.0, sum(float(row["metrics"]["quality_q"]) for row in target_rows) / len(target_rows) - sum(float(row["metrics"]["quality_q"]) for row in base_rows) / len(base_rows))
    claim = DiscoveryClaim(
        passage=passage,
        benefit_terms={"quality_q_signal": benefit},
        score_terms={"public_projection_cost": 0.03, "changed_cell_cost": 0.001 * delta_count},
        debt_terms={"mixing_family_debt": _target_debt(target_rows), "projection_floor": 0.02 if delta_count else 0.0},
        ledger_required_rows=ledger_rows,
        ledger_recorded_rows=ledger_rows,
        public_cost_protocol=True,
        scope_sealed=closed_claim_scope_seal(SCOPE_SEAL),
        not_claimed_boundary=frozenset({"formal-bedc-closure", "non-gaussian-mixing-generalization", "aggregate-surface-claim"}),
        benefit_modes=frozenset({"quality_q_signal"}),
        reproducible_evidence=True,
    )
    return {"family": target_family, "passage": passage, "claim": claim, "baseline_rows": base_rows, "target_rows": target_rows}


def _blockers(family: str, projection: dict[str, Any], delta: frozenset[tuple[str, str]], net: float, positive: bool) -> list[dict[str, Any]]:
    blockers: list[dict[str, Any]] = []
    for arm, rows in (("baseline", projection["baseline_rows"]), ("target", projection["target_rows"])):
        for row in rows:
            if row.get("envelope_projection", {}).get("classifier_spec", {}).get("cert_status") != "certified":
                blockers.append({"family": family, "arm": arm, "seed": int(row["seed"]), "reason": "not-certified"})
    if not delta:
        blockers.append({"family": family, "reason": "empty-surface-delta"})
    if net <= 0.0:
        blockers.append({"family": family, "reason": "net-nonpositive", "net_information": net})
    if not positive:
        blockers.append({"family": family, "reason": "predicate-not-positive"})
    return blockers


def _verdict_row(projection: dict[str, Any]) -> dict[str, Any]:
    family, passage, claim = projection["family"], projection["passage"], projection["claim"]
    delta, net = classifier_surface_delta(passage), net_information(claim)
    structural, positive = structural_discovery(passage), positive_discovery(claim)
    verdict = "positive" if positive and delta and net > 0.0 else "negative" if structural and delta and net <= 0.0 else "compression" if not delta else "not_positive"
    return {
        "family": family,
        "surface_delta_count": len(delta),
        "surface_delta": [list(pair) for pair in sorted(delta)],
        "source_ids": sorted(passage.source.source_ids),
        "shift_information": shift_information(passage),
        "structural_discovery": structural,
        "net_positive_signal": net > 0.0,
        "net_information": net,
        "positive_discovery": positive,
        "verdict": verdict,
        "blockers": _blockers(family, projection, delta, net, positive),
    }


def _matched_random_baseline(rows: list[dict[str, Any]]) -> dict[str, Any]:
    rng = random.Random(CONTROL_SEED)
    nets = [float(row["net_information"]) for row in rows]
    observed = sum(1 for row in rows if row["positive_discovery"])
    controls = []
    for _ in range(CONTROL_PERMUTATIONS):
        shuffled = [net * (-1 if rng.random() < 0.5 else 1) for net in nets]
        controls.append(sum(1 for net in shuffled if net > 0.0))
    controls.sort()
    return {"seed": CONTROL_SEED, "permutations": CONTROL_PERMUTATIONS, "method": "matched-sign-flip-net-information", "observed_positive_count": observed, "mean_positive_count": sum(controls) / len(controls), "max_positive_count": max(controls), "quantile95_positive_count": controls[min(len(controls) - 1, int(0.95 * len(controls)) - 1)]}


def _positive_probe_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    positives = [row["family"] for row in rows if row["positive_discovery"]]
    return {"second_positive_probe_found": bool(positives), "positive_families": positives, "answer": "H1" if positives else "H0", "criterion": "H1 iff any non-baseline family has positive_discovery true under the existing predicates"}


def _verdict_payload(source_payload: dict[str, Any]) -> dict[str, Any]:
    baseline = str(source_payload["negative_result_summary"]["baseline_family"])
    targets = [family for family in source_payload["config"]["families"] if family != baseline]
    rows = [_verdict_row(_project_family(source_payload, family)) for family in targets]
    return {
        "artifact": JSON_ARTIFACT,
        "source_artifacts": {"source_json_artifact": SOURCE_JSON_ARTIFACT, "source_report_artifact": SOURCE_REPORT_ARTIFACT, "source_runner": "scripts/run_mixing_family_sweep.py"},
        "report": REPORT_ARTIFACT,
        "projection_script": "scripts/run_mixing_family_discovery.py",
        "generated_from": {"artifact": SOURCE_JSON_ARTIFACT, "source_runner": "scripts/run_mixing_family_sweep.py", "record_count": len(source_payload["records"])},
        "scope_seal": SCOPE_SEAL,
        "baseline_family": baseline,
        "verdicts": rows,
        "positive_probe_summary": _positive_probe_summary(rows),
        "certification_blockers": [blocker for row in rows for blocker in row["blockers"]],
        "matched_random_baseline": _matched_random_baseline(rows),
        "applicability_boundary": source_payload.get("applicability_boundary", {}),
    }


def _write_payload(payload: dict[str, Any]) -> None:
    lines = ["# Mixing-family discovery projection", "", f"- Source JSON artifact: `{payload['source_artifacts']['source_json_artifact']}`", f"- Projection script: `{payload['projection_script']}`", f"- Baseline family: `{payload['baseline_family']}`", f"- Answer: `{payload['positive_probe_summary']['answer']}`", "", "## Family Verdicts", "", "| family | net information | surface delta | shift info | structural | positive | verdict |", "| --- | ---: | ---: | ---: | --- | --- | --- |"]
    lines += [f"| `{row['family']}` | {row['net_information']:.6f} | {row['surface_delta_count']} | {row['shift_information']} | `{str(row['structural_discovery']).lower()}` | `{str(row['positive_discovery']).lower()}` | `{row['verdict']}` |" for row in payload["verdicts"]]
    lines += ["", "## Positive Probe Summary", "", f"- Second positive probe found: `{str(payload['positive_probe_summary']['second_positive_probe_found']).lower()}`", f"- Positive families: `{', '.join(payload['positive_probe_summary']['positive_families'])}`", "", "## Matched Random Baseline", "", f"- Seed: `{payload['matched_random_baseline']['seed']}`", f"- Permutations: `{payload['matched_random_baseline']['permutations']}`", f"- Observed positive count: `{payload['matched_random_baseline']['observed_positive_count']}`", "", "## Applicability Boundary", "", f"- Claimed scope: `{payload['applicability_boundary'].get('claimed_scope', payload['applicability_boundary'].get('claimed_scope', ''))}`", ""]
    (ROOT / JSON_ARTIFACT).parent.mkdir(parents=True, exist_ok=True)
    (ROOT / JSON_ARTIFACT).write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    (ROOT / REPORT_ARTIFACT).write_text("\n".join(lines), encoding="utf-8")


def main() -> None:
    payload = _verdict_payload(_load_source_payload())
    _write_payload(payload)
    print(f"wrote {JSON_ARTIFACT}")
    print(f"wrote {REPORT_ARTIFACT}")
    print(f"answer={payload['positive_probe_summary']['answer']}")


if __name__ == "__main__":
    main()
