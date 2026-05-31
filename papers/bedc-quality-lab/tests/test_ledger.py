from bedc_quality_lab.debt import assess_debt
from bedc_quality_lab.ledger import derive_ledger_gaps, format_ledger_gaps


def test_ledger_gaps_derive_from_debt_and_specs():
    source_spec = {
        "name": "gaussian-ou-toy-world",
        "sample_count": 384,
        "mixing": "sinusoidal-parabolic-shear",
    }
    classifier_spec = {
        "name": "tiny-mlp-2-128-128-2",
        "output_dim": 2,
        "training": "align-cov-mean",
    }
    stability_spec = {
        "name": "fixed-seed-single-source",
        "seed": 23,
        "pair_process": "ornstein-uhlenbeck",
    }
    metrics = {"approx_identifiability_proxy": 0.8}
    assessment = assess_debt(metrics, source_spec, classifier_spec, stability_spec)

    gaps = derive_ledger_gaps(metrics, source_spec, classifier_spec, stability_spec, assessment)
    rows = format_ledger_gaps(gaps)

    assert rows
    assert all(row.startswith("residue=") for row in rows)
    assert all("; severity=" in row for row in rows)
    assert all("; status=" in row for row in rows)
    assert any(gap.residue == "source-coverage" and gap.status in {"open", "partial"} for gap in gaps)
    assert any(
        gap.residue == "mixing-family-coverage" and gap.status in {"open", "partial"}
        for gap in gaps
    )
    assert any(
        gap.residue == "global-claim-boundary" and gap.status in {"open", "partial"}
        for gap in gaps
    )
