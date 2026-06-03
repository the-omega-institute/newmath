import json
from pathlib import Path

from bedc_quality_lab.claim_terms import FORBIDDEN_POSITIVE_CLAIM_TERMS
from scripts import run_canonical_reports as canonical


ROOT = Path(__file__).resolve().parents[1]
CANONICAL = ROOT / "reports" / "canonical"
FREEZE_MARKDOWN_SURFACES = (
    ROOT / "docs" / "bedc_quality_lab_v1_alpha.md",
    ROOT / "docs" / "claims_and_nonclaims.md",
    ROOT / "docs" / "artifact_manifest.md",
    CANONICAL / "index.md",
    CANONICAL / "quality-scorecard.md",
)
HIDDEN_SCORECARD_TERMS = (
    "weighted_total",
    "total_score",
    "grade",
    "hidden weighting",
    "hidden cost weight",
)


def _discovery_rows_by_report() -> dict[str, dict]:
    payload = json.loads((CANONICAL / "discovery_map.json").read_text(encoding="utf-8"))
    return {row["report"]: row for row in payload["rows"]}


def _walk_keys(value):
    if isinstance(value, dict):
        for key, cell in value.items():
            yield key
            yield from _walk_keys(cell)
    elif isinstance(value, list):
        for cell in value:
            yield from _walk_keys(cell)


def test_hg_v1a_discovery_map_levels_are_frozen():
    assert (CANONICAL / "discovery_map.json").exists()
    assert (CANONICAL / "index.md").exists()
    assert "## freeze status pointers" in (CANONICAL / "index.md").read_text(encoding="utf-8")

    rows = _discovery_rows_by_report()
    assert rows["gap-head-on-h"]["discovery_level"] == "D4"
    assert rows["certificate-guided-discovery"]["discovery_level"] == "DN"
    assert rows["nongaussian-distribution-sweep"]["discovery_level"] == "D1"
    assert rows["anisotropic-ou-sweep"]["discovery_level"] == "D1"


def test_hg_v1a_docs_use_claim_terms_source():
    assert FORBIDDEN_POSITIVE_CLAIM_TERMS
    for path in FREEZE_MARKDOWN_SURFACES:
        assert path.exists(), path
        text = path.read_text(encoding="utf-8").lower()
        hits = [term for term in FORBIDDEN_POSITIVE_CLAIM_TERMS if term.lower() in text]
        assert hits == [], f"{path.relative_to(ROOT)} contains forbidden positive claim terms: {hits}"


def test_hg_v1a_scorecard_has_no_hidden_weight():
    scorecard_json = CANONICAL / "quality-scorecard.json"
    scorecard_md = CANONICAL / "quality-scorecard.md"
    assert scorecard_json.exists()
    assert scorecard_md.exists()

    payload = json.loads(scorecard_json.read_text(encoding="utf-8"))
    markdown = scorecard_md.read_text(encoding="utf-8").lower()
    keys = set(_walk_keys(payload))
    encoded_payload = json.dumps(payload, sort_keys=True).lower()

    for term in HIDDEN_SCORECARD_TERMS:
        assert term not in keys
        assert term not in encoded_payload
        assert term not in markdown

    assert all(spec.json_artifact != "reports/canonical/v1-alpha-freeze-gate.json" for spec in canonical.CANONICAL_REPORTS)
    assert not (CANONICAL / "v1-alpha-freeze-gate.json").exists()
