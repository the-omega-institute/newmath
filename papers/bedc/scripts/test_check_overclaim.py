import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from check_overclaim import OverclaimLedger, scan_overclaims


def _write_ledger(root: Path, entries: list[dict]) -> Path:
    path = root / "rh_claim_ledger.json"
    path.write_text(
        json.dumps(
            {
                "schema_id": "bedc-rh-claim-ledger",
                "entries": entries,
            },
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )
    return path


def test_unregistered_rh_output_bundle_is_reported(tmp_path):
    parts = tmp_path / "parts" / "visions" / "rh"
    parts.mkdir(parents=True)
    tex = parts / "claim.tex"
    tex.write_text(
        "A constructive proof of RH supplies a Riemann-von Mangoldt counting function.\n",
        encoding="utf-8",
    )
    ledger = OverclaimLedger.from_path(_write_ledger(tmp_path, []), tmp_path)

    findings = scan_overclaims(tmp_path, ledger)

    assert len(findings) == 1
    assert findings[0].family == "F1"
    assert findings[0].line == 1


def test_scoped_reparametrization_entry_allows_rh_equivalence(tmp_path):
    parts = tmp_path / "parts" / "visions" / "rh"
    parts.mkdir(parents=True)
    tex = parts / "prime.tex"
    tex.write_text(
        "\\label{prop:rh-prime-balanced-equivalent}\n"
        "Within this scoped fixed-line readout, PrimeBalancedRH is equivalent to RH.\n",
        encoding="utf-8",
    )
    ledger = OverclaimLedger.from_path(
        _write_ledger(
            tmp_path,
            [
                {
                    "file": "parts/visions/rh/prime.tex",
                    "anchor": "prop:rh-prime-balanced-equivalent",
                    "claim_class": "reparametrization",
                    "structure_used": "fixed-line prime-unitary readout",
                    "scope_status": "scoped",
                    "note": "Scope-limited fixed-line readout.",
                }
            ],
        ),
        tmp_path,
    )

    findings = scan_overclaims(tmp_path, ledger)

    assert findings == []


def test_axiom_necessity_language_is_reported(tmp_path):
    parts = tmp_path / "parts" / "visions" / "rh"
    parts.mkdir(parents=True)
    tex = parts / "axiom.tex"
    tex.write_text(
        "This route mathematically requires Classical.choice in the object itself.\n",
        encoding="utf-8",
    )
    ledger = OverclaimLedger.from_path(_write_ledger(tmp_path, []), tmp_path)

    findings = scan_overclaims(tmp_path, ledger)

    assert len(findings) == 1
    assert findings[0].family == "F2"


def test_axiom_necessity_language_is_not_ledger_allowlisted(tmp_path):
    parts = tmp_path / "parts" / "visions" / "rh"
    parts.mkdir(parents=True)
    tex = parts / "axiom.tex"
    tex.write_text(
        "\\label{bad-axiom-necessity}\n"
        "This route mathematically requires Classical.choice in the object itself.\n",
        encoding="utf-8",
    )
    ledger = OverclaimLedger.from_path(
        _write_ledger(
            tmp_path,
            [
                {
                    "file": "parts/visions/rh/axiom.tex",
                    "anchor": "bad-axiom-necessity",
                    "claim_class": "conditional",
                    "structure_used": "not applicable",
                    "scope_status": "scoped",
                    "note": "F2 wording cannot be allowlisted.",
                }
            ],
        ),
        tmp_path,
    )

    findings = scan_overclaims(tmp_path, ledger)

    assert len(findings) == 1
    assert findings[0].family == "F2"
