Changed files:
- papers/bedc-quality-lab/README.md

Resolution:
- Merged the script inventory conflict by preserving `run_bedc_multistep_latent_prediction.py` from the PR side and adding `run_sti_admission.py` from the rebased base side.

Verification:
- `python3 -m py_compile papers/bedc-quality-lab/scripts/run_sti_admission.py papers/bedc-quality-lab/bedc_quality_lab/tasks/sti.py`
- `python3 - <<'PY' ... PY` checked that the README contains both inventory entries and no conflict markers.

Unresolved risk:
- `python3 -m pytest -q papers/bedc-quality-lab/tests/test_sti_admission.py papers/bedc-quality-lab/tests/test_run_canonical_reports.py` could not run because this environment has no `pytest` module.

⟦AI:AUTO-LOOP⟧
REBASE_RESOLVE_DONE:1637:resolved
