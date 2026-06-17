Rebase resolve PR 1544

Changed files:
- papers/bedc-quality-lab/bedc_quality_lab/tasks/__init__.py
- papers/bedc-quality-lab/bedc_quality_lab/tasks/jepa_wm_l1.py
- papers/bedc-quality-lab/scripts/run_jepa_wm_l1.py
- papers/bedc-quality-lab/tests/test_jepa_wm_l1.py

Resolution:
- Kept the canonical JEPA-WM-L1 report path from the base branch.
- Preserved the PR run-local admission contract through `load_observation`, run-local `build_payload`, run-local artifact writing, and `--input` CLI mode.
- Combined both JEPA-WM-L1 test surfaces.

Verification:
- `PYTHONPATH=papers/bedc-quality-lab pytest -q papers/bedc-quality-lab/tests/test_jepa_wm_l1.py`
- `PYTHONPATH=papers/bedc-quality-lab pytest -q papers/bedc-quality-lab/tests/test_jepa_wm_l1_evaluator_calibration.py`
- `PYTHONPATH=papers/bedc-quality-lab pytest -q papers/bedc-quality-lab/tests/test_canonical_reports.py -k 'jepa_wm_l1_admission or jepa_wm_l1_evaluator_calibration'`

Unresolved risk:
- Full repository verification was not run; this worker only ran the smallest relevant quality-lab checks for the resolved conflict surface.

⟦AI:AUTO-LOOP⟧
REBASE_RESOLVE_DONE:1544:resolved
