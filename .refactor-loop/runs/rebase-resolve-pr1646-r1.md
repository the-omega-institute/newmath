Changed files:
- papers/bedc-quality-lab/README.md

Resolution:
- Kept the local-source discovery command for quality-lab script entrypoints.
- Removed the static generated script inventory from the conflict block.

Verification:
- `grep -n '<<<<<<<\|=======\|>>>>>>>' papers/bedc-quality-lab/README.md || true`
- `python3 -m compileall -q papers/bedc-quality-lab/bedc_quality_lab/schema.py tools/automath_newmath_bridge/validate_bridge_manifest.py tools/test_bridge_manifest_schema_policy.py papers/bedc-quality-lab/tests/test_schema.py`
- `python3 - <<'PY' ... validate_bridge_manifest.py default-field smoke ... PY`

Unresolved risk:
- `python3 -m pytest -q papers/bedc-quality-lab/tests/test_schema.py tools/test_bridge_manifest_schema_policy.py` could not run because this Python environment has no `pytest` module.

⟦AI:AUTO-LOOP⟧
REBASE_RESOLVE_DONE:1646:resolved
