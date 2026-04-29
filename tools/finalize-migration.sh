#!/usr/bin/env bash
set -euo pipefail

echo "[1/6] Running migration audit..."
if ! python3 tools/migration-audit.py; then
  echo "FAIL: audit did not pass. Fix issues or extend allowlists. Aborting." >&2
  exit 1
fi

echo "[2/6] Running audit self-test (.source ↔ .source)..."
if ! python3 tools/migration-audit.py --source-dir .source/BEDC_Master_Project_v1_5_5 --target-dir .source/BEDC_Master_Project_v1_5_5/parts --lean-dir .source/BEDC_Master_Project_v1_5_5/lean; then
  echo "FAIL: audit self-test broken (audit script bug). Aborting." >&2
  exit 1
fi

echo "[3/6] Checking tools/eyeball-checklist.md for unsigned items..."
TODO_COUNT=$(grep -c 'TODO' tools/eyeball-checklist.md || true)
if [ "$TODO_COUNT" -gt 0 ]; then
  echo "FAIL: $TODO_COUNT eyeball-checklist rows still TODO. Sign off each row before running this script." >&2
  exit 1
fi

echo ""
echo "*** READY TO DELETE .source/ — this is IRREVERSIBLE ***"
echo "Audit: PASS  Self-test: PASS  Eyeball-checklist: signed"
echo ""
read -rp "Type DELETE to confirm: " CONFIRM
if [ "$CONFIRM" != "DELETE" ]; then
  echo "Aborted (no changes made)." >&2
  exit 1
fi

echo "[4/6] Deleting .source/..."
rm -rf .source

echo "[5/6] Removing /.source/ line from .gitignore..."
# Cross-platform in-place edit: BSD sed on macOS needs '' after -i; GNU sed accepts -i.bak
if sed --version >/dev/null 2>&1; then
  sed -i.bak '/^\/\.source\/$/d' .gitignore
else
  sed -i '' '/^\/\.source\/$/d' .gitignore
fi
rm -f .gitignore.bak

echo "[6/6] Re-running lake build + make to verify no .source dependency..."
(cd lean4 && lake build) || { echo "FAIL: lake build broke after .source deletion. Restore from git stash or revert." >&2; exit 1; }
(cd papers/bedc && make) || { echo "FAIL: make broke after .source deletion." >&2; exit 1; }

echo ""
echo "*** .source/ deleted, post-deletion build passes ***"
echo "Next: stage + commit:"
echo "  git add -u .gitignore"
echo "  git rm -r --cached .source 2>/dev/null || true"
echo "  git commit -m 'chore: remove .source/ after migration audit pass'"
