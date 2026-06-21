#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LEAN_DIR="$ROOT/lean4"
TMP_DIR="$(mktemp -d "${TMPDIR:-/tmp}/bedc-bridge-negative.XXXXXX")"
trap 'rm -rf "$TMP_DIR"' EXIT

expect_fail() {
  local token="$1"
  shift
  local output
  local status
  set +e
  output="$("$@" 2>&1)"
  status=$?
  set -e
  if [[ "$status" -eq 0 ]]; then
    echo "expected command to fail with token: $token" >&2
    exit 1
  fi
  if ! grep -Fq "$token" <<<"$output"; then
    echo "command failed, but not for the expected gate: $token" >&2
    echo "$output" >&2
    exit 1
  fi
  echo "[negative] observed $token"
}

copy_lean_fixture() {
  local name="$1"
  cp "$ROOT/tests/negative/$name.lean" "$TMP_DIR/$name.lean"
}

copy_lean_fixture GateA
copy_lean_fixture GateBMissingAttr
copy_lean_fixture GateBForeignPrimitive
copy_lean_fixture GateBMissingDep

cat > "$TMP_DIR/GateBCutpointGraft.lean" <<'EOF'
import BedcMathlibBridge.CI.Policy
import BedcGate.Audit
import BEDC.Derived.PrimeUp

namespace BedcMathlibBridge.Negative

open BedcMathlibBridge.Constructive.Int

@[bedcDerived BEDC.Derived.PrimeUp.NatMul]
def cutpointGraftMul (x y : CInt) : CInt :=
  CInt.ofInt (x.toInt * y.toInt)

end BedcMathlibBridge.Negative

run_cmd do
  BedcGate.audit BedcMathlibBridge.CI.policy
EOF

expect_fail BEDC_GATE_A_AXIOM \
  bash -c "cd '$LEAN_DIR' && lake env lean '$TMP_DIR/GateA.lean'"

expect_fail BEDC_GATE_B_MISSING_ATTR \
  bash -c "cd '$LEAN_DIR' && lake env lean '$TMP_DIR/GateBMissingAttr.lean'"

expect_fail BEDC_GATE_B_FOREIGN_PRIMITIVE \
  bash -c "cd '$LEAN_DIR' && lake env lean '$TMP_DIR/GateBForeignPrimitive.lean'"

expect_fail BEDC_GATE_B_MISSING_DEP \
  bash -c "cd '$LEAN_DIR' && lake env lean '$TMP_DIR/GateBMissingDep.lean'"

expect_fail BEDC_GATE_B_MISSING_DEP \
  bash -c "cd '$LEAN_DIR' && lake env lean '$TMP_DIR/GateBCutpointGraft.lean'"

cp "$ROOT/tests/negative/gate_c_missing.md" "$TMP_DIR/MISSING_IN_BEDC.md"
cp "$ROOT/tests/negative/gate_c_matrix.json" "$TMP_DIR/matrix.json"

expect_fail BEDC_GATE_C_SYNC \
  python3 "$ROOT/scripts/check_gap_sync.py" "$TMP_DIR/MISSING_IN_BEDC.md" "$TMP_DIR/matrix.json"

echo "[negative] all expected failures matched gate tokens"
