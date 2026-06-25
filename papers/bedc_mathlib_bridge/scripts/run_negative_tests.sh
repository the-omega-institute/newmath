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

cat > "$TMP_DIR/GateBTransport.lean" <<'EOF'
import BedcMathlibBridge.CI.Policy
import BedcGate.Audit
import Lean

open Lean Elab Command

namespace BedcMathlibBridge.Negative.Transport

open BedcMathlibBridge.Constructive.Int

def transportedMulAnchor : Unit :=
  let _ : Function.Injective (fun x : CInt => x) := fun _ _ h => h
  ()

@[bedcDerived CInt.toInt]
instance instTransportMulCInt : Mul CInt where
  mul x y :=
    let _ := transportedMulAnchor
    CInt.ofInt (x.toInt * y.toInt)

end BedcMathlibBridge.Negative.Transport

def transportPolicy : BedcGate.Policy :=
  { BedcMathlibBridge.CI.policy with
    bridgeDeclPrefix := `BedcMathlibBridge.Negative.Transport,
    bridgeModulePrefix := `BedcMathlibBridge.Negative.Transport,
    ignoredDeclPrefixes := #[] }

run_cmd do
  BedcGate.audit transportPolicy
EOF

expect_fail BEDC_GATE_B_TRANSPORT \
  bash -c "cd '$LEAN_DIR' && lake env lean '$TMP_DIR/GateBTransport.lean'"

mkdir -p "$TMP_DIR/BedcMathlibBridge/Constructive"
cp "$ROOT/tests/negative/BedcMathlibBridge/Constructive/ThinLayerNegative.lean" \
  "$TMP_DIR/BedcMathlibBridge/Constructive/ThinLayerNegative.lean"

expect_fail BEDC_GATE_THIN_LAYER \
  bash -c "cd '$LEAN_DIR' && lake env lean '$TMP_DIR/BedcMathlibBridge/Constructive/ThinLayerNegative.lean'"

cp "$ROOT/tests/negative/gate_c_missing.md" "$TMP_DIR/MISSING_IN_BEDC.md"
cp "$ROOT/tests/negative/gate_c_matrix.json" "$TMP_DIR/matrix.json"

expect_fail BEDC_GATE_C_SYNC \
  python3 "$ROOT/scripts/check_gap_sync.py" "$TMP_DIR/MISSING_IN_BEDC.md" "$TMP_DIR/matrix.json"

cat > "$TMP_DIR/export_missing.md" <<'EOF'
| row_id | BEDC source | mathlib target | bridge status | constructive content | axioms | boundary |
| --- | --- | --- | --- | --- | --- | --- |
| missing-export | fixture | fixture | adequacy(0-axiom) | fixture | axioms=[] | fixture <!-- bedc-bridge-row: {"row_id":"missing-export","kind":"exported_core","mathlib_class":"Dvd","mathlib_instance":"Int.instDvd","export_witness":"BedcMathlibBridge.Negative.missingWitness"} --> |
EOF

expect_fail BEDC_GATE_D_MISSING_WITNESS \
  python3 "$ROOT/scripts/check_export_matrix.py" "$TMP_DIR/export_missing.md"

python3 - "$ROOT/MATRIX.md" "$TMP_DIR/export_unclassified.md" <<'PY'
from pathlib import Path
import sys
src = Path(sys.argv[1]).read_text()
lines = [
    line for line in src.splitlines()
    if '"row_id":"int-repr-generic"' not in line
]
Path(sys.argv[2]).write_text("\n".join(lines) + "\n")
PY

expect_fail BEDC_GATE_D_UNCLASSIFIED \
  python3 "$ROOT/scripts/check_export_matrix.py" "$TMP_DIR/export_unclassified.md"

cat > "$TMP_DIR/GateDAxiomWitness.lean" <<'EOF'
import BedcMathlibBridge.CI.ExportAudit

noncomputable def BedcMathlibBridge.Negative.axiomWitness : Nat :=
  Classical.choice (show Nonempty Nat from ⟨0⟩)

run_cmd do
  BedcMathlibBridge.CI.ExportAudit.audit #[
    { rowId := "axiom-export", witness := `BedcMathlibBridge.Negative.axiomWitness }
  ]
EOF

expect_fail BEDC_GATE_D_AXIOM \
  bash -c "cd '$LEAN_DIR' && lake env lean '$TMP_DIR/GateDAxiomWitness.lean'"

cat > "$TMP_DIR/GateSWeakenedSignature.lean" <<'EOF'
import BedcMathlibBridge.Export.Int
import BedcMathlibBridge.CI.IntMetadata
import Lean

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let some info := getStructureInfo? env `BedcMathlibBridge.Export.Int.IntExportWitness
    | throwError "BEDC_GATE_S_SIGNATURE: missing IntExportWitness"
  let fields := info.fieldInfo.qsort fun a b => Name.quickLt a.fieldName b.fieldName
  let some field := fields[0]?
    | throwError "BEDC_GATE_S_SIGNATURE: missing field"
  let some ci := env.find? field.projFn
    | throwError "BEDC_GATE_S_SIGNATURE: missing projection"
  let actualHash := hash ci.type
  if actualHash == 0 then
    pure ()
  else
    throwError m!"BEDC_GATE_S_SIGNATURE: field `{field.fieldName}` type hash {actualHash}, expected 0"
EOF

expect_fail BEDC_GATE_S_SIGNATURE \
  bash -c "cd '$LEAN_DIR' && lake env lean '$TMP_DIR/GateSWeakenedSignature.lean'"

cat > "$TMP_DIR/GateDOrphan.lean" <<'EOF'
import BedcMathlibBridge.CI.ExportAudit

run_cmd do
  BedcMathlibBridge.CI.ExportAudit.audit #[]
EOF

expect_fail BEDC_GATE_D_ORPHAN_WITNESS \
  bash -c "cd '$LEAN_DIR' && lake env lean '$TMP_DIR/GateDOrphan.lean'"

cat > "$TMP_DIR/correspondence_missing_field.md" <<'EOF'
| row_id | BEDC source | mathlib target | bridge status | constructive content | axioms | boundary |
| --- | --- | --- | --- | --- | --- | --- |
| missing-correspondence | fixture | mathlib Int | adequacy(0-axiom) | fixture | axioms=[] | fixture <!-- bedc-bridge-row: {"row_id":"missing-correspondence","kind":"exported_core","mathlib_class":"Dvd","mathlib_instance":"Int.instDvd","mathlib_decl":"Int.instDvd","bedc_irreducible_decl":"BedcMathlibBridge.Export.Int.cintIntExport","export_witness":"BedcMathlibBridge.Export.Int.cintIntExport"} --> |
EOF

expect_fail BEDC_GATE_W_NO_MATHLIB_CORRESPONDENCE \
  python3 "$ROOT/scripts/check_mathlib_correspondence.py" "$TMP_DIR/correspondence_missing_field.md"

cat > "$TMP_DIR/correspondence_missing_decl.md" <<'EOF'
| row_id | BEDC source | mathlib target | bridge status | constructive content | axioms | boundary |
| --- | --- | --- | --- | --- | --- | --- |
| absent-correspondence | fixture | mathlib Int | adequacy(0-axiom) | fixture | axioms=[] | fixture <!-- bedc-bridge-row: {"row_id":"absent-correspondence","kind":"exported_core","mathlib_class":"Dvd","mathlib_instance":"Int.instDvd","mathlib_decl":"Int.instDvd","bedc_irreducible_decl":"BedcMathlibBridge.Export.Int.cintIntExport","export_witness":"BedcMathlibBridge.Export.Int.cintIntExport","mathlib_correspondence_decl":"BedcMathlibBridge.Negative.absentCorrespondence"} --> |
EOF

expect_fail BEDC_GATE_W_NO_MATHLIB_CORRESPONDENCE \
  python3 "$ROOT/scripts/check_mathlib_correspondence.py" "$TMP_DIR/correspondence_missing_decl.md"

cat > "$TMP_DIR/GateWTrivial.lean" <<'EOF'
import BedcMathlibBridge.CI.MathlibCorrespondence

theorem BedcMathlibBridge.Negative.trivialCorrespondence : True :=
  True.intro
EOF

cat > "$TMP_DIR/correspondence_trivial.md" <<'EOF'
| row_id | BEDC source | mathlib target | bridge status | constructive content | axioms | boundary |
| --- | --- | --- | --- | --- | --- | --- |
| trivial-correspondence | fixture | mathlib Int | adequacy(0-axiom) | fixture | axioms=[] | fixture <!-- bedc-bridge-row: {"row_id":"trivial-correspondence","kind":"exported_core","mathlib_class":"Dvd","mathlib_instance":"Int.instDvd","mathlib_decl":"Int.instDvd","bedc_irreducible_decl":"BedcMathlibBridge.Export.Int.cintIntExport","export_witness":"BedcMathlibBridge.Export.Int.cintIntExport","mathlib_correspondence_decl":"BedcMathlibBridge.Negative.trivialCorrespondence"} --> |
EOF

expect_fail BEDC_GATE_W_NO_MATHLIB_CORRESPONDENCE \
  python3 "$ROOT/scripts/check_mathlib_correspondence.py" "$TMP_DIR/correspondence_trivial.md" \
    "$TMP_DIR/GateWTrivial.lean"

cat > "$TMP_DIR/GateWMathlibOnly.lean" <<'EOF'
import BedcMathlibBridge.CI.MathlibCorrespondence

theorem BedcMathlibBridge.Negative.mathlibOnlyCorrespondence (x y : Int) :
    @Dvd.dvd Int Int.instDvd x y ↔ @Dvd.dvd Int Int.instDvd x y :=
  Iff.rfl
EOF

cat > "$TMP_DIR/correspondence_mathlib_only.md" <<'EOF'
| row_id | BEDC source | mathlib target | bridge status | constructive content | axioms | boundary |
| --- | --- | --- | --- | --- | --- | --- |
| mathlib-only-correspondence | fixture | mathlib Int | adequacy(0-axiom) | fixture | axioms=[] | fixture <!-- bedc-bridge-row: {"row_id":"mathlib-only-correspondence","kind":"exported_core","mathlib_class":"Dvd","mathlib_instance":"Int.instDvd","mathlib_decl":"Int.instDvd","bedc_irreducible_decl":"BedcMathlibBridge.Constructive.Int.CInt","export_witness":"BedcMathlibBridge.Export.Int.cintIntExport","mathlib_correspondence_decl":"BedcMathlibBridge.Negative.mathlibOnlyCorrespondence"} --> |
EOF

expect_fail BEDC_GATE_W_NO_MATHLIB_CORRESPONDENCE \
  python3 "$ROOT/scripts/check_mathlib_correspondence.py" "$TMP_DIR/correspondence_mathlib_only.md" \
    "$TMP_DIR/GateWMathlibOnly.lean"

cp "$ROOT/tests/negative/gate_h_statement_only.lean" "$TMP_DIR/gate_h_statement_only.lean"
cp "$ROOT/tests/negative/gate_h_certificate_hypothesis.lean" \
  "$TMP_DIR/gate_h_certificate_hypothesis.lean"
cp "$ROOT/tests/negative/gate_h_projection_exists.lean" \
  "$TMP_DIR/gate_h_projection_exists.lean"

expect_fail BEDC_GATE_H_HOLLOW_PATTERN \
  python3 "$ROOT/scripts/check_no_hollow.py" "$ROOT/MATRIX.md" \
    "$TMP_DIR/gate_h_statement_only.lean"

expect_fail BEDC_GATE_H_HOLLOW_PATTERN \
  python3 "$ROOT/scripts/check_no_hollow.py" "$ROOT/MATRIX.md" \
    "$TMP_DIR/gate_h_certificate_hypothesis.lean"

expect_fail BEDC_GATE_H_HOLLOW_PATTERN \
  python3 "$ROOT/scripts/check_no_hollow.py" "$ROOT/MATRIX.md" \
    "$TMP_DIR/gate_h_projection_exists.lean"

cat > "$TMP_DIR/gate_r_local_int_law.lean" <<'EOF'
namespace BEDC.Derived.GateRNegative

theorem IntMul_assoc (a b c : IntegerUp) :
    IntEq (IntMul (IntMul a b) c) (IntMul a (IntMul b c)) :=
  by
    exact canonicalShouldBeImported

end BEDC.Derived.GateRNegative
EOF

expect_fail BEDC_GATE_R_LOCAL_INT_LAW \
  python3 "$ROOT/scripts/check_canonical_int_law.py" "$TMP_DIR/gate_r_local_int_law.lean"

cat > "$TMP_DIR/boundary_fake.md" <<'EOF'
| row_id | BEDC source | mathlib target | bridge status | constructive content | axioms | boundary |
| --- | --- | --- | --- | --- | --- | --- |
| fake-boundary | fixture | mathlib Int CommRing (`Int.instCommRing`) | boundary fact (not bridged) | fixture | mathlib_footprint=[] | fixture <!-- bedc-bridge-row: {"row_id":"fake-boundary","kind":"measured_boundary","mathlib_class":"CommRing","mathlib_instance":"Int.instCommRing","mathlib_decl":"Int.instCommRing","mathlib_footprint":[],"bedc_irreducible_decl":"Int.instCommRing","bedc_irreducible_footprint":["propext"],"choice_status":"unprobed","probe_status":"unprobed","axiom_status":{"propext":"mathlib_intrinsic"}} --> |
EOF

expect_fail BEDC_GATE_E_AXIOM_MISMATCH \
  python3 "$ROOT/scripts/check_boundary_axioms.py" "$TMP_DIR/boundary_fake.md"

cat > "$TMP_DIR/boundary_tag_fake.md" <<'EOF'
| row_id | BEDC source | mathlib target | bridge status | constructive content | axioms | boundary |
| --- | --- | --- | --- | --- | --- | --- |
| fake-tag-boundary | fixture | mathlib Int CommRing (`Int.instCommRing`) | boundary fact (not bridged) | fixture | mathlib_footprint=[propext] | fixture <!-- bedc-bridge-row: {"row_id":"fake-tag-boundary","kind":"measured_boundary","mathlib_class":"CommRing","mathlib_instance":"Int.instCommRing","mathlib_decl":"Int.instCommRing","mathlib_footprint":["propext"],"bedc_irreducible_decl":"Int.instCommRing","bedc_irreducible_footprint":["propext"],"choice_status":"unprobed","probe_status":"unprobed","place":"finite_prime","locatedness":"n_a","quotient_status":"structural_quotient","axiom_status":{"propext":"mathlib_intrinsic"}} --> |
EOF

expect_fail BEDC_GATE_E_SCHEMA \
  python3 "$ROOT/scripts/check_boundary_axioms.py" "$TMP_DIR/boundary_tag_fake.md"

cat > "$TMP_DIR/boundary_choice_fake.md" <<'EOF'
| row_id | BEDC source | mathlib target | bridge status | constructive content | axioms | boundary |
| --- | --- | --- | --- | --- | --- | --- |
| fake-choice-boundary | fixture | mathlib Int EuclideanDomain (`Int.euclideanDomain`) | boundary fact (not bridged) | fixture | bedc_irreducible_footprint=[Classical.choice] | fixture <!-- bedc-bridge-row: {"row_id":"fake-choice-boundary","kind":"measured_boundary","mathlib_class":"EuclideanDomain","mathlib_instance":"Int.euclideanDomain","boundary_decl":"Int.euclideanDomain","mathlib_footprint":["Classical.choice","Quot.sound","propext"],"bedc_irreducible_decl":"Int.euclideanDomain","bedc_irreducible_footprint":["Classical.choice","Quot.sound","propext"],"choice_status":"eliminated","probe_status":"probed","axiom_status":{"Classical.choice":"principled_irreducible","Quot.sound":"mathlib_intrinsic","propext":"mathlib_intrinsic"}} --> |
EOF

expect_fail BEDC_GATE_E_REDUCIBLE_CHOICE \
  python3 "$ROOT/scripts/check_boundary_axioms.py" "$TMP_DIR/boundary_choice_fake.md"

cat > "$TMP_DIR/boundary_axiom_missing_fake.md" <<'EOF'
| row_id | BEDC source | mathlib target | bridge status | constructive content | axioms | boundary |
| --- | --- | --- | --- | --- | --- | --- |
| fake-axiom-missing-boundary | fixture | mathlib Int CommRing (`Int.instCommRing`) | boundary fact (not bridged) | fixture | bedc_irreducible_footprint=[propext] | fixture <!-- bedc-bridge-row: {"row_id":"fake-axiom-missing-boundary","kind":"measured_boundary","mathlib_class":"CommRing","mathlib_instance":"Int.instCommRing","mathlib_decl":"Int.instCommRing","mathlib_footprint":["propext"],"bedc_irreducible_decl":"Int.instCommRing","bedc_irreducible_footprint":["propext"],"choice_status":"unprobed","probe_status":"unprobed"} --> |
EOF

expect_fail BEDC_GATE_E_AXIOM_UNCLASSIFIED \
  python3 "$ROOT/scripts/check_boundary_axioms.py" "$TMP_DIR/boundary_axiom_missing_fake.md"

cat > "$TMP_DIR/boundary_axiom_unclassified_fake.md" <<'EOF'
| row_id | BEDC source | mathlib target | bridge status | constructive content | axioms | boundary |
| --- | --- | --- | --- | --- | --- | --- |
| fake-axiom-unclassified-boundary | fixture | mathlib Int CommRing (`Int.instCommRing`) | boundary fact (not bridged) | fixture | bedc_irreducible_footprint=[propext] | fixture <!-- bedc-bridge-row: {"row_id":"fake-axiom-unclassified-boundary","kind":"measured_boundary","mathlib_class":"CommRing","mathlib_instance":"Int.instCommRing","mathlib_decl":"Int.instCommRing","mathlib_footprint":["propext"],"bedc_irreducible_decl":"Int.instCommRing","bedc_irreducible_footprint":["propext"],"choice_status":"unprobed","probe_status":"unprobed","axiom_status":{"propext":"unprobed"}} --> |
EOF

expect_fail BEDC_GATE_E_AXIOM_UNCLASSIFIED \
  python3 "$ROOT/scripts/check_boundary_axioms.py" "$TMP_DIR/boundary_axiom_unclassified_fake.md"

cat > "$TMP_DIR/boundary_reducible_axiom_fake.md" <<'EOF'
| row_id | BEDC source | mathlib target | bridge status | constructive content | axioms | boundary |
| --- | --- | --- | --- | --- | --- | --- |
| fake-reducible-axiom-boundary | fixture | mathlib Int CommRing (`Int.instCommRing`) | boundary fact (not bridged) | fixture | bedc_irreducible_footprint=[propext] | fixture <!-- bedc-bridge-row: {"row_id":"fake-reducible-axiom-boundary","kind":"measured_boundary","mathlib_class":"CommRing","mathlib_instance":"Int.instCommRing","mathlib_decl":"Int.instCommRing","mathlib_footprint":["propext"],"bedc_irreducible_decl":"Int.instCommRing","bedc_irreducible_footprint":["propext"],"choice_status":"unprobed","probe_status":"unprobed","axiom_status":{"propext":"eliminated"}} --> |
EOF

expect_fail BEDC_GATE_E_REDUCIBLE_AXIOM \
  python3 "$ROOT/scripts/check_boundary_axioms.py" "$TMP_DIR/boundary_reducible_axiom_fake.md"

cat > "$TMP_DIR/boundary_real_fake.md" <<'EOF'
| row_id | BEDC source | mathlib target | bridge status | constructive content | axioms | boundary |
| --- | --- | --- | --- | --- | --- | --- |
| fake-real-boundary | fixture | synthesized mathlib SupSet Real | boundary fact (not bridged) | fixture | mathlib_footprint=[] | fixture <!-- bedc-bridge-row: {"row_id":"fake-real-boundary","kind":"measured_boundary","mathlib_class":"SupSet","mathlib_instance":"ConditionallyCompleteLattice.toSupSet","mathlib_decl":"BedcMathlibBridge.Audit.BoundaryFactAxiomGuard.auditRealSupSet","mathlib_footprint":[],"bedc_irreducible_decl":"BedcMathlibBridge.Audit.BoundaryFactAxiomGuard.auditRealSupSet","bedc_irreducible_footprint":[],"choice_status":"principled_irreducible","probe_status":"unprobed","place":"infinite_archimedean","locatedness":"arbitrary","quotient_status":"structural_quotient","axiom_status":{}} --> |
EOF

expect_fail BEDC_GATE_E_AXIOM_MISMATCH \
  python3 "$ROOT/scripts/check_boundary_axioms.py" "$TMP_DIR/boundary_real_fake.md"

echo "[negative] all expected failures matched gate tokens"
