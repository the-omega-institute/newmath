import BedcMathlibBridge.Export.Int
import Lean
import Lean.Meta.Basic
import Lean.Meta.Instances
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Order.Basic

namespace BedcMathlibBridge.CI.IntMetadata

open Lean
open Lean.Elab.Command
open Lean.Meta

inductive ClassificationKind where
  | exportedCore
  | subsumedByCore
  | measuredBoundary
  | outOfScopeGeneric
deriving BEq, Repr

structure ClassificationExpectation where
  rowId : String
  kind : ClassificationKind
  className : Name
  instanceName : Name

structure SignatureExpectation where
  field : Name
  typeHash : UInt64

structure IntInstanceMetadata where
  className : Name
  instanceName : Name
  typeHash : UInt64
  parents : Array Name
  maximal : Bool

def formatNames (names : Array Name) : String :=
  String.intercalate ", " (names.toList.map Name.toString)

def containsName (xs : Array Name) (x : Name) : Bool :=
  xs.any fun y => y == x

def duplicateNames (xs : Array Name) : Array Name := Id.run do
  let mut seen : Array Name := #[]
  let mut dupes : Array Name := #[]
  for x in xs do
    if containsName seen x then
      unless containsName dupes x do
        dupes := dupes.push x
    else
      seen := seen.push x
  return dupes

def duplicateInstances (xs : Array ClassificationExpectation) : Array Name :=
  duplicateNames (xs.map (·.instanceName))

def isIntConst (e : Expr) : Bool :=
  match e.consumeMData with
  | .const n _ => n == ``Int
  | _ => false

def unaryIntTarget (result : Expr) : Bool :=
  result.getAppNumArgs == 1 &&
    match result.getAppArgs[0]? with
    | some arg => isIntConst arg
    | none => false

/--
Int metadata enumeration is relative to this module import set. The set contains
`Mathlib.Data.Int.ConditionallyCompleteOrder`, so the conditional-completeness
instance and its synthesized `SupSet`/`InfSet` projections are visible here.
-/
def intInstanceProjectionSpecs : Array (Name × Name) := #[
  (`SupSet, `ConditionallyCompleteLattice.toSupSet),
  (`InfSet, `ConditionallyCompleteLattice.toInfSet)
]

def intClassResult (cls : Name) : Expr :=
  mkApp (mkConst cls [levelZero]) (mkConst ``Int)

def projectedIntInstanceRows (env : Environment) :
    CommandElabM (Array (Name × Name × UInt64)) := do
  let mut rows : Array (Name × Name × UInt64) := #[]
  for spec in intInstanceProjectionSpecs do
    let cls := spec.1
    let inst := spec.2
    if env.contains inst then
      let result := intClassResult cls
      try
        let _ ← liftTermElabM <| synthInstance result
        rows := rows.push (cls, inst, hash result)
      catch _ =>
        pure ()
  return rows

def containsHit (hits : Array (Name × Name × UInt64)) (hit : Name × Name × UInt64) : Bool :=
  hits.any fun existing => existing.1 == hit.1 && existing.2.1 == hit.2.1

def instanceTarget? (ci : ConstantInfo) : MetaM (Option (Name × Expr)) := do
  forallTelescopeReducing ci.type fun _ result => do
    let result ← whnf result
    match result.getAppFn with
    | .const cls _ => pure (some (cls, result))
    | _ => pure none

partial def classAncestors (env : Environment) (cls : Name) : NameSet := Id.run do
  let rec go (c : Name) : StateM NameSet Unit := do
    if (← get).contains c then
      return
    modify fun s => s.insert c
    match getStructureInfo? env c with
    | none => pure ()
    | some info =>
        for parent in info.parentInfo do
          go parent.structName
  let (_, state) := (go cls).run {}
  state.erase cls

def directParentNames (env : Environment) (cls : Name) : Array Name :=
  match getStructureInfo? env cls with
  | none => #[]
  | some info => info.parentInfo.map (·.structName)

def hasDescendantHit (env : Environment) (hits : Array Name) (cls : Name) : Bool :=
  hits.any fun other =>
    other != cls && (classAncestors env other).contains cls

def enumerate : CommandElabM (Array IntInstanceMetadata) := do
  let env ← getEnv
  let mut hits : Array (Name × Name × UInt64) := #[]
  for (n, ci) in env.constants.toList do
    if Meta.isInstanceCore env n then
      try
        match ← liftTermElabM <| instanceTarget? ci with
        | some (cls, result) =>
            if unaryIntTarget result then
              hits := hits.push (cls, n, hash result)
        | none => pure ()
      catch _ =>
        pure ()
  for hit in (← projectedIntInstanceRows env) do
    unless containsHit hits hit do
      hits := hits.push hit
  let classes :=
    hits.foldl
      (fun acc hit => if containsName acc hit.1 then acc else acc.push hit.1)
      #[]
  let out := hits.map fun hit =>
    { className := hit.1
      instanceName := hit.2.1
      typeHash := hit.2.2
      parents := directParentNames env hit.1
      maximal := !hasDescendantHit env classes hit.1 }
  return out.qsort fun a b =>
    Name.quickLt a.className b.className ||
      (a.className == b.className && Name.quickLt a.instanceName b.instanceName)

def maximalRows (rows : Array IntInstanceMetadata) : Array IntInstanceMetadata :=
  rows.filter (·.maximal)

def auditClassification (expected : Array ClassificationExpectation) : CommandElabM Unit := do
  let rows ← enumerate
  let maxRows := maximalRows rows
  let dupes := duplicateInstances expected
  unless dupes.isEmpty do
    throwError m!
      "BEDC_GATE_D_DUPLICATE_CLASSIFICATION: duplicate classified instance(s): \
      {formatNames dupes}"
  for row in maxRows do
    let rowMatches := expected.filter (fun e =>
      e.className == row.className && e.instanceName == row.instanceName)
    if rowMatches.isEmpty then
      throwError m!
        "BEDC_GATE_D_UNCLASSIFIED: maximal Int class `{row.className}` \
        via instance `{row.instanceName}` has no MATRIX classification"
    if rowMatches.size != 1 then
      throwError m!
        "BEDC_GATE_D_DUPLICATE_CLASSIFICATION: maximal Int class `{row.className}` \
        via instance `{row.instanceName}` has {rowMatches.size} MATRIX rows"
  for e in expected do
    unless rows.any (fun r => r.className == e.className && r.instanceName == e.instanceName) do
      throwError m!
        "BEDC_GATE_D_UNKNOWN_CLASSIFICATION: row `{e.rowId}` names non-enumerated \
        Int instance `{e.instanceName}` for class `{e.className}`"
  logInfo m!
    "[int-metadata] enumerated {rows.size} direct Int instance row(s); \
    {maxRows.size} maximal row(s) classified"

def projectionResult? (env : Environment) (proj : Name) : MetaM (Option Expr) := do
  let some ci := env.find? proj | return none
  forallTelescopeReducing ci.type fun _ result => do
    pure (some result)

def intExportSignatureGolden : Array SignatureExpectation := #[
  { field := `order_apply, typeHash := 1975926009 },
  { field := `ring_apply, typeHash := 1889744218 },
  { field := `dvd_iff, typeHash := 1467912209 },
  { field := `dvd_apply, typeHash := 1467912209 },
  { field := `le_iff, typeHash := 3952604688 },
  { field := `add_apply, typeHash := 346867285 },
  { field := `ringEquiv, typeHash := 141253817 },
  { field := `linearOrder, typeHash := 3573691674 },
  { field := `ofInt_toInt, typeHash := 2264819455 },
  { field := `mul_apply, typeHash := 4220398218 },
  { field := `toInt_ofInt, typeHash := 720315670 }
]

def auditIntExportSignature : CommandElabM Unit := do
  let env ← getEnv
  let some info := getStructureInfo? env `BedcMathlibBridge.Export.Int.IntExportWitness
    | throwError
        "BEDC_GATE_S_SIGNATURE: missing IntExportWitness structure metadata"
  let fields := info.fieldInfo.qsort fun a b => Name.quickLt a.fieldName b.fieldName
  unless fields.size == intExportSignatureGolden.size do
    throwError m!
      "BEDC_GATE_S_SIGNATURE: IntExportWitness has {fields.size} field(s), \
      expected {intExportSignatureGolden.size}"
  for idx in [:fields.size] do
    let some field := fields[idx]?
      | throwError m!"BEDC_GATE_S_SIGNATURE: missing actual field at index {idx}"
    let some expected := intExportSignatureGolden[idx]?
      | throwError m!"BEDC_GATE_S_SIGNATURE: missing golden field at index {idx}"
    unless field.fieldName == expected.field do
      throwError m!
        "BEDC_GATE_S_SIGNATURE: field index {idx} is `{field.fieldName}`, \
        expected `{expected.field}`"
    let some ci := env.find? field.projFn
      | throwError m!
          "BEDC_GATE_S_SIGNATURE: missing projection type for `{field.fieldName}`"
    let actualHash := hash ci.type
    unless actualHash == expected.typeHash do
      throwError m!
        "BEDC_GATE_S_SIGNATURE: field `{field.fieldName}` type hash {actualHash}, \
        expected {expected.typeHash}"
  logInfo m!"[int-signature] IntExportWitness signature matches golden manifest"

end BedcMathlibBridge.CI.IntMetadata
