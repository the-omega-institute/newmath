import BEDC.Derived.LocatedSupremumUp.Core
import BEDC.Derived.PadicUp.Valuation
import BedcMathlibBridge.All
import BedcMathlibBridge.CI.IntMetadata
import Lean
import Lean.Meta.Basic
import Lean.Util.CollectAxioms

namespace BedcMathlibBridge.CI.ExportAudit

open Lean
open Lean.Elab.Command
open Lean.Meta

structure ExportExpectation where
  rowId : String
  witness : Name

abbrev ClassificationExpectation :=
  IntMetadata.ClassificationExpectation

structure ExportRegistration where
  witness : Name
  witnessType : Name

def exportWitnessRegistry : Array ExportRegistration := #[
  { witness := `BedcMathlibBridge.Export.Int.cintIntExport,
    witnessType := `BedcMathlibBridge.Export.Int.IntExportWitness },
  { witness := `BedcMathlibBridge.Export.Bool.boolExport,
    witnessType := `BedcMathlibBridge.Export.Bool.BoolExportWitness },
  { witness := `BedcMathlibBridge.Export.Gaussian.gaussExport,
    witnessType := `BedcMathlibBridge.Export.Gaussian.GaussianExportWitness },
  { witness := `BedcMathlibBridge.Export.Eisenstein.eisExport,
    witnessType := `BedcMathlibBridge.Export.Eisenstein.EisensteinExportWitness },
  { witness := `BedcMathlibBridge.Export.ZMod.zmodExport,
    witnessType := `BedcMathlibBridge.Export.ZMod.ZModExportWitness },
  { witness := `BedcMathlibBridge.Export.Fibonacci.fibonacciExport,
    witnessType := `BedcMathlibBridge.Export.Fibonacci.FibonacciExportWitness },
  { witness := `BedcMathlibBridge.Export.Binomial.binomialExport,
    witnessType := `BedcMathlibBridge.Export.Binomial.BinomialExportWitness },
  { witness := `BedcMathlibBridge.Export.Factorial.factorialExport,
    witnessType := `BedcMathlibBridge.Export.Factorial.FactorialExportWitness },
  { witness := `BedcMathlibBridge.Export.Catalan.catalanExport,
    witnessType := `BedcMathlibBridge.Export.Catalan.CatalanExportWitness },
  { witness := `BedcMathlibBridge.Export.StirlingFirst.stirlingFirstExport,
    witnessType :=
      `BedcMathlibBridge.Export.StirlingFirst.StirlingFirstExportWitness },
  { witness := `BEDC.Derived.LocatedSupremumUp.locatedSupremumExport,
    witnessType :=
      `BEDC.Derived.LocatedSupremumUp.LocatedSupremumExportWitness },
  { witness := `BEDC.Derived.PadicUp.QpInt_valued_field,
    witnessType := `BEDC.Derived.PadicUp.QpValuedFieldSummary }
]

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

def typeHead? (ci : ConstantInfo) : CommandElabM (Option Name) :=
  liftTermElabM <| forallTelescopeReducing ci.type fun _ result => do
    let result ← whnf result
    match result.getAppFn with
    | .const n _ => pure (some n)
    | _ => pure none

def auditRegistration (reg : ExportRegistration) : CommandElabM Unit := do
  let env ← getEnv
  let some ci := env.find? reg.witness
    | throwError m!"BEDC_GATE_D_MISSING_WITNESS: `{reg.witness}` is registered but absent"
  let head? ← typeHead? ci
  unless head? == some reg.witnessType do
    throwError m!
      "BEDC_GATE_D_WRONG_WITNESS_TYPE: `{reg.witness}` has type head {head?}, \
      expected `{reg.witnessType}`"
  let axioms ← collectAxioms reg.witness
  unless axioms.isEmpty do
    throwError m!
      "BEDC_GATE_D_AXIOM: export witness `{reg.witness}` depends on axiom(s): \
      {formatNames (axioms.qsort Name.quickLt)}"

def auditExpectedWitness (e : ExportExpectation) : CommandElabM Unit := do
  let env ← getEnv
  unless env.contains e.witness do
    throwError m!"BEDC_GATE_D_MISSING_WITNESS: row `{e.rowId}` names absent witness `{e.witness}`"
  let axioms ← collectAxioms e.witness
  unless axioms.isEmpty do
    throwError m!
      "BEDC_GATE_D_AXIOM: row `{e.rowId}` witness `{e.witness}` depends on axiom(s): \
      {formatNames (axioms.qsort Name.quickLt)}"

def auditRegistrations (registrations : Array ExportRegistration) :
    CommandElabM Unit := do
  let names := registrations.map (·.witness)
  let dupes := duplicateNames names
  unless dupes.isEmpty do
    throwError m!
      "BEDC_GATE_D_DUPLICATE_WITNESS: duplicate registered export witness(es): \
      {formatNames dupes}"
  for reg in registrations do
    auditRegistration reg

def audit (expected : Array ExportExpectation)
    (classification : Array ClassificationExpectation := #[]) : CommandElabM Unit := do
  IntMetadata.auditIntExportSignature
  auditRegistrations exportWitnessRegistry
  let expectedNames := expected.map (·.witness)
  let dupes := duplicateNames expectedNames
  unless dupes.isEmpty do
    throwError m!
      "BEDC_GATE_D_DUPLICATE_WITNESS: duplicate MATRIX export witness(es): \
      {formatNames dupes}"
  for e in expected do
    auditExpectedWitness e
  for e in expected do
    unless containsName (exportWitnessRegistry.map (·.witness)) e.witness do
      throwError m!
        "BEDC_GATE_D_UNREGISTERED_WITNESS: row `{e.rowId}` names `{e.witness}`, \
        but the witness is not registered"
  for reg in exportWitnessRegistry do
    unless containsName expectedNames reg.witness do
      throwError m!
        "BEDC_GATE_D_ORPHAN_WITNESS: registered witness `{reg.witness}` has no MATRIX row"
  unless classification.isEmpty do
    IntMetadata.auditClassification classification
  logInfo m!"[export-audit] audited {expected.size} MATRIX export witness row(s)"

end BedcMathlibBridge.CI.ExportAudit
