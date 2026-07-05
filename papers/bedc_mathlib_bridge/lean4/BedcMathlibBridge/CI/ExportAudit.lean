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
  { witness := `BedcMathlibBridge.Export.IntSignMagnitude.intSignMagnitudeExport,
    witnessType :=
      `BedcMathlibBridge.Export.IntSignMagnitude.IntSignMagnitudeExportWitness },
  { witness := `BedcMathlibBridge.Export.Bool.boolExport,
    witnessType := `BedcMathlibBridge.Export.Bool.BoolExportWitness },
  { witness := `BedcMathlibBridge.Export.Bool.boolAndOrderExport,
    witnessType := `BedcMathlibBridge.Export.Bool.BoolAndOrderExportWitness },
  { witness := `BedcMathlibBridge.Export.Gaussian.gaussExport,
    witnessType := `BedcMathlibBridge.Export.Gaussian.GaussianExportWitness },
  { witness := `BedcMathlibBridge.Export.Pythagorean.pythagoreanExport,
    witnessType :=
      `BedcMathlibBridge.Export.Pythagorean.PythagoreanExportWitness },
  { witness := `BedcMathlibBridge.Export.Eisenstein.eisExport,
    witnessType := `BedcMathlibBridge.Export.Eisenstein.EisensteinExportWitness },
  { witness := `BedcMathlibBridge.Export.ZMod.zmodExport,
    witnessType := `BedcMathlibBridge.Export.ZMod.ZModExportWitness },
  { witness := `BedcMathlibBridge.Export.Fibonacci.fibonacciExport,
    witnessType := `BedcMathlibBridge.Export.Fibonacci.FibonacciExportWitness },
  { witness := `BedcMathlibBridge.Export.Lucas.lucasExport,
    witnessType := `BedcMathlibBridge.Export.Lucas.LucasExportWitness },
  { witness := `BedcMathlibBridge.Export.FibonacciLucasIdentity.fibonacciLucasIdentityExport,
    witnessType :=
      `BedcMathlibBridge.Export.FibonacciLucasIdentity.FibonacciLucasIdentityExportWitness },
  { witness := `BedcMathlibBridge.Export.Leonardo.leonardoExport,
    witnessType := `BedcMathlibBridge.Export.Leonardo.LeonardoExportWitness },
  { witness := `BedcMathlibBridge.Export.SylvesterSequence.sylvesterSequenceExport,
    witnessType :=
      `BedcMathlibBridge.Export.SylvesterSequence.SylvesterSequenceExportWitness },
  { witness := `BedcMathlibBridge.Export.Binomial.binomialExport,
    witnessType := `BedcMathlibBridge.Export.Binomial.BinomialExportWitness },
  { witness := `BedcMathlibBridge.Export.BellTriangle.bellTriangleExport,
    witnessType :=
      `BedcMathlibBridge.Export.BellTriangle.BellTriangleExportWitness },
  { witness := `BedcMathlibBridge.Export.Factorial.factorialExport,
    witnessType := `BedcMathlibBridge.Export.Factorial.FactorialExportWitness },
  { witness := `BedcMathlibBridge.Export.Eulerian.eulerianRowSumExport,
    witnessType :=
      `BedcMathlibBridge.Export.Eulerian.EulerianRowSumExportWitness },
  { witness := `BedcMathlibBridge.Export.Eulerian.eulerianTriangleExport,
    witnessType :=
      `BedcMathlibBridge.Export.Eulerian.EulerianTriangleExportWitness },
  { witness := `BedcMathlibBridge.Export.Catalan.catalanExport,
    witnessType := `BedcMathlibBridge.Export.Catalan.CatalanExportWitness },
  { witness := `BedcMathlibBridge.Export.StirlingFirst.stirlingFirstExport,
    witnessType :=
      `BedcMathlibBridge.Export.StirlingFirst.StirlingFirstExportWitness },
  { witness := `BedcMathlibBridge.Export.StirlingSecond.stirlingSecondExport,
    witnessType :=
      `BedcMathlibBridge.Export.StirlingSecond.StirlingSecondExportWitness },
  { witness :=
      `BedcMathlibBridge.Export.StirlingCycleColumn.stirlingCycleColumnExport,
    witnessType :=
      `BedcMathlibBridge.Export.StirlingCycleColumn.StirlingCycleColumnExportWitness },
  { witness := `BedcMathlibBridge.Export.Derangement.derangementExport,
    witnessType :=
      `BedcMathlibBridge.Export.Derangement.DerangementExportWitness },
  { witness := `BedcMathlibBridge.Export.SubfactorialNumber.subfactorialNumberExport,
    witnessType :=
      `BedcMathlibBridge.Export.SubfactorialNumber.SubfactorialNumberExportWitness },
  { witness := `BedcMathlibBridge.Export.Rencontres.rencontresNumberExport,
    witnessType :=
      `BedcMathlibBridge.Export.Rencontres.RencontresNumberExportWitness },
  { witness := `BedcMathlibBridge.Export.DescFactorial.descFactorialExport,
    witnessType :=
      `BedcMathlibBridge.Export.DescFactorial.DescFactorialExportWitness },
  { witness := `BedcMathlibBridge.Export.Superfactorial.superfactorialExport,
    witnessType :=
      `BedcMathlibBridge.Export.Superfactorial.SuperfactorialExportWitness },
  { witness := `BedcMathlibBridge.Export.Hyperfactorial.hyperfactorialExport,
    witnessType :=
      `BedcMathlibBridge.Export.Hyperfactorial.HyperfactorialExportWitness },
  { witness := `BedcMathlibBridge.Export.EuclidFactorial.euclidFactorialExport,
    witnessType :=
      `BedcMathlibBridge.Export.EuclidFactorial.EuclidFactorialExportWitness },
  { witness := `BedcMathlibBridge.Export.PowTwo.powTwoExport,
    witnessType :=
      `BedcMathlibBridge.Export.PowTwo.PowTwoExportWitness },
  { witness := `BedcMathlibBridge.Export.NatPowSucc.natPowSuccExport,
    witnessType :=
      `BedcMathlibBridge.Export.NatPowSucc.NatPowSuccExportWitness },
  { witness := `BedcMathlibBridge.Export.NatAddAssoc.natAddAssocExport,
    witnessType :=
      `BedcMathlibBridge.Export.NatAddAssoc.NatAddAssocExportWitness },
  { witness := `BedcMathlibBridge.Export.NatAddComm.natAddCommExport,
    witnessType :=
      `BedcMathlibBridge.Export.NatAddComm.NatAddCommExportWitness },
  { witness := `BedcMathlibBridge.Export.NatSuccPred.natSuccPredExport,
    witnessType :=
      `BedcMathlibBridge.Export.NatSuccPred.NatSuccPredExportWitness },
  { witness := `BedcMathlibBridge.Export.NatSuccInjective.natSuccInjectiveExport,
    witnessType :=
      `BedcMathlibBridge.Export.NatSuccInjective.NatSuccInjectiveExportWitness },
  { witness := `BedcMathlibBridge.Export.ListMapEqMap.listMapEqMapExport,
    witnessType :=
      `BedcMathlibBridge.Export.ListMapEqMap.ListMapEqMapExportWitness },
  { witness := `BedcMathlibBridge.Export.NatMulComm.natMulCommExport,
    witnessType :=
      `BedcMathlibBridge.Export.NatMulComm.NatMulCommExportWitness },
  { witness := `BedcMathlibBridge.Export.NatChooseSuccSucc.natChooseSuccSuccExport,
    witnessType :=
      `BedcMathlibBridge.Export.NatChooseSuccSucc.NatChooseSuccSuccExportWitness },
  { witness := `BedcMathlibBridge.Export.NatChooseZeroRight.natChooseZeroRightExport,
    witnessType :=
      `BedcMathlibBridge.Export.NatChooseZeroRight.NatChooseZeroRightExportWitness },
  { witness :=
      `BedcMathlibBridge.Export.NatChooseSuccSuccPrime.natChooseSuccSuccPrimeExport,
    witnessType :=
      `BedcMathlibBridge.Export.NatChooseSuccSuccPrime.NatChooseSuccSuccPrimeExportWitness },
  { witness :=
      `BedcMathlibBridge.Export.ListBindEqFlatMap.listBindEqFlatMapExport,
    witnessType :=
      `BedcMathlibBridge.Export.ListBindEqFlatMap.ListBindEqFlatMapExportWitness },
  { witness := `BedcMathlibBridge.Export.Jacobsthal.jacobsthalExport,
    witnessType :=
      `BedcMathlibBridge.Export.Jacobsthal.JacobsthalExportWitness },
  { witness := `BedcMathlibBridge.Export.Motzkin.motzkinExport,
    witnessType :=
      `BedcMathlibBridge.Export.Motzkin.MotzkinExportWitness },
  { witness := `BedcMathlibBridge.Export.MotzkinPath.motzkinPathExport,
    witnessType :=
      `BedcMathlibBridge.Export.MotzkinPath.MotzkinPathExportWitness },
  { witness := `BedcMathlibBridge.Export.MotzkinTriangle.motzkinTriangleExport,
    witnessType :=
      `BedcMathlibBridge.Export.MotzkinTriangle.MotzkinTriangleExportWitness },
  { witness := `BedcMathlibBridge.Export.Padovan.padovanExport,
    witnessType :=
      `BedcMathlibBridge.Export.Padovan.PadovanExportWitness },
  { witness := `BedcMathlibBridge.Export.Perrin.perrinExport,
    witnessType :=
      `BedcMathlibBridge.Export.Perrin.PerrinExportWitness },
  { witness := `BedcMathlibBridge.Export.Tribonacci.tribonacciExport,
    witnessType :=
      `BedcMathlibBridge.Export.Tribonacci.TribonacciExportWitness },
  { witness := `BedcMathlibBridge.Export.Tetranacci.tetranacciExport,
    witnessType :=
      `BedcMathlibBridge.Export.Tetranacci.TetranacciExportWitness },
  { witness := `BedcMathlibBridge.Export.CullenWoodall.cullenExport,
    witnessType :=
      `BedcMathlibBridge.Export.CullenWoodall.CullenExportWitness },
  { witness := `BedcMathlibBridge.Export.CullenWoodall.woodallExport,
    witnessType :=
      `BedcMathlibBridge.Export.CullenWoodall.WoodallExportWitness },
  { witness := `BedcMathlibBridge.Export.HarshadNumber.harshadNumberExport,
    witnessType :=
      `BedcMathlibBridge.Export.HarshadNumber.HarshadNumberExportWitness },
  { witness := `BedcMathlibBridge.Export.KeithNumber.keithNumberExport,
    witnessType :=
      `BedcMathlibBridge.Export.KeithNumber.KeithNumberExportWitness },
  { witness := `BedcMathlibBridge.Export.CentralTrinomial.centralTrinomialExport,
    witnessType :=
      `BedcMathlibBridge.Export.CentralTrinomial.CentralTrinomialExportWitness },
  { witness := `BedcMathlibBridge.Export.AscFactorial.ascFactorialExport,
    witnessType :=
      `BedcMathlibBridge.Export.AscFactorial.AscFactorialExportWitness },
  { witness := `BedcMathlibBridge.Export.CentralBinom.centralBinomExport,
    witnessType :=
      `BedcMathlibBridge.Export.CentralBinom.CentralBinomExportWitness },
  { witness := `BedcMathlibBridge.Export.Delannoy.delannoyClosedFormTermExport,
    witnessType :=
      `BedcMathlibBridge.Export.Delannoy.DelannoyClosedFormTermExportWitness },
  { witness := `BedcMathlibBridge.Export.Pell.pellRecurrenceExport,
    witnessType :=
      `BedcMathlibBridge.Export.Pell.PellRecurrenceExportWitness },
  { witness := `BedcMathlibBridge.Export.PellLucas.pellLucasExport,
    witnessType :=
      `BedcMathlibBridge.Export.PellLucas.PellLucasExportWitness },
  { witness := `BedcMathlibBridge.Export.SchroederNumber.schroederNumberExport,
    witnessType :=
      `BedcMathlibBridge.Export.SchroederNumber.SchroederNumberExportWitness },
  { witness := `BedcMathlibBridge.Export.SternDiatomic.sternDiatomicExport,
    witnessType :=
      `BedcMathlibBridge.Export.SternDiatomic.SternDiatomicExportWitness },
  { witness := `BedcMathlibBridge.Export.QBinomial.qBinomialExport,
    witnessType :=
      `BedcMathlibBridge.Export.QBinomial.QBinomialExportWitness },
  { witness := `BedcMathlibBridge.Export.Narayana.narayanaExport,
    witnessType :=
      `BedcMathlibBridge.Export.Narayana.NarayanaExportWitness },
  { witness := `BedcMathlibBridge.Export.QFactorial.qFactorialExport,
    witnessType :=
      `BedcMathlibBridge.Export.QFactorial.QFactorialExportWitness },
  { witness := `BedcMathlibBridge.Export.Raney.raneyExport,
    witnessType := `BedcMathlibBridge.Export.Raney.RaneyExportWitness },
  { witness := `BedcMathlibBridge.Export.FussCatalan.fussCatalanExport,
    witnessType :=
      `BedcMathlibBridge.Export.FussCatalan.FussCatalanExportWitness },
  { witness := `BedcMathlibBridge.Export.TernaryTree.ternaryTreeExport,
    witnessType :=
      `BedcMathlibBridge.Export.TernaryTree.TernaryTreeExportWitness },
  { witness := `BedcMathlibBridge.Export.SuperCatalan.superCatalanExport,
    witnessType :=
      `BedcMathlibBridge.Export.SuperCatalan.SuperCatalanExportWitness },
  { witness := `BedcMathlibBridge.Export.Lobb.lobbExport,
    witnessType := `BedcMathlibBridge.Export.Lobb.LobbExportWitness },
  { witness := `BedcMathlibBridge.Export.BallotNumber.ballotNumberExport,
    witnessType :=
      `BedcMathlibBridge.Export.BallotNumber.BallotNumberExportWitness },
  { witness := `BedcMathlibBridge.Export.Lah.lahFirstColumnExport,
    witnessType := `BedcMathlibBridge.Export.Lah.LahFirstColumnExportWitness },
  { witness := `BedcMathlibBridge.Export.LahClosedForm.lahClosedFormExport,
    witnessType :=
      `BedcMathlibBridge.Export.LahClosedForm.LahClosedFormExportWitness },
  { witness := `BedcMathlibBridge.Export.BesselNumber.besselNumberExport,
    witnessType :=
      `BedcMathlibBridge.Export.BesselNumber.BesselNumberExportWitness },
  { witness := `BedcMathlibBridge.Export.LahRecurrence.lahRecurrenceExport,
    witnessType :=
      `BedcMathlibBridge.Export.LahRecurrence.LahRecurrenceExportWitness },
  { witness := `BedcMathlibBridge.Export.Tetrahedral.tetrahedralExport,
    witnessType :=
      `BedcMathlibBridge.Export.Tetrahedral.TetrahedralExportWitness },
  { witness := `BedcMathlibBridge.Export.Triangular.triangularExport,
    witnessType :=
      `BedcMathlibBridge.Export.Triangular.TriangularExportWitness },
  { witness := `BedcMathlibBridge.Export.CakeNumber.cakeNumberExport,
    witnessType :=
      `BedcMathlibBridge.Export.CakeNumber.CakeNumberExportWitness },
  { witness :=
      `BedcMathlibBridge.Export.OddDoubleFactorial.oddDoubleFactorialExport,
    witnessType :=
      `BedcMathlibBridge.Export.OddDoubleFactorial.OddDoubleFactorialExportWitness },
  { witness :=
      `BedcMathlibBridge.Export.EulerianSecondOrder.eulerianSecondOrderExport,
    witnessType :=
      `BedcMathlibBridge.Export.EulerianSecondOrder.EulerianSecondOrderExportWitness },
  { witness :=
      `BedcMathlibBridge.Export.EvenDoubleFactorial.evenDoubleFactorialExport,
    witnessType :=
      `BedcMathlibBridge.Export.EvenDoubleFactorial.EvenDoubleFactorialExportWitness },
  { witness := `BedcMathlibBridge.Export.Square.squareExport,
    witnessType :=
      `BedcMathlibBridge.Export.Square.SquareExportWitness },
  { witness := `BedcMathlibBridge.Export.Pronic.pronicExport,
    witnessType :=
      `BedcMathlibBridge.Export.Pronic.PronicExportWitness },
  { witness := `BedcMathlibBridge.Export.CenteredHexagonal.centeredHexagonalExport,
    witnessType :=
      `BedcMathlibBridge.Export.CenteredHexagonal.CenteredHexagonalExportWitness },
  { witness := `BedcMathlibBridge.Export.SquarePyramidal.squarePyramidalExport,
    witnessType :=
      `BedcMathlibBridge.Export.SquarePyramidal.SquarePyramidalExportWitness },
  { witness := `BedcMathlibBridge.Export.Pentagonal.pentagonalExport,
    witnessType :=
      `BedcMathlibBridge.Export.Pentagonal.PentagonalExportWitness },
  { witness := `BedcMathlibBridge.Export.Hexagonal.hexagonalExport,
    witnessType :=
      `BedcMathlibBridge.Export.Hexagonal.HexagonalExportWitness },
  { witness := `BedcMathlibBridge.Export.CentralFactorial.centralFactorialExport,
    witnessType :=
      `BedcMathlibBridge.Export.CentralFactorial.CentralFactorialExportWitness },
  { witness := `BedcMathlibBridge.Export.WilsonQuotient.wilsonQuotientExport,
    witnessType :=
      `BedcMathlibBridge.Export.WilsonQuotient.WilsonQuotientExportWitness },
  { witness := `BedcMathlibBridge.Export.Apery.aperyExport,
    witnessType :=
      `BedcMathlibBridge.Export.Apery.AperyExportWitness },
  { witness := `BedcMathlibBridge.Export.EntringerNumber.entringerNumberExport,
    witnessType :=
      `BedcMathlibBridge.Export.EntringerNumber.EntringerNumberExportWitness },
  { witness := `BedcMathlibBridge.Export.TangentNumber.tangentNumberExport,
    witnessType :=
      `BedcMathlibBridge.Export.TangentNumber.TangentNumberExportWitness },
  { witness := `BedcMathlibBridge.Export.SecantNumber.secantNumberExport,
    witnessType :=
      `BedcMathlibBridge.Export.SecantNumber.SecantNumberExportWitness },
  { witness := `BedcMathlibBridge.Export.GenocchiNumber.genocchiNumberExport,
    witnessType :=
      `BedcMathlibBridge.Export.GenocchiNumber.GenocchiNumberExportWitness },
  { witness := `BedcMathlibBridge.Export.AssociatedStirling.associatedStirlingExport,
    witnessType :=
      `BedcMathlibBridge.Export.AssociatedStirling.AssociatedStirlingExportWitness },
  { witness := `BedcMathlibBridge.Export.Riordan.riordanExport,
    witnessType := `BedcMathlibBridge.Export.Riordan.RiordanExportWitness },
  { witness := `BedcMathlibBridge.Export.NarayanaCow.narayanaCowExport,
    witnessType :=
      `BedcMathlibBridge.Export.NarayanaCow.NarayanaCowExportWitness },
  { witness :=
      `BedcMathlibBridge.Export.ProjectionLedgerCount.projectionLedgerCountExport,
    witnessType :=
      `BedcMathlibBridge.Export.ProjectionLedgerCount.ProjectionLedgerCountExportWitness },
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
