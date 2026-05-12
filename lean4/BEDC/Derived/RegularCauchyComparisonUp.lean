import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyComparisonUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyComparisonCarrier [AskSetup] [PackageSetup]
    (leftName rightName window observations tolerance ledger sealRow sameRows routes provenance
      nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory leftName ∧ UnaryHistory rightName ∧ UnaryHistory window ∧
    UnaryHistory observations ∧ UnaryHistory tolerance ∧ UnaryHistory ledger ∧
      UnaryHistory sealRow ∧ UnaryHistory sameRows ∧ UnaryHistory routes ∧
        UnaryHistory provenance ∧ UnaryHistory nameCert ∧ Cont leftName window sameRows ∧
          Cont rightName window sameRows ∧ Cont sameRows observations routes ∧
            Cont observations tolerance ledger ∧ Cont ledger sealRow provenance ∧
              hsame ledger (append observations tolerance) ∧ PkgSig bundle provenance pkg

theorem RegularCauchyComparisonCarrier_window_exactness [AskSetup] [PackageSetup]
    {leftName rightName window observations tolerance ledger sealRow sameRows routes provenance
      nameCert sharedRead observationRead toleranceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyComparisonCarrier leftName rightName window observations tolerance ledger sealRow
        sameRows routes provenance nameCert bundle pkg ->
      Cont leftName window sharedRead ->
        Cont rightName window sharedRead ->
          Cont sharedRead observations observationRead ->
            Cont observationRead tolerance toleranceRead ->
              UnaryHistory sharedRead ∧ UnaryHistory observationRead ∧
                UnaryHistory toleranceRead ∧ hsame ledger (append observations tolerance) ∧
                  PkgSig bundle provenance pkg := by
  intro carrier leftWindowRead _rightWindowRead observationReadRow toleranceReadRow
  obtain ⟨leftUnary, _rightUnary, windowUnary, observationsUnary, toleranceUnary, _ledgerUnary,
    _sealUnary, _sameRowsUnary, _routesUnary, _provenanceUnary, _nameCertUnary,
    _leftWindowSameRows, _rightWindowSameRows, _sameRowsObservationsRoutes,
    _observationsToleranceLedger, _ledgerSealProvenance, ledgerSame, pkgSig⟩ := carrier
  have sharedReadUnary : UnaryHistory sharedRead :=
    unary_cont_closed leftUnary windowUnary leftWindowRead
  have observationReadUnary : UnaryHistory observationRead :=
    unary_cont_closed sharedReadUnary observationsUnary observationReadRow
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed observationReadUnary toleranceUnary toleranceReadRow
  exact ⟨sharedReadUnary, observationReadUnary, toleranceReadUnary, ledgerSame, pkgSig⟩

end BEDC.Derived.RegularCauchyComparisonUp
