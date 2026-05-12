import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyComparisonUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem RegularCauchyComparisonCarrier_semantic_name_certificate [AskSetup] [PackageSetup]
    {leftName rightName window observations tolerance ledger sealRow sameRows routes provenance
      nameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyComparisonCarrier leftName rightName window observations tolerance ledger sealRow
        sameRows routes provenance nameCert bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          RegularCauchyComparisonCarrier leftName rightName window observations tolerance ledger
              sealRow sameRows routes provenance nameCert bundle pkg ∧ hsame row nameCert)
        (fun row : BHist =>
          RegularCauchyComparisonCarrier leftName rightName window observations tolerance ledger
              sealRow sameRows routes provenance nameCert bundle pkg ∧ hsame row nameCert)
        (fun row : BHist =>
          RegularCauchyComparisonCarrier leftName rightName window observations tolerance ledger
              sealRow sameRows routes provenance nameCert bundle pkg ∧ hsame row nameCert)
        hsame := by
  intro carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro nameCert (And.intro carrier (hsame_refl nameCert))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

theorem RegularCauchyComparisonCarrier_public_rows_zero_head_absurd [AskSetup] [PackageSetup]
    {leftName rightName window observations tolerance ledger sealRow sameRows routes provenance
      nameCert zWindow zLedger zSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyComparisonCarrier leftName rightName window observations tolerance ledger sealRow
        sameRows routes provenance nameCert bundle pkg ->
      (hsame window (BHist.e0 zWindow) -> False) ∧
        (hsame ledger (BHist.e0 zLedger) -> False) ∧
          (hsame sealRow (BHist.e0 zSeal) -> False) := by
  intro carrier
  obtain ⟨_leftUnary, _rightUnary, windowUnary, _observationsUnary, _toleranceUnary,
    ledgerUnary, sealUnary, _sameRowsUnary, _routesUnary, _provenanceUnary,
    _nameCertUnary, _leftWindowSameRows, _rightWindowSameRows, _sameRowsObservationsRoutes,
    _observationsToleranceLedger, _ledgerSealProvenance, _ledgerSame, _pkgSig⟩ := carrier
  constructor
  · intro sameWindowZero
    exact unary_no_zero_extension (unary_transport windowUnary sameWindowZero)
  constructor
  · intro sameLedgerZero
    exact unary_no_zero_extension (unary_transport ledgerUnary sameLedgerZero)
  · intro sameSealZero
    exact unary_no_zero_extension (unary_transport sealUnary sameSealZero)

theorem RegularCauchyComparisonCarrier_real_classifier_handoff [AskSetup] [PackageSetup]
    {leftName rightName window observations tolerance ledger sealRow sameRows routes provenance
      nameCert sharedRead observationRead toleranceRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyComparisonCarrier leftName rightName window observations tolerance ledger sealRow
        sameRows routes provenance nameCert bundle pkg ->
      Cont leftName window sharedRead ->
        Cont rightName window sharedRead ->
          Cont sharedRead observations observationRead ->
            Cont observationRead tolerance toleranceRead ->
              Cont ledger sealRow sealRead ->
                PkgSig bundle sealRead pkg ->
                  UnaryHistory sharedRead ∧ UnaryHistory observationRead ∧
                    UnaryHistory toleranceRead ∧ UnaryHistory sealRead ∧
                      Cont ledger sealRow sealRead ∧
                        hsame ledger (append observations tolerance) ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle sealRead pkg := by
  intro carrier leftWindowRead _rightWindowRead observationReadRow toleranceReadRow
    ledgerSealRead sealReadPkg
  obtain ⟨leftUnary, _rightUnary, windowUnary, observationsUnary, toleranceUnary, ledgerUnary,
    sealUnary, _sameRowsUnary, _routesUnary, _provenanceUnary, _nameCertUnary,
    _leftWindowSameRows, _rightWindowSameRows, _sameRowsObservationsRoutes,
    _observationsToleranceLedger, _ledgerSealProvenance, ledgerSame, provenancePkg⟩ :=
      carrier
  have sharedReadUnary : UnaryHistory sharedRead :=
    unary_cont_closed leftUnary windowUnary leftWindowRead
  have observationReadUnary : UnaryHistory observationRead :=
    unary_cont_closed sharedReadUnary observationsUnary observationReadRow
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed observationReadUnary toleranceUnary toleranceReadRow
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed ledgerUnary sealUnary ledgerSealRead
  exact
    ⟨sharedReadUnary, observationReadUnary, toleranceReadUnary, sealReadUnary,
      ledgerSealRead, ledgerSame, provenancePkg, sealReadPkg⟩

theorem RegularCauchyComparisonCarrier_tolerance_row_stability [AskSetup] [PackageSetup]
    {leftName rightName window observations tolerance ledger sealRow sameRows routes provenance
      nameCert transportedTolerance toleranceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyComparisonCarrier leftName rightName window observations tolerance ledger sealRow
        sameRows routes provenance nameCert bundle pkg ->
      hsame tolerance transportedTolerance ->
        Cont observations transportedTolerance toleranceRead ->
          UnaryHistory transportedTolerance ∧ UnaryHistory toleranceRead ∧
            hsame ledger (append observations tolerance) ∧ PkgSig bundle provenance pkg := by
  intro carrier sameTolerance toleranceReadRow
  obtain ⟨_leftUnary, _rightUnary, _windowUnary, observationsUnary, toleranceUnary,
    _ledgerUnary, _sealUnary, _sameRowsUnary, _routesUnary, _provenanceUnary,
    _nameCertUnary, _leftWindowSameRows, _rightWindowSameRows, _sameRowsObservationsRoutes,
    _observationsToleranceLedger, _ledgerSealProvenance, ledgerSame, provenancePkg⟩ :=
      carrier
  have transportedToleranceUnary : UnaryHistory transportedTolerance :=
    unary_transport toleranceUnary sameTolerance
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed observationsUnary transportedToleranceUnary toleranceReadRow
  exact ⟨transportedToleranceUnary, toleranceReadUnary, ledgerSame, provenancePkg⟩

theorem RegularCauchyComparisonCarrier_seal_handoff_obligation [AskSetup] [PackageSetup]
    {leftName rightName window observations tolerance ledger sealRow sameRows routes provenance
      nameCert sharedRead observationRead toleranceRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyComparisonCarrier leftName rightName window observations tolerance ledger sealRow
        sameRows routes provenance nameCert bundle pkg ->
      Cont leftName window sharedRead ->
        Cont rightName window sharedRead ->
          Cont sharedRead observations observationRead ->
            Cont observationRead tolerance toleranceRead ->
              Cont ledger sealRow sealRead ->
                PkgSig bundle sealRead pkg ->
                  UnaryHistory window ∧ UnaryHistory ledger ∧ UnaryHistory sealRow ∧
                    UnaryHistory sealRead ∧ Cont ledger sealRow sealRead ∧
                      hsame ledger (append observations tolerance) ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle sealRead pkg := by
  intro carrier _leftWindowRead _rightWindowRead _observationReadRow _toleranceReadRow
    ledgerSealRead sealReadPkg
  obtain ⟨_leftUnary, _rightUnary, windowUnary, _observationsUnary, _toleranceUnary,
    ledgerUnary, sealUnary, _sameRowsUnary, _routesUnary, _provenanceUnary, _nameCertUnary,
    _leftWindowSameRows, _rightWindowSameRows, _sameRowsObservationsRoutes,
    _observationsToleranceLedger, _ledgerSealProvenance, ledgerSame, provenancePkg⟩ :=
      carrier
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed ledgerUnary sealUnary ledgerSealRead
  exact
    ⟨windowUnary, ledgerUnary, sealUnary, sealReadUnary, ledgerSealRead, ledgerSame,
      provenancePkg, sealReadPkg⟩

end BEDC.Derived.RegularCauchyComparisonUp
