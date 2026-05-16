import BEDC.Derived.CauchyCriterionUp
import BEDC.Derived.FiniteObservationBudgetSelectorUp
import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.CauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCriterionCarrier_finite_selector_exhaustion [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      index windowsU modulusU toleranceU tail sealRow transportsU routesU provenanceU nameU
      selector cauchySeal uniformSeal budgetB budgetS budgetW budgetD budgetR budgetE budgetH
      budgetC budgetP budgetN selectorRequest selectorSeal pullback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg ->
      BEDC.Derived.UniformCauchyCriterionUp.UniformCauchyCriterionPacket index windowsU
          modulusU toleranceU tail sealRow transportsU routesU provenanceU nameU bundle pkg ->
        BEDC.Derived.FiniteObservationBudgetSelectorUp.FiniteObservationBudgetSelectorCarrier
          budgetB budgetS budgetW budgetD budgetR budgetE budgetH budgetC budgetP budgetN ->
          hsame ledger tail ->
            hsame realSeal sealRow ->
              Cont endpoint realSeal selector ->
                Cont ledger realSeal cauchySeal ->
                  Cont tail sealRow uniformSeal ->
                    PkgSig bundle selector pkg ->
                      PkgSig bundle cauchySeal pkg ->
                        PkgSig bundle uniformSeal pkg ->
                          Cont endpoint realSeal selectorRequest ->
                            Cont selectorRequest budgetE selectorSeal ->
                              Cont selectorSeal budgetC pullback ->
                                PkgSig bundle pullback pkg ->
                                  hsame budgetN budgetE ->
                                    UnaryHistory endpoint ∧ UnaryHistory selector ∧
                                      UnaryHistory cauchySeal ∧ UnaryHistory uniformSeal ∧
                                        UnaryHistory selectorRequest ∧
                                          UnaryHistory selectorSeal ∧
                                            UnaryHistory pullback ∧
                                              hsame cauchySeal uniformSeal ∧
                                                Cont endpoint realSeal selector ∧
                                                  Cont endpoint realSeal selectorRequest ∧
                                                    Cont selectorRequest budgetE selectorSeal ∧
                                                      Cont selectorSeal budgetC pullback ∧
                                                        PkgSig bundle endpoint pkg ∧
                                                          PkgSig bundle selector pkg ∧
                                                            PkgSig bundle pullback pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory PkgSig
  intro carrier uniformPacket budgetCarrier sameLedgerTail sameRealSealSealRow
    endpointRealSealSelector ledgerRealSealCauchySeal tailSealRowUniformSeal selectorPkg
    _cauchySealPkg _uniformSealPkg endpointRealSelectorRequest selectorBudgetSeal
    selectorBudgetPullback pullbackPkg _sameBudgetName
  obtain ⟨_windowUnary, _modulusUnary, _toleranceUnary, ledgerUnary, _regseqUnary,
    realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary,
    endpointUnary, _windowModulusTolerance, _toleranceLedgerRegseq,
    _regseqRealSealTransport, _transportLocalCertRoute, _routeProvenanceEndpoint,
    endpointPkg⟩ := carrier
  obtain ⟨_indexUnary, _windowsUnary, _modulusUUnary, _toleranceUUnary, tailUnary,
    sealRowUnary, _transportsUUnary, _routesUUnary, _provenanceUUnary, _nameUUnary,
    _indexWindowsModulus, _modulusToleranceTail, _tailSealRowTransports,
    _transportsRoutesProvenance, _nameUPkg⟩ := uniformPacket
  obtain ⟨budgetBUnary, budgetSUnary, budgetDUnary, budgetEUnary, _budgetHUnary,
    budgetSchedule, budgetWindowDyadic, budgetRegularSeal, _budgetNameSame⟩ :=
    budgetCarrier
  have budgetWUnary : UnaryHistory budgetW :=
    unary_cont_closed budgetBUnary budgetSUnary budgetSchedule
  have budgetRUnary : UnaryHistory budgetR :=
    unary_cont_closed budgetWUnary budgetDUnary budgetWindowDyadic
  have budgetCUnary : UnaryHistory budgetC :=
    unary_cont_closed budgetRUnary budgetEUnary budgetRegularSeal
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed endpointUnary realSealUnary endpointRealSealSelector
  have cauchySealUnary : UnaryHistory cauchySeal :=
    unary_cont_closed ledgerUnary realSealUnary ledgerRealSealCauchySeal
  have uniformSealUnary : UnaryHistory uniformSeal :=
    unary_cont_closed tailUnary sealRowUnary tailSealRowUniformSeal
  have selectorRequestUnary : UnaryHistory selectorRequest :=
    unary_cont_closed endpointUnary realSealUnary endpointRealSelectorRequest
  have selectorSealUnary : UnaryHistory selectorSeal :=
    unary_cont_closed selectorRequestUnary budgetEUnary selectorBudgetSeal
  have pullbackUnary : UnaryHistory pullback :=
    unary_cont_closed selectorSealUnary budgetCUnary selectorBudgetPullback
  have sameSeals : hsame cauchySeal uniformSeal :=
    cont_respects_hsame sameLedgerTail sameRealSealSealRow ledgerRealSealCauchySeal
      tailSealRowUniformSeal
  exact
    ⟨endpointUnary, selectorUnary, cauchySealUnary, uniformSealUnary, selectorRequestUnary,
      selectorSealUnary, pullbackUnary, sameSeals, endpointRealSealSelector,
      endpointRealSelectorRequest, selectorBudgetSeal, selectorBudgetPullback, endpointPkg,
      selectorPkg, pullbackPkg⟩

end BEDC.Derived.CauchyCriterionUp
