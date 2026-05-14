import BEDC.Derived.CauchyLimitSealUp.RegularTailSelectorBudgetCompatibility

namespace BEDC.Derived.CauchyLimitSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.RegularCauchyTailSelectorUp

theorem CauchyLimitSealCarrier_tail_selector_window_support_determinacy
    [AskSetup] [PackageSetup]
    {source schedule dyadic diagonal sealRow transportRow provenance localCert endpoint precision
      stream regularity selectorDyadic selectorSeal witness selectorTransport routes
      selectorProvenance selectorName budgetWindow budgetRead completionRead selectorRead
      transportedBudgetRead transportedCompletionRead transportedSelectorRead publicRead : BHist}
    {sealBundle selectorBundle : ProbeBundle ProbeName} {sealPkg selectorPkg : Pkg} :
    CauchyLimitSealCarrier source schedule dyadic diagonal sealRow transportRow provenance
        localCert endpoint sealBundle sealPkg ->
      RegularCauchyTailSelectorPacket precision stream regularity selectorDyadic selectorSeal
          witness selectorTransport routes selectorProvenance selectorName selectorBundle
          selectorPkg ->
        Cont schedule source budgetWindow ->
          Cont budgetWindow dyadic budgetRead ->
            Cont budgetRead diagonal completionRead ->
              Cont witness regularity selectorRead ->
                hsame dyadic budgetRead ->
                  hsame selectorDyadic dyadic ->
                    hsame budgetRead transportedBudgetRead ->
                      hsame completionRead transportedCompletionRead ->
                        hsame selectorRead transportedSelectorRead ->
                          Cont transportedCompletionRead endpoint publicRead ->
                            PkgSig sealBundle publicRead sealPkg ->
                              UnaryHistory transportedBudgetRead ∧
                                UnaryHistory transportedCompletionRead ∧
                                  UnaryHistory transportedSelectorRead ∧
                                    UnaryHistory publicRead ∧
                                      hsame sealRow transportedCompletionRead ∧
                                        hsame selectorDyadic transportedBudgetRead ∧
                                          Cont transportedCompletionRead endpoint publicRead ∧
                                            PkgSig sealBundle endpoint sealPkg ∧
                                              PkgSig sealBundle publicRead sealPkg ∧
                                                PkgSig selectorBundle selectorName
                                                  selectorPkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier selectorPacket scheduleSourceBudget budgetDyadicRead readDiagonalCompletion
    witnessRegularityRead sameDyadicBudget sameSelectorDyadic sameBudgetTransport
    sameCompletionTransport sameSelectorTransport transportedCompletionEndpointPublic
    publicPkg
  have budgetCompatibility :=
    CauchyLimitSealCarrier_regular_tail_selector_budget_compatibility carrier selectorPacket
      scheduleSourceBudget budgetDyadicRead readDiagonalCompletion witnessRegularityRead
      sameDyadicBudget sameSelectorDyadic sameBudgetTransport sameCompletionTransport
      sameSelectorTransport
  obtain ⟨_sourceUnary, _scheduleUnary, _dyadicUnary, _diagonalUnary, _sealUnary,
    _transportUnary, _provenanceUnary, _localCertUnary, endpointUnary,
    _sourceScheduleDyadic, _dyadicDiagonalSeal, _sealTransportProvenance,
    _provenanceLocalEndpoint, _sameEndpoint, endpointPkg⟩ := carrier
  obtain ⟨_budgetWindowUnary, _budgetReadUnary, _completionReadUnary, _selectorReadUnary,
    transportedBudgetUnary, transportedCompletionUnary, transportedSelectorUnary,
    sameSealTransportedCompletion, sameSelectorTransportedBudget, _endpointPkgFromCompatibility,
    selectorPkgSig⟩ := budgetCompatibility
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed transportedCompletionUnary endpointUnary
      transportedCompletionEndpointPublic
  exact
    ⟨transportedBudgetUnary, transportedCompletionUnary, transportedSelectorUnary,
      publicReadUnary, sameSealTransportedCompletion, sameSelectorTransportedBudget,
      transportedCompletionEndpointPublic, endpointPkg, publicPkg, selectorPkgSig⟩

end BEDC.Derived.CauchyLimitSealUp
