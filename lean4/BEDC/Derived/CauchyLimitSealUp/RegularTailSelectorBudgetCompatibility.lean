import BEDC.Derived.CauchyLimitSealUp

namespace BEDC.Derived.CauchyLimitSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.RegularCauchyTailSelectorUp

theorem CauchyLimitSealCarrier_regular_tail_selector_budget_compatibility
    [AskSetup] [PackageSetup]
    {source schedule dyadic diagonal sealRow transportRow provenance localCert endpoint
      precision stream regularity selectorDyadic selectorSeal witness selectorTransport routes
      selectorProvenance selectorName budgetWindow budgetRead completionRead selectorRead
      transportedBudgetRead transportedCompletionRead transportedSelectorRead : BHist}
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
                          UnaryHistory budgetWindow ∧ UnaryHistory budgetRead ∧
                            UnaryHistory completionRead ∧ UnaryHistory selectorRead ∧
                              UnaryHistory transportedBudgetRead ∧
                                UnaryHistory transportedCompletionRead ∧
                                  UnaryHistory transportedSelectorRead ∧
                                    hsame sealRow transportedCompletionRead ∧
                                      hsame selectorDyadic transportedBudgetRead ∧
                                        PkgSig sealBundle endpoint sealPkg ∧
                                          PkgSig selectorBundle selectorName selectorPkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier selectorPacket scheduleSourceBudget budgetDyadicRead readDiagonalCompletion
    witnessRegularityRead sameDyadicBudget sameSelectorDyadic sameBudgetTransport
    sameCompletionTransport sameSelectorTransport
  have meet :=
    CauchyLimitSealCarrier_tail_budget_meet carrier selectorPacket scheduleSourceBudget
      budgetDyadicRead readDiagonalCompletion witnessRegularityRead sameDyadicBudget
      sameSelectorDyadic
  have transported :=
    CauchyLimitSealCarrier_selector_budget_transport carrier selectorPacket
      scheduleSourceBudget budgetDyadicRead readDiagonalCompletion witnessRegularityRead
      sameDyadicBudget sameSelectorDyadic sameBudgetTransport sameCompletionTransport
      sameSelectorTransport
  obtain ⟨budgetWindowUnary, budgetReadUnary, completionReadUnary, selectorReadUnary,
    _sameSealCompletion, _sameSelectorBudget, _endpointPkgFromMeet,
    _selectorPkgFromMeet⟩ := meet
  obtain ⟨transportedBudgetUnary, transportedCompletionUnary, transportedSelectorUnary,
    sameSealTransportedCompletion, sameSelectorTransportedBudget, endpointPkg,
    selectorPkgSig⟩ := transported
  exact
    ⟨budgetWindowUnary, budgetReadUnary, completionReadUnary, selectorReadUnary,
      transportedBudgetUnary, transportedCompletionUnary, transportedSelectorUnary,
      sameSealTransportedCompletion, sameSelectorTransportedBudget, endpointPkg,
      selectorPkgSig⟩

end BEDC.Derived.CauchyLimitSealUp
