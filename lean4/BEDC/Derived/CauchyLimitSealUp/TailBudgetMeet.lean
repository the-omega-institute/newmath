import BEDC.Derived.CauchyLimitSealUp

namespace BEDC.Derived.CauchyLimitSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.RegularCauchyTailSelectorUp

theorem CauchyLimitSealCarrier_completion_budget_root_unblock [AskSetup] [PackageSetup]
    {source schedule dyadic diagonal sealRow transportRow provenance localCert endpoint precision
      stream regularity selectorDyadic selectorSeal witness selectorTransport routes
      selectorProvenance selectorName budgetWindow budgetRead completionRead selectorRead
      transportedBudgetRead transportedCompletionRead transportedSelectorRead rootRead : BHist}
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
                          Cont transportedCompletionRead endpoint rootRead ->
                            UnaryHistory rootRead ∧
                              Cont schedule (append source (append dyadic (append diagonal endpoint)))
                                rootRead ∧
                                hsame sealRow transportedCompletionRead ∧
                                  PkgSig sealBundle endpoint sealPkg ∧
                                    PkgSig selectorBundle selectorName selectorPkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier selectorPacket scheduleSourceBudget budgetDyadicRead readDiagonalCompletion
    witnessRegularityRead sameDyadicBudget sameSelectorDyadic sameBudgetTransport
    sameCompletionTransport sameSelectorTransport transportedCompletionEndpointRoot
  have transported :=
    CauchyLimitSealCarrier_selector_budget_transport carrier selectorPacket
      scheduleSourceBudget budgetDyadicRead readDiagonalCompletion witnessRegularityRead
      sameDyadicBudget sameSelectorDyadic sameBudgetTransport sameCompletionTransport
      sameSelectorTransport
  obtain ⟨_transportedBudgetUnary, transportedCompletionUnary, _transportedSelectorUnary,
    sameSealTransportedCompletion, _sameSelectorTransportedBudget, endpointPkg,
    selectorPkgSig⟩ := transported
  obtain ⟨_sourceUnary, _scheduleUnary, _dyadicUnary, _diagonalUnary, _sealUnary,
    _transportUnary, _provenanceUnary, _localCertUnary, endpointUnary,
    _sourceScheduleDyadic, _dyadicDiagonalSeal, _sealTransportProvenance,
    _provenanceLocalEndpoint, _sameEndpoint, _carrierEndpointPkg⟩ := carrier
  have rootReadUnary : UnaryHistory rootRead :=
    unary_cont_closed transportedCompletionUnary endpointUnary transportedCompletionEndpointRoot
  have scheduleToRoot :
      Cont schedule (append source (append dyadic (append diagonal endpoint))) rootRead := by
    cases scheduleSourceBudget
    cases budgetDyadicRead
    cases readDiagonalCompletion
    cases sameCompletionTransport
    cases transportedCompletionEndpointRoot
    exact
      (append_assoc (append (append schedule source) dyadic) diagonal endpoint).trans
        ((append_assoc (append schedule source) dyadic (append diagonal endpoint)).trans
          (append_assoc schedule source (append dyadic (append diagonal endpoint))))
  exact
    ⟨rootReadUnary, scheduleToRoot, sameSealTransportedCompletion, endpointPkg,
      selectorPkgSig⟩

theorem CauchyLimitSealCarrier_tail_budget_meet_exactness [AskSetup] [PackageSetup]
    {source schedule dyadic diagonal sealRow transportRow provenance localCert endpoint precision
      stream regularity selectorDyadic selectorSeal witness selectorTransport routes
      selectorProvenance selectorName budgetWindow budgetRead completionRead selectorRead meetRead
      rootRead : BHist}
    {sealBundle selectorBundle : ProbeBundle ProbeName} {sealPkg selectorPkg : Pkg} :
    CauchyLimitSealCarrier source schedule dyadic diagonal sealRow transportRow provenance
        localCert endpoint sealBundle sealPkg →
      RegularCauchyTailSelectorPacket precision stream regularity selectorDyadic selectorSeal
          witness selectorTransport routes selectorProvenance selectorName selectorBundle
          selectorPkg →
        Cont schedule source budgetWindow →
          Cont budgetWindow dyadic budgetRead →
            Cont budgetRead diagonal completionRead →
              Cont witness regularity selectorRead →
                Cont budgetWindow budgetRead meetRead →
                  Cont meetRead completionRead rootRead →
                    hsame dyadic budgetRead →
                      hsame selectorDyadic dyadic →
                        UnaryHistory meetRead ∧ UnaryHistory rootRead ∧
                          hsame rootRead (append (append budgetWindow budgetRead)
                            completionRead) ∧
                            hsame sealRow completionRead ∧ hsame selectorDyadic budgetRead ∧
                              PkgSig sealBundle endpoint sealPkg ∧
                                PkgSig selectorBundle selectorName selectorPkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier selectorPacket scheduleSourceBudget budgetDyadicRead readDiagonalCompletion
    witnessRegularityRead budgetMeetRead meetCompletionRoot sameDyadicBudget
    sameSelectorDyadic
  have meet :=
    CauchyLimitSealCarrier_tail_budget_meet carrier selectorPacket scheduleSourceBudget
      budgetDyadicRead readDiagonalCompletion witnessRegularityRead sameDyadicBudget
      sameSelectorDyadic
  obtain ⟨budgetWindowUnary, budgetReadUnary, _completionReadUnary, _selectorReadUnary,
    sameSealCompletion, sameSelectorBudget, endpointPkg, selectorPkgSig⟩ := meet
  have meetReadUnary : UnaryHistory meetRead :=
    unary_cont_closed budgetWindowUnary budgetReadUnary budgetMeetRead
  have rootReadUnary : UnaryHistory rootRead :=
    unary_cont_closed meetReadUnary _completionReadUnary meetCompletionRoot
  have rootExact : hsame rootRead (append (append budgetWindow budgetRead) completionRead) := by
    cases budgetMeetRead
    cases meetCompletionRoot
    rfl
  exact
    ⟨meetReadUnary, rootReadUnary, rootExact, sameSealCompletion, sameSelectorBudget,
      endpointPkg, selectorPkgSig⟩

end BEDC.Derived.CauchyLimitSealUp
