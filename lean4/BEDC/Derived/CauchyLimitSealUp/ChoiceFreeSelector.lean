import BEDC.Derived.CauchyLimitSealUp

namespace BEDC.Derived.CauchyLimitSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.RegularCauchyTailSelectorUp

theorem CauchyLimitSealCarrier_choice_free_selector_nonescape [AskSetup] [PackageSetup]
    {source schedule dyadic diagonal sealRow transportRow provenance localCert endpoint precision
      stream regularity selectorDyadic selectorSeal witness selectorTransport routes
      selectorProvenance selectorName budgetWindow budgetRead completionRead selectorRead rootRead
      hostTail : BHist}
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
                Cont completionRead endpoint rootRead ->
                  hsame dyadic budgetRead ->
                    hsame selectorDyadic dyadic ->
                      hsame endpoint (append provenance localCert) ∧
                        PkgSig sealBundle endpoint sealPkg ∧
                          PkgSig selectorBundle selectorName selectorPkg ∧
                            (Cont rootRead (BHist.e0 hostTail) schedule -> False) ∧
                              (Cont rootRead (BHist.e1 hostTail) schedule -> False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier selectorPacket scheduleSourceBudget budgetDyadicRead readDiagonalCompletion
    witnessRegularityRead completionEndpointRoot sameDyadicBudget sameSelectorDyadic
  have normalForm :=
    CauchyLimitSealCarrier_tail_budget_consumer_normal_form (hostTail := hostTail) carrier selectorPacket
      scheduleSourceBudget budgetDyadicRead readDiagonalCompletion witnessRegularityRead
      completionEndpointRoot sameDyadicBudget sameSelectorDyadic
  obtain ⟨_rootReadUnary, _scheduleToRoot, _sameSealCompletion, _sameSelectorBudget,
    endpointPkg, selectorPkgSig, noE0Return, noE1Return⟩ := normalForm
  obtain ⟨_sourceUnary, _scheduleUnary, _dyadicUnary, _diagonalUnary, _sealUnary,
    _transportUnary, _provenanceUnary, _localCertUnary, _endpointUnary,
    _sourceScheduleDyadic, _dyadicDiagonalSeal, _sealTransportProvenance,
    _provenanceLocalEndpoint, sameEndpoint, _endpointPkg⟩ := carrier
  exact ⟨sameEndpoint, endpointPkg, selectorPkgSig, noE0Return, noE1Return⟩

end BEDC.Derived.CauchyLimitSealUp
