import BEDC.Derived.CauchyLimitSealUp

namespace BEDC.Derived.CauchyLimitSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.RegularCauchyTailSelectorUp

theorem CauchyLimitSealCarrier_regular_tail_selector_nonescape [AskSetup] [PackageSetup]
    {source schedule dyadic diagonal sealRow transportRow provenance localCert endpoint precision
      stream regularity selectorDyadic selectorSeal witness selectorTransport routes
      selectorProvenance selectorName budgetWindow budgetRead completionRead selectorRead
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
                Cont completionRead endpoint rootRead →
                  hsame dyadic budgetRead →
                    hsame selectorDyadic dyadic →
                      UnaryHistory budgetWindow ∧ UnaryHistory budgetRead ∧
                        UnaryHistory completionRead ∧ UnaryHistory selectorRead ∧
                          UnaryHistory rootRead ∧ hsame sealRow completionRead ∧
                            hsame selectorDyadic budgetRead ∧
                              hsame endpoint (append provenance localCert) ∧
                                PkgSig sealBundle endpoint sealPkg ∧
                                  PkgSig selectorBundle selectorName selectorPkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier selectorPacket scheduleSourceBudget budgetDyadicRead readDiagonalCompletion
    witnessRegularityRead completionEndpointRoot sameDyadicBudget sameSelectorDyadic
  have coverage :=
    CauchyLimitSealCarrier_root_budget_seal_coverage carrier selectorPacket
      scheduleSourceBudget budgetDyadicRead readDiagonalCompletion witnessRegularityRead
      completionEndpointRoot sameDyadicBudget sameSelectorDyadic
  obtain ⟨budgetWindowUnary, budgetReadUnary, completionReadUnary, selectorReadUnary,
    rootReadUnary, sameSealCompletion, sameSelectorBudget, endpointPkg, selectorPkgSig⟩ :=
    coverage
  obtain ⟨_sourceUnary, _scheduleUnary, _dyadicUnary, _diagonalUnary, _sealUnary,
    _transportUnary, _provenanceUnary, _localCertUnary, _endpointUnary,
    _sourceScheduleDyadic, _dyadicDiagonalSeal, _sealTransportProvenance,
    _provenanceLocalEndpoint, sameEndpoint, _endpointPkgCarrier⟩ := carrier
  exact
    ⟨budgetWindowUnary, budgetReadUnary, completionReadUnary, selectorReadUnary,
      rootReadUnary, sameSealCompletion, sameSelectorBudget, sameEndpoint, endpointPkg,
      selectorPkgSig⟩

end BEDC.Derived.CauchyLimitSealUp
