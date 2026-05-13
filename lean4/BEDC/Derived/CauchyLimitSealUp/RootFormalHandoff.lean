import BEDC.Derived.CauchyLimitSealUp

namespace BEDC.Derived.CauchyLimitSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.RegularCauchyTailSelectorUp

theorem CauchyLimitSealCarrier_root_choice_free_route [AskSetup] [PackageSetup]
    {source schedule dyadic diagonal sealRow transportRow provenance localCert endpoint precision
      stream regularity selectorDyadic selectorSeal witness selectorTransport routes
      selectorProvenance selectorName budgetWindow budgetRead completionRead selectorRead rootRead :
        BHist}
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
                      UnaryHistory budgetWindow ∧ UnaryHistory budgetRead ∧
                        UnaryHistory completionRead ∧ UnaryHistory selectorRead ∧
                          UnaryHistory rootRead ∧ hsame sealRow completionRead ∧
                            hsame selectorDyadic budgetRead ∧
                              hsame endpoint (append provenance localCert) ∧
                                PkgSig sealBundle endpoint sealPkg ∧
                                  PkgSig selectorBundle selectorName selectorPkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
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
    _provenanceLocalEndpoint, sameEndpoint, _endpointPkg⟩ := carrier
  exact
    ⟨budgetWindowUnary, budgetReadUnary, completionReadUnary, selectorReadUnary,
      rootReadUnary, sameSealCompletion, sameSelectorBudget, sameEndpoint, endpointPkg,
      selectorPkgSig⟩

theorem CauchyLimitSealCarrier_root_formal_handoff_package [AskSetup] [PackageSetup]
    {source schedule dyadic diagonal sealRow transportRow provenance localCert endpoint precision
      stream regularity selectorDyadic selectorSeal witness selectorTransport routes
      selectorProvenance selectorName budgetWindow budgetRead completionRead selectorRead rootRead
      formalSurface : BHist}
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
                  Cont rootRead provenance formalSurface ->
                    hsame dyadic budgetRead ->
                      hsame selectorDyadic dyadic ->
                        PkgSig sealBundle formalSurface sealPkg ->
                          SemanticNameCert
                            (fun row : BHist =>
                              hsame row formalSurface ∧ UnaryHistory row ∧
                                PkgSig sealBundle row sealPkg)
                            (fun row : BHist => hsame row formalSurface ∧ UnaryHistory row)
                            (fun _row : BHist =>
                              PkgSig sealBundle endpoint sealPkg ∧
                                PkgSig selectorBundle selectorName selectorPkg ∧
                                  Cont completionRead endpoint rootRead ∧
                                    Cont rootRead provenance formalSurface)
                            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier selectorPacket scheduleSourceBudget budgetDyadicRead readDiagonalCompletion
    witnessRegularityRead completionEndpointRoot rootProvenanceFormal sameDyadicBudget
    sameSelectorDyadic formalPkg
  have coverage :=
    CauchyLimitSealCarrier_root_budget_seal_coverage carrier selectorPacket
      scheduleSourceBudget budgetDyadicRead readDiagonalCompletion witnessRegularityRead
      completionEndpointRoot sameDyadicBudget sameSelectorDyadic
  obtain ⟨_sourceUnary, _scheduleUnary, _dyadicUnary, _diagonalUnary, _sealUnary,
    _transportUnary, provenanceUnary, _localCertUnary, _endpointUnary,
    _sourceScheduleDyadic, _dyadicDiagonalSeal, _sealTransportProvenance,
    _provenanceLocalEndpoint, _sameEndpoint, endpointPkg⟩ := carrier
  obtain ⟨_budgetWindowUnary, _budgetReadUnary, _completionReadUnary, _selectorReadUnary,
    rootReadUnary, _sameSealCompletion, _sameSelectorBudget, _coverageEndpointPkg,
    selectorPkgSig⟩ := coverage
  have formalUnary : UnaryHistory formalSurface :=
    unary_cont_closed rootReadUnary provenanceUnary rootProvenanceFormal
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro formalSurface ⟨hsame_refl formalSurface, formalUnary, formalPkg⟩
      equiv_refl := by
        intro row _sourceRow
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' classified
        exact hsame_symm classified
      equiv_trans := by
        intro _row _row' _row'' leftClassified rightClassified
        exact hsame_trans leftClassified rightClassified
      carrier_respects_equiv := by
        intro _row _row' classified sourceRow
        cases classified
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, sourceRow.right.left⟩
    ledger_sound := by
      intro _row _sourceRow
      exact ⟨endpointPkg, selectorPkgSig, completionEndpointRoot, rootProvenanceFormal⟩
  }

end BEDC.Derived.CauchyLimitSealUp
