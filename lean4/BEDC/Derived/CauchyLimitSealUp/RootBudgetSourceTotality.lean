import BEDC.Derived.CauchyLimitSealUp

namespace BEDC.Derived.CauchyLimitSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyLimitSealCarrier_budget_root_source_totality [AskSetup] [PackageSetup]
    {source schedule dyadic diagonal sealRow transportRow provenance localCert endpoint
      budgetWindow budgetRead completionRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyLimitSealCarrier source schedule dyadic diagonal sealRow transportRow provenance
        localCert endpoint bundle pkg ->
      Cont schedule source budgetWindow ->
        Cont budgetWindow dyadic budgetRead ->
          Cont budgetRead diagonal completionRead ->
            Cont completionRead endpoint consumerRead ->
              hsame dyadic budgetRead ->
                UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory dyadic ∧
                  UnaryHistory diagonal ∧ UnaryHistory sealRow ∧ UnaryHistory budgetWindow ∧
                    UnaryHistory budgetRead ∧ UnaryHistory completionRead ∧
                      UnaryHistory consumerRead ∧ hsame sealRow completionRead ∧
                        hsame endpoint (append provenance localCert) ∧
                          PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier scheduleSourceBudget budgetWindowDyadicRead budgetReadDiagonalCompletion
    completionEndpointConsumer sameDyadicBudget
  obtain ⟨sourceUnary, scheduleUnary, dyadicUnary, diagonalUnary, sealUnary,
    _transportUnary, _provenanceUnary, _localCertUnary, endpointUnary,
    _sourceScheduleDyadic, dyadicDiagonalSeal, _sealTransportProvenance,
    _provenanceLocalEndpoint, sameEndpoint, endpointPkg⟩ := carrier
  have budgetWindowUnary : UnaryHistory budgetWindow :=
    unary_cont_closed scheduleUnary sourceUnary scheduleSourceBudget
  have budgetReadUnary : UnaryHistory budgetRead :=
    unary_cont_closed budgetWindowUnary dyadicUnary budgetWindowDyadicRead
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed budgetReadUnary diagonalUnary budgetReadDiagonalCompletion
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed completionReadUnary endpointUnary completionEndpointConsumer
  have sameSealCompletion : hsame sealRow completionRead :=
    cont_respects_hsame sameDyadicBudget (hsame_refl diagonal) dyadicDiagonalSeal
      budgetReadDiagonalCompletion
  exact
    ⟨sourceUnary, scheduleUnary, dyadicUnary, diagonalUnary, sealUnary, budgetWindowUnary,
      budgetReadUnary, completionReadUnary, consumerReadUnary, sameSealCompletion,
      sameEndpoint, endpointPkg⟩

theorem CauchyLimitSealCarrier_budget_source_endpoint_exhaustion
    [AskSetup] [PackageSetup]
    {source schedule dyadic diagonal sealRow transportRow provenance localCert endpoint
      budgetWindow budgetRead completionRead endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyLimitSealCarrier source schedule dyadic diagonal sealRow transportRow provenance
        localCert endpoint bundle pkg ->
      Cont schedule source budgetWindow ->
        Cont budgetWindow dyadic budgetRead ->
          Cont budgetRead diagonal completionRead ->
            Cont completionRead endpoint endpointRead ->
              hsame dyadic budgetRead ->
                UnaryHistory budgetWindow ∧ UnaryHistory budgetRead ∧
                  UnaryHistory completionRead ∧ UnaryHistory endpointRead ∧
                    hsame sealRow completionRead ∧ hsame endpoint (append provenance localCert) ∧
                      PkgSig bundle endpoint pkg ∧
                        SemanticNameCert
                          (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row)
                          (fun row : BHist => hsame row endpointRead)
                          (fun row : BHist => hsame row endpointRead ∧ PkgSig bundle endpoint pkg)
                          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier scheduleSourceBudget budgetWindowDyadicRead budgetReadDiagonalCompletion
    completionEndpointRead sameDyadicBudget
  obtain ⟨sourceUnary, scheduleUnary, dyadicUnary, diagonalUnary, _sealUnary,
    _transportUnary, _provenanceUnary, _localCertUnary, endpointUnary,
    _sourceScheduleDyadic, dyadicDiagonalSeal, _sealTransportProvenance,
    _provenanceLocalEndpoint, sameEndpoint, endpointPkg⟩ := carrier
  have budgetWindowUnary : UnaryHistory budgetWindow :=
    unary_cont_closed scheduleUnary sourceUnary scheduleSourceBudget
  have budgetReadUnary : UnaryHistory budgetRead :=
    unary_cont_closed budgetWindowUnary dyadicUnary budgetWindowDyadicRead
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed budgetReadUnary diagonalUnary budgetReadDiagonalCompletion
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed completionReadUnary endpointUnary completionEndpointRead
  have sameSealCompletion : hsame sealRow completionRead :=
    cont_respects_hsame sameDyadicBudget (hsame_refl diagonal) dyadicDiagonalSeal
      budgetReadDiagonalCompletion
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row)
        (fun row : BHist => hsame row endpointRead)
        (fun row : BHist => hsame row endpointRead ∧ PkgSig bundle endpoint pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro endpointRead (And.intro (hsame_refl endpointRead) endpointReadUnary)
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact And.intro (hsame_trans (hsame_symm same) source.left)
            (unary_transport source.right same)
      }
      pattern_sound := by
        intro _row source
        exact source.left
      ledger_sound := by
        intro _row source
        exact And.intro source.left endpointPkg
    }
  exact
    ⟨budgetWindowUnary, budgetReadUnary, completionReadUnary, endpointReadUnary,
      sameSealCompletion, sameEndpoint, endpointPkg, cert⟩

theorem CauchyLimitSealCarrier_root_l10_sibling_route [AskSetup] [PackageSetup]
    {source schedule dyadic diagonal sealRow transportRow provenance localCert endpoint
      budgetWindow budgetRead completionRead rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyLimitSealCarrier source schedule dyadic diagonal sealRow transportRow provenance
        localCert endpoint bundle pkg ->
      Cont schedule source budgetWindow ->
        Cont budgetWindow dyadic budgetRead ->
          Cont budgetRead diagonal completionRead ->
            Cont completionRead endpoint rootRead ->
              hsame dyadic budgetRead ->
                UnaryHistory rootRead ∧
                  Cont schedule (append source (append dyadic (append diagonal endpoint)))
                    rootRead ∧
                    hsame sealRow completionRead ∧ hsame endpoint (append provenance localCert) ∧
                      PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier scheduleSourceBudget budgetWindowDyadicRead budgetReadDiagonalCompletion
    completionEndpointRoot sameDyadicBudget
  have totality :=
    CauchyLimitSealCarrier_budget_root_source_totality carrier scheduleSourceBudget
      budgetWindowDyadicRead budgetReadDiagonalCompletion completionEndpointRoot sameDyadicBudget
  obtain ⟨_sourceUnary, _scheduleUnary, _dyadicUnary, _diagonalUnary, _sealUnary,
    _budgetWindowUnary, _budgetReadUnary, _completionReadUnary, rootReadUnary,
    sameSealCompletion, sameEndpoint, endpointPkg⟩ := totality
  have scheduleToRoot :
      Cont schedule (append source (append dyadic (append diagonal endpoint))) rootRead := by
    cases scheduleSourceBudget
    cases budgetWindowDyadicRead
    cases budgetReadDiagonalCompletion
    cases completionEndpointRoot
    exact
      (append_assoc (append (append schedule source) dyadic) diagonal endpoint).trans
        ((append_assoc (append schedule source) dyadic (append diagonal endpoint)).trans
          (append_assoc schedule source (append dyadic (append diagonal endpoint))))
  exact ⟨rootReadUnary, scheduleToRoot, sameSealCompletion, sameEndpoint, endpointPkg⟩

end BEDC.Derived.CauchyLimitSealUp
