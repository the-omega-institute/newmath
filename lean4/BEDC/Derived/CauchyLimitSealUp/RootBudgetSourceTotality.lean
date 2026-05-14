import BEDC.Derived.CauchyLimitSealUp

namespace BEDC.Derived.CauchyLimitSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
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

end BEDC.Derived.CauchyLimitSealUp
