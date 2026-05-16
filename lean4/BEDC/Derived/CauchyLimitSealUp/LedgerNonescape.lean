import BEDC.Derived.CauchyLimitSealUp

namespace BEDC.Derived.CauchyLimitSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyLimitSealCarrier_ledger_nonescape_totality [AskSetup] [PackageSetup]
    {source schedule dyadic diagonal sealRow transportRow provenance localCert endpoint
      budgetWindow budgetRead completionRead realRead hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyLimitSealCarrier source schedule dyadic diagonal sealRow transportRow provenance
        localCert endpoint bundle pkg ->
      Cont schedule source budgetWindow ->
        Cont budgetWindow dyadic budgetRead ->
          Cont budgetRead diagonal completionRead ->
            Cont completionRead endpoint realRead ->
              hsame dyadic budgetRead ->
                UnaryHistory budgetWindow ∧ UnaryHistory budgetRead ∧
                  UnaryHistory completionRead ∧ UnaryHistory realRead ∧
                    hsame sealRow completionRead ∧ PkgSig bundle endpoint pkg ∧
                      (Cont realRead (BHist.e0 hostTail) budgetRead -> False) ∧
                        (Cont realRead (BHist.e1 hostTail) budgetRead -> False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier scheduleSourceBudget budgetDyadicRead readDiagonalCompletion
    completionEndpointReal sameDyadicBudget
  have exhaustion :=
    CauchyLimitSealCarrier_real_handoff_exhaustion carrier scheduleSourceBudget
      budgetDyadicRead readDiagonalCompletion completionEndpointReal sameDyadicBudget
  obtain ⟨budgetWindowUnary, budgetReadUnary, completionReadUnary, realReadUnary,
    sameSealCompletion, endpointPkg⟩ := exhaustion
  have budgetToReal : Cont budgetRead (append diagonal endpoint) realRead := by
    cases readDiagonalCompletion
    exact completionEndpointReal.trans (append_assoc budgetRead diagonal endpoint)
  exact
    ⟨budgetWindowUnary, budgetReadUnary, completionReadUnary, realReadUnary,
      sameSealCompletion, endpointPkg,
      (fun hostReturn =>
        cont_mutual_extension_right_tail_absurd.left budgetToReal hostReturn),
      (fun hostReturn =>
        cont_mutual_extension_right_tail_absurd.right budgetToReal hostReturn)⟩

theorem CauchyLimitSealCarrier_regseqrat_window_nonescape [AskSetup] [PackageSetup]
    {source schedule dyadic diagonal sealRow transportRow provenance localCert endpoint window
      observation realRead hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyLimitSealCarrier source schedule dyadic diagonal sealRow transportRow provenance
        localCert endpoint bundle pkg ->
      Cont schedule source window ->
        Cont window dyadic observation ->
          Cont observation diagonal realRead ->
            hsame dyadic observation ->
              UnaryHistory window ∧ UnaryHistory observation ∧ UnaryHistory realRead ∧
                hsame sealRow realRead ∧ PkgSig bundle endpoint pkg ∧
                  (Cont realRead (BHist.e0 hostTail) window -> False) ∧
                    (Cont realRead (BHist.e1 hostTail) window -> False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier scheduleSourceWindow windowDyadicObservation observationDiagonalReal
    sameDyadicObservation
  obtain ⟨sourceUnary, scheduleUnary, dyadicUnary, diagonalUnary, _sealUnary,
    _transportUnary, _provenanceUnary, _localCertUnary, _endpointUnary,
    _sourceScheduleDyadic, dyadicDiagonalSeal, _sealTransportProvenance,
    _provenanceLocalEndpoint, _sameEndpoint, endpointPkg⟩ := carrier
  have windowUnary : UnaryHistory window :=
    unary_cont_closed scheduleUnary sourceUnary scheduleSourceWindow
  have observationUnary : UnaryHistory observation :=
    unary_cont_closed windowUnary dyadicUnary windowDyadicObservation
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed observationUnary diagonalUnary observationDiagonalReal
  have sameSealReal : hsame sealRow realRead :=
    cont_respects_hsame sameDyadicObservation (hsame_refl diagonal) dyadicDiagonalSeal
      observationDiagonalReal
  have windowToReal : Cont window (append dyadic diagonal) realRead := by
    cases windowDyadicObservation
    exact observationDiagonalReal.trans (append_assoc window dyadic diagonal)
  exact
    ⟨windowUnary, observationUnary, realUnary, sameSealReal, endpointPkg,
      (fun hostReturn =>
        cont_mutual_extension_right_tail_absurd.left windowToReal hostReturn),
      (fun hostReturn =>
        cont_mutual_extension_right_tail_absurd.right windowToReal hostReturn)⟩

end BEDC.Derived.CauchyLimitSealUp
