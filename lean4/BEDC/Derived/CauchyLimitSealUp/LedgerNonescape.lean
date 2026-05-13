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

end BEDC.Derived.CauchyLimitSealUp
