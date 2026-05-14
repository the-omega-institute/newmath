import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementTailMeetBudgetRouteUniqueness [AskSetup] [PackageSetup]
    {tailBudget observation limiter entry m0 m1 u v t w q e h c p n publicRead
      publicReadPrime : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory tailBudget ->
      UnaryHistory observation ->
        Cont tailBudget observation limiter ->
          Cont limiter m0 entry ->
            CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
              Cont h c publicRead ->
                Cont h c publicReadPrime ->
                  hsame publicRead publicReadPrime ->
                    PkgSig bundle publicRead pkg ->
                      PkgSig bundle publicReadPrime pkg ->
                        SemanticNameCert
                          (fun row : BHist =>
                            CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n
                              bundle pkg ∧ hsame row publicRead)
                          (fun row : BHist =>
                            Cont tailBudget observation limiter ∧ Cont limiter m0 entry ∧
                              Cont m0 m1 u ∧ Cont u v t ∧ Cont q e h ∧
                                Cont h c row ∧ PkgSig bundle publicRead pkg)
                          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle publicRead pkg)
                          hsame := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame SemanticNameCert
  intro tailUnary observationUnary tailObservationLimiter limiterEntry carrier hPublicRead
    hPublicReadPrime samePublicReads publicPkg _publicPrimePkg
  rcases carrier with
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary, cUnary,
      pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩
  have limiterUnary : UnaryHistory limiter :=
    unary_cont_closed tailUnary observationUnary tailObservationLimiter
  have _entryUnary : UnaryHistory entry :=
    unary_cont_closed limiterUnary m0Unary limiterEntry
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed hUnary cUnary hPublicRead
  have carrierWitness :
      CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg :=
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary, cUnary,
      pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩
  have transportedPrime : Cont h c publicRead :=
    cont_result_hsame_transport hPublicReadPrime (hsame_symm samePublicReads)
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead (And.intro carrierWitness (hsame_refl publicRead))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨tailObservationLimiter, limiterEntry, m0m1u, uvt, qeh,
          cont_result_hsame_transport transportedPrime (hsame_symm source.right), publicPkg⟩
    ledger_sound := by
      intro _row source
      exact ⟨unary_transport publicUnary (hsame_symm source.right), publicPkg⟩
  }

end BEDC.Derived.CauchyModulusRefinementUp
