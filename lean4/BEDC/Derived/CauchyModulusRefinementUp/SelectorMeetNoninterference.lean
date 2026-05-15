import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_selector_meet_noninterference [AskSetup]
    [PackageSetup]
    {m0 m1 u v t w q e h c p n hidden secondMeet quotient selectedLimit hostEquality
      ambient : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont hidden secondMeet quotient ->
        Cont selectedLimit hostEquality ambient ->
          SemanticNameCert
            (fun row : BHist =>
              CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ∧
                (hsame row u ∨ hsame row t ∨ hsame row q ∨ hsame row e ∨ hsame row n))
            (fun row : BHist =>
              Cont m0 m1 u ∧ Cont u v t ∧ Cont t w q ∧ Cont q e h ∧
                PkgSig bundle p pkg ∧ Cont hidden secondMeet quotient ∧
                  Cont selectedLimit hostEquality ambient ∧
                    (hsame row u ∨ hsame row t ∨ hsame row q ∨ hsame row e ∨
                      hsame row n))
            (fun row : BHist => UnaryHistory row ∧ PkgSig bundle p pkg)
            hsame := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame SemanticNameCert
  intro carrier hiddenMeet selectedAmbient
  rcases carrier with
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary, cUnary,
      pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩
  have carrierWitness :
      CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg :=
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
      cUnary, pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro u (And.intro carrierWitness (Or.inl (hsame_refl u)))
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
        intro row row' sameRows source
        refine And.intro source.left ?_
        cases source.right with
        | inl sameU =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameU)
        | inr rest =>
            cases rest with
            | inl sameT =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameT))
            | inr rest =>
                cases rest with
                | inl sameQ =>
                    exact Or.inr (Or.inr (Or.inl
                      (hsame_trans (hsame_symm sameRows) sameQ)))
                | inr rest =>
                    cases rest with
                    | inl sameE =>
                        exact Or.inr (Or.inr (Or.inr (Or.inl
                          (hsame_trans (hsame_symm sameRows) sameE))))
                    | inr sameN =>
                        exact Or.inr (Or.inr (Or.inr (Or.inr
                          (hsame_trans (hsame_symm sameRows) sameN))))
    }
    pattern_sound := by
      intro row source
      exact
        ⟨m0m1u, uvt, twq, qeh, pPkg, hiddenMeet, selectedAmbient, source.right⟩
    ledger_sound := by
      intro row source
      cases source.right with
      | inl sameU =>
          exact And.intro (unary_transport uUnary (hsame_symm sameU)) pPkg
      | inr rest =>
          cases rest with
          | inl sameT =>
              exact And.intro (unary_transport tUnary (hsame_symm sameT)) pPkg
          | inr rest =>
              cases rest with
              | inl sameQ =>
                  exact And.intro (unary_transport qUnary (hsame_symm sameQ)) pPkg
              | inr rest =>
                  cases rest with
                  | inl sameE =>
                      exact And.intro (unary_transport eUnary (hsame_symm sameE)) pPkg
                  | inr sameN =>
                      exact And.intro (unary_transport nUnary (hsame_symm sameN)) pPkg
  }

end BEDC.Derived.CauchyModulusRefinementUp
