import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_selector_budget_nonescape [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n windowRead readbackRead selectorExit : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg →
      Cont t w windowRead →
        Cont windowRead q readbackRead →
          Cont readbackRead h selectorExit →
            PkgSig bundle selectorExit pkg →
              SemanticNameCert
                (fun row : BHist =>
                  CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n
                    bundle pkg ∧ hsame row selectorExit)
                (fun row : BHist =>
                  Cont u v t ∧ Cont t w windowRead ∧ Cont windowRead q readbackRead ∧
                    Cont readbackRead h row)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle p pkg ∧
                    PkgSig bundle selectorExit pkg)
                hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert
  intro carrier windowRoute readbackRoute selectorRoute selectorPkg
  rcases carrier with
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
      cUnary, pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩
  have carrierWitness :
      CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg :=
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
      cUnary, pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed tUnary wUnary windowRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary qUnary readbackRoute
  have selectorUnary : UnaryHistory selectorExit :=
    unary_cont_closed readbackUnary hUnary selectorRoute
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro selectorExit (And.intro carrierWitness (hsame_refl selectorExit))
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
        ⟨uvt, windowRoute, readbackRoute,
          cont_result_hsame_transport selectorRoute (hsame_symm source.right)⟩
    ledger_sound := by
      intro _row source
      exact ⟨unary_transport selectorUnary (hsame_symm source.right), pPkg, selectorPkg⟩
  }

end BEDC.Derived.CauchyModulusRefinementUp
