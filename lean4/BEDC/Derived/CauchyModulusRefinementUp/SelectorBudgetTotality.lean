import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_selector_budget_totality [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n windowRead readbackRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont t w windowRead ->
        Cont windowRead q readbackRead ->
          PkgSig bundle windowRead pkg ->
            PkgSig bundle readbackRead pkg ->
              SemanticNameCert
                (fun row : BHist =>
                  CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ∧
                    hsame row readbackRead)
                (fun row : BHist =>
                  Cont u v t ∧ Cont t w windowRead ∧ Cont windowRead q row ∧
                    PkgSig bundle readbackRead pkg)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle windowRead pkg ∧
                    PkgSig bundle readbackRead pkg)
                hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert
  intro carrier windowRoute readbackRoute windowPkg readbackPkg
  rcases carrier with
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary, cUnary,
      pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩
  have carrierWitness :
      CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg :=
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary, cUnary,
      pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed tUnary wUnary windowRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary qUnary readbackRoute
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro readbackRead (And.intro carrierWitness (hsame_refl readbackRead))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro row source
      exact
        ⟨uvt, windowRoute,
          cont_result_hsame_transport readbackRoute (hsame_symm source.right), readbackPkg⟩
    ledger_sound := by
      intro row source
      exact
        ⟨unary_transport readbackUnary (hsame_symm source.right), windowPkg, readbackPkg⟩
  }

end BEDC.Derived.CauchyModulusRefinementUp
