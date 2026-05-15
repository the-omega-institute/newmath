import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_window_consumer_coverage [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n selected readback visible : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg →
      Cont t w selected →
        Cont selected q readback →
          Cont readback n visible →
            PkgSig bundle visible pkg →
              SemanticNameCert
                (fun row : BHist =>
                  CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n
                    bundle pkg ∧ hsame row visible)
                (fun row : BHist =>
                  Cont m0 m1 u ∧ Cont u v t ∧ Cont t w selected ∧
                    Cont selected q readback ∧ Cont readback n row ∧
                      PkgSig bundle visible pkg)
                (fun row : BHist => UnaryHistory row ∧ PkgSig bundle visible pkg)
                hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg SemanticNameCert
  intro carrier selectedRoute readbackRoute visibleRoute visiblePkg
  rcases carrier with
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, _eUnary,
      _hUnary, _cUnary, pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed tUnary wUnary selectedRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed selectedUnary qUnary readbackRoute
  have visibleUnary : UnaryHistory visible :=
    unary_cont_closed readbackUnary nUnary visibleRoute
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro visible
          (And.intro
            ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, _eUnary,
              _hUnary, _cUnary, pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩
            (hsame_refl visible))
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
        ⟨m0m1u, uvt, selectedRoute, readbackRoute,
          cont_result_hsame_transport visibleRoute (hsame_symm source.right), visiblePkg⟩
    ledger_sound := by
      intro row source
      exact And.intro (unary_transport visibleUnary (hsame_symm source.right)) visiblePkg
  }

end BEDC.Derived.CauchyModulusRefinementUp
