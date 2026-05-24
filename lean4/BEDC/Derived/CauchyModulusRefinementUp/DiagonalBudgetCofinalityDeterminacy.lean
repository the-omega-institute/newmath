import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_diagonal_budget_cofinality_determinacy
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n cofinalRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont q e cofinalRead ->
        Cont cofinalRead e terminalRead ->
          PkgSig bundle cofinalRead pkg ->
            PkgSig bundle terminalRead pkg ->
              SemanticNameCert
                (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  Cont q e cofinalRead ∧ Cont cofinalRead e row ∧
                    PkgSig bundle cofinalRead pkg ∧ PkgSig bundle terminalRead pkg)
                (fun row : BHist => hsame row terminalRead ∧ PkgSig bundle terminalRead pkg)
                hsame := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame SemanticNameCert
  intro carrier cofinalRoute terminalRoute cofinalPkg terminalPkg
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, _tUnary, _wUnary, qUnary, eUnary,
      _hUnary, _cUnary, _pUnary, _nUnary, _m0m1u, _uvt, _twq, _qeh, _pPkg, _hn⟩
  have cofinalUnary : UnaryHistory cofinalRead :=
    unary_cont_closed qUnary eUnary cofinalRoute
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed cofinalUnary eUnary terminalRoute
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro terminalRead (And.intro (hsame_refl terminalRead) terminalUnary)
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨cofinalRoute,
          cont_result_hsame_transport terminalRoute (hsame_symm source.left), cofinalPkg,
          terminalPkg⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, terminalPkg⟩
  }

end BEDC.Derived.CauchyModulusRefinementUp
