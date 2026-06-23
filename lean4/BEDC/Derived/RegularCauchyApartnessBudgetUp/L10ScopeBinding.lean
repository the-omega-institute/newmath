import BEDC.Derived.RegularCauchyApartnessBudgetUp.TasteGate

namespace BEDC.Derived.RegularCauchyApartnessBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyApartnessBudgetCarrier_l10_scope_binding [AskSetup] [PackageSetup]
    {X A M W D R E H C P N realRead scopeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyApartnessBudgetCarrier X A M W D R E H C P N bundle pkg ->
      Cont R E realRead ->
        Cont realRead H scopeRead ->
          PkgSig bundle scopeRead pkg ->
            SemanticNameCert
              (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row X ∨ hsame row A ∨ hsame row M ∨ hsame row W ∨
                  hsame row D ∨ hsame row R ∨ hsame row E ∨ hsame row scopeRead)
              (fun row : BHist =>
                hsame row scopeRead ∧ Cont A M W ∧ Cont W D R ∧
                  Cont R E realRead ∧ Cont realRead H scopeRead ∧
                    PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
                      PkgSig bundle scopeRead pkg)
              hsame ∧ UnaryHistory W ∧ UnaryHistory R ∧ UnaryHistory realRead ∧
                UnaryHistory scopeRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier realRoute scopeRoute scopePkg
  obtain ⟨_xUnary, _aUnary, _mUnary, wUnary, _dUnary, rUnary, eUnary, hUnary,
    _cUnary, _pUnary, _nUnary, budgetRoute, lowerRoute, pkgP, pkgN⟩ := carrier
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed rUnary eUnary realRoute
  have scopeUnary : UnaryHistory scopeRead :=
    unary_cont_closed realUnary hUnary scopeRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row X ∨ hsame row A ∨ hsame row M ∨ hsame row W ∨
            hsame row D ∨ hsame row R ∨ hsame row E ∨ hsame row scopeRead)
        (fun row : BHist =>
          hsame row scopeRead ∧ Cont A M W ∧ Cont W D R ∧
            Cont R E realRead ∧ Cont realRead H scopeRead ∧ PkgSig bundle P pkg ∧
              PkgSig bundle N pkg ∧ PkgSig bundle scopeRead pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro scopeRead ⟨hsame_refl scopeRead, scopeUnary⟩
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
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.left, budgetRoute, lowerRoute, realRoute, scopeRoute, pkgP, pkgN,
          scopePkg⟩
  }
  exact ⟨cert, wUnary, rUnary, realUnary, scopeUnary⟩

end BEDC.Derived.RegularCauchyApartnessBudgetUp
