import BEDC.Derived.RegularCauchyApartnessBudgetUp.TasteGate

namespace BEDC.Derived.RegularCauchyApartnessBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyApartnessBudgetCarrier_route_rows [AskSetup] [PackageSetup]
    {X A M W D R E H C P N windowRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyApartnessBudgetCarrier X A M W D R E H C P N bundle pkg →
      Cont A M windowRead →
        PkgSig bundle P pkg →
          SemanticNameCert
              (fun row : BHist => hsame row windowRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row A ∨ hsame row M ∨ hsame row W ∨ hsame row D ∨
                  hsame row R ∨ hsame row windowRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont A M windowRead ∧ PkgSig bundle P pkg)
              hsame ∧
            UnaryHistory windowRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier windowRoute packageProof
  obtain ⟨_xUnary, aUnary, mUnary, _wUnary, _dUnary, _rUnary, _eUnary, _hUnary,
    _cUnary, _pUnary, _nUnary, _apartnessModulusWindow, _windowLowerReadback,
    _pkgP, _pkgN⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed aUnary mUnary windowRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row windowRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row M ∨ hsame row W ∨ hsame row D ∨
              hsame row R ∨ hsame row windowRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont A M windowRead ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro windowRead ⟨hsame_refl windowRead, windowUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, windowRoute, packageProof⟩
  }
  exact ⟨cert, windowUnary⟩

end BEDC.Derived.RegularCauchyApartnessBudgetUp
