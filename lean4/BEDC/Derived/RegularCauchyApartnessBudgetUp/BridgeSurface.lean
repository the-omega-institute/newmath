import BEDC.Derived.RegularCauchyApartnessBudgetUp.TasteGate

namespace BEDC.Derived.RegularCauchyApartnessBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyApartnessBudgetCarrier_bridge_surface [AskSetup] [PackageSetup]
    {X A M W D R E H C P N bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyApartnessBudgetCarrier X A M W D R E H C P N bundle pkg ->
      Cont D R bridgeRead ->
        PkgSig bundle bridgeRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row A ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨
                  hsame row E ∨ hsame row bridgeRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont W D R ∧ Cont D R bridgeRead ∧
                  PkgSig bundle bridgeRead pkg ∧ PkgSig bundle N pkg)
              hsame ∧ UnaryHistory bridgeRead ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier lowerBridgeRoute bridgePkg
  obtain ⟨_xUnary, _aUnary, _mUnary, _wUnary, dUnary, rUnary, _eUnary, _hUnary,
    _cUnary, _pUnary, _nUnary, _apartnessModulusWindow, windowLowerReadback, _pkgP,
    pkgN⟩ := carrier
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed dUnary rUnary lowerBridgeRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨ hsame row E ∨
              hsame row bridgeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W D R ∧ Cont D R bridgeRead ∧
              PkgSig bundle bridgeRead pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro bridgeRead ⟨hsame_refl bridgeRead, bridgeUnary⟩
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
      exact ⟨source.right, windowLowerReadback, lowerBridgeRoute, bridgePkg, pkgN⟩
  }
  exact ⟨cert, bridgeUnary, pkgN⟩

end BEDC.Derived.RegularCauchyApartnessBudgetUp
