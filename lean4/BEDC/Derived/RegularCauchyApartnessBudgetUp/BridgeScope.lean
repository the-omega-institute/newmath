import BEDC.Derived.RegularCauchyApartnessBudgetUp.TasteGate

namespace BEDC.Derived.RegularCauchyApartnessBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyApartnessBudgetCarrier_bridge_scope [AskSetup] [PackageSetup]
    {X A M W D R E H C P N bridgeRead sealRead nameRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyApartnessBudgetCarrier X A M W D R E H C P N bundle pkg ->
      Cont A W bridgeRead ->
        Cont bridgeRead R sealRead ->
          Cont sealRead E nameRead ->
            SemanticNameCert
              (fun row : BHist => hsame row nameRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row X ∨ hsame row A ∨ hsame row M ∨ hsame row W ∨
                  hsame row D ∨ hsame row R ∨ hsame row E ∨ hsame row H ∨
                    hsame row C ∨ hsame row P ∨ hsame row N ∨
                      hsame row bridgeRead ∨ hsame row sealRead ∨ hsame row nameRead)
              (fun row : BHist =>
                hsame row nameRead ∧ Cont A W bridgeRead ∧
                  Cont bridgeRead R sealRead ∧ Cont sealRead E nameRead ∧
                    PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
              hsame ∧ UnaryHistory bridgeRead ∧ UnaryHistory sealRead ∧
                UnaryHistory nameRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier bridgeRoute sealRoute nameRoute
  obtain ⟨_xUnary, aUnary, _mUnary, wUnary, _dUnary, rUnary, eUnary, _hUnary,
    _cUnary, _pUnary, _nUnary, _budgetRoute, _lowerRoute, pkgP, pkgN⟩ := carrier
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed aUnary wUnary bridgeRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed bridgeUnary rUnary sealRoute
  have nameUnary : UnaryHistory nameRead :=
    unary_cont_closed sealUnary eUnary nameRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row nameRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row X ∨ hsame row A ∨ hsame row M ∨ hsame row W ∨
            hsame row D ∨ hsame row R ∨ hsame row E ∨ hsame row H ∨
              hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row bridgeRead ∨
                hsame row sealRead ∨ hsame row nameRead)
        (fun row : BHist =>
          hsame row nameRead ∧ Cont A W bridgeRead ∧
            Cont bridgeRead R sealRead ∧ Cont sealRead E nameRead ∧
              PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro nameRead ⟨hsame_refl nameRead, nameUnary⟩
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
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr source.left))))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, bridgeRoute, sealRoute, nameRoute, pkgP, pkgN⟩
  }
  exact ⟨cert, bridgeUnary, sealUnary, nameUnary⟩

end BEDC.Derived.RegularCauchyApartnessBudgetUp
