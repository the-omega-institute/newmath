import BEDC.Derived.RegularCauchyApartnessBudgetUp.TasteGate

namespace BEDC.Derived.RegularCauchyApartnessBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyApartnessBudgetCarrier_public_interface [AskSetup] [PackageSetup]
    {X A M W D R E H C P N sealRead nameRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyApartnessBudgetCarrier X A M W D R E H C P N bundle pkg →
      Cont R E sealRead →
        Cont sealRead H C →
          Cont C P nameRead →
            SemanticNameCert
                (fun row : BHist => hsame row nameRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row A ∨ hsame row M ∨ hsame row W ∨ hsame row D ∨
                    hsame row R ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨
                      hsame row P ∨ hsame row N ∨ hsame row sealRead ∨
                        hsame row nameRead)
                (fun row : BHist =>
                  hsame row nameRead ∧ Cont R E sealRead ∧ Cont sealRead H C ∧
                    Cont C P nameRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                hsame ∧
              UnaryHistory sealRead ∧ UnaryHistory nameRead ∧ PkgSig bundle P pkg ∧
                PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory PkgSig
  intro carrier sealRoute structureRoute nameRoute
  obtain ⟨_xUnary, _aUnary, _mUnary, _wUnary, _dUnary, rUnary, eUnary, _hUnary,
    cUnary, pUnary, _nUnary, _apartnessModulusWindow, _windowLowerReadback, pkgP,
    pkgN⟩ := carrier
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed rUnary eUnary sealRoute
  have nameUnary : UnaryHistory nameRead :=
    unary_cont_closed cUnary pUnary nameRoute
  have sourceAtName :
      (fun row : BHist => hsame row nameRead ∧ UnaryHistory row) nameRead :=
    ⟨hsame_refl nameRead, nameUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row nameRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row M ∨ hsame row W ∨ hsame row D ∨
              hsame row R ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row N ∨ hsame row sealRead ∨ hsame row nameRead)
          (fun row : BHist =>
            hsame row nameRead ∧ Cont R E sealRead ∧ Cont sealRead H C ∧
              Cont C P nameRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro nameRead sourceAtName
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
                          (Or.inr (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, sealRoute, structureRoute, nameRoute, pkgP, pkgN⟩
  }
  exact ⟨cert, sealUnary, nameUnary, pkgP, pkgN⟩

end BEDC.Derived.RegularCauchyApartnessBudgetUp
