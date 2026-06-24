import BEDC.Derived.RegularCauchyApartnessBudgetUp.TasteGate

namespace BEDC.Derived.RegularCauchyApartnessBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyApartnessBudgetCarrier_field_handoff [AskSetup] [PackageSetup]
    {X A M W D R E H C P N lowerRead sealRead fieldRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyApartnessBudgetCarrier X A M W D R E H C P N bundle pkg ->
      Cont D R lowerRead ->
        Cont lowerRead E sealRead ->
          Cont sealRead C fieldRead ->
            PkgSig bundle fieldRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row fieldRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row A ∨ hsame row D ∨ hsame row R ∨ hsame row E ∨
                      hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                        hsame row lowerRead ∨ hsame row sealRead ∨
                          hsame row fieldRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont D R lowerRead ∧
                      Cont lowerRead E sealRead ∧ Cont sealRead C fieldRead ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
                          PkgSig bundle fieldRead pkg)
                  hsame ∧
                UnaryHistory lowerRead ∧ UnaryHistory sealRead ∧
                  UnaryHistory fieldRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier lowerRoute sealRoute fieldRoute fieldPkg
  obtain ⟨_xUnary, _aUnary, _mUnary, _wUnary, dUnary, rUnary, eUnary, _hUnary,
    cUnary, _pUnary, _nUnary, _apartnessModulusWindow, _windowLowerReadback, pkgP,
    pkgN⟩ := carrier
  have lowerUnary : UnaryHistory lowerRead :=
    unary_cont_closed dUnary rUnary lowerRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed lowerUnary eUnary sealRoute
  have fieldUnary : UnaryHistory fieldRead :=
    unary_cont_closed sealUnary cUnary fieldRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row fieldRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row D ∨ hsame row R ∨ hsame row E ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row lowerRead ∨ hsame row sealRead ∨ hsame row fieldRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D R lowerRead ∧ Cont lowerRead E sealRead ∧
              Cont sealRead C fieldRead ∧ PkgSig bundle P pkg ∧
                PkgSig bundle N pkg ∧ PkgSig bundle fieldRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro fieldRead ⟨hsame_refl fieldRead, fieldUnary⟩
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
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, lowerRoute, sealRoute, fieldRoute, pkgP, pkgN, fieldPkg⟩
  }
  exact ⟨cert, lowerUnary, sealUnary, fieldUnary⟩

end BEDC.Derived.RegularCauchyApartnessBudgetUp
