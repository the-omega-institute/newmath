import BEDC.Derived.RegularCauchyApartnessBudgetUp.TasteGate

namespace BEDC.Derived.RegularCauchyApartnessBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyApartnessBudgetInverseWindowConsumption [AskSetup] [PackageSetup]
    {X A M W D R E H C P N lowerRead reciprocalRead fieldRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyApartnessBudgetCarrier X A M W D R E H C P N bundle pkg →
      Cont A M lowerRead →
        Cont W D reciprocalRead →
          Cont lowerRead reciprocalRead fieldRead →
            PkgSig bundle fieldRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row fieldRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row A ∨ hsame row M ∨ hsame row W ∨ hsame row D ∨
                      hsame row R ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨
                        hsame row P ∨ hsame row N ∨ hsame row fieldRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont A M lowerRead ∧ Cont W D reciprocalRead ∧
                      Cont lowerRead reciprocalRead fieldRead ∧
                        PkgSig bundle fieldRead pkg)
                  hsame ∧
                UnaryHistory lowerRead ∧ UnaryHistory reciprocalRead ∧
                  UnaryHistory fieldRead := by
  -- BEDC touchpoint anchor: RegularCauchyApartnessBudgetCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier lowerRoute reciprocalRoute fieldRoute fieldPkg
  obtain ⟨_xUnary, aUnary, mUnary, wUnary, dUnary, _rUnary, _eUnary, _hUnary,
    _cUnary, _pUnary, _nUnary, _apartnessWindow, _windowReadback, _pkgP, _pkgN⟩ :=
      carrier
  have lowerUnary : UnaryHistory lowerRead :=
    unary_cont_closed aUnary mUnary lowerRoute
  have reciprocalUnary : UnaryHistory reciprocalRead :=
    unary_cont_closed wUnary dUnary reciprocalRoute
  have fieldUnary : UnaryHistory fieldRead :=
    unary_cont_closed lowerUnary reciprocalUnary fieldRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row fieldRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row M ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨
              hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row fieldRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont A M lowerRead ∧ Cont W D reciprocalRead ∧
              Cont lowerRead reciprocalRead fieldRead ∧ PkgSig bundle fieldRead pkg)
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
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, lowerRoute, reciprocalRoute, fieldRoute, fieldPkg⟩
  }
  exact ⟨cert, lowerUnary, reciprocalUnary, fieldUnary⟩

theorem RegularCauchyApartnessBudgetCarrier_inverse_window_consumption
    [AskSetup] [PackageSetup]
    {X A M W D R E H C P N lowerRead reciprocalRead cofinalRead inverseRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyApartnessBudgetCarrier X A M W D R E H C P N bundle pkg ->
      Cont W D lowerRead ->
        Cont lowerRead R reciprocalRead ->
          Cont reciprocalRead E cofinalRead ->
            Cont cofinalRead C inverseRead ->
              PkgSig bundle inverseRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row inverseRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row A ∨ hsame row D ∨ hsame row R ∨ hsame row E ∨
                        hsame row reciprocalRead ∨ hsame row cofinalRead ∨
                          hsame row inverseRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont W D lowerRead ∧
                        Cont lowerRead R reciprocalRead ∧
                          Cont reciprocalRead E cofinalRead ∧
                            Cont cofinalRead C inverseRead ∧
                              PkgSig bundle inverseRead pkg ∧
                                PkgSig bundle N pkg)
                    hsame ∧
                  UnaryHistory lowerRead ∧ UnaryHistory reciprocalRead ∧
                    UnaryHistory cofinalRead ∧ UnaryHistory inverseRead ∧
                      PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier lowerRoute reciprocalRoute cofinalRoute inverseRoute inversePkg
  obtain ⟨_xUnary, _aUnary, _mUnary, wUnary, dUnary, rUnary, eUnary, _hUnary,
    cUnary, _pUnary, _nUnary, _apartnessModulusWindow, _windowLowerReadback,
    _pkgP, pkgN⟩ := carrier
  have lowerUnary : UnaryHistory lowerRead :=
    unary_cont_closed wUnary dUnary lowerRoute
  have reciprocalUnary : UnaryHistory reciprocalRead :=
    unary_cont_closed lowerUnary rUnary reciprocalRoute
  have cofinalUnary : UnaryHistory cofinalRead :=
    unary_cont_closed reciprocalUnary eUnary cofinalRoute
  have inverseUnary : UnaryHistory inverseRead :=
    unary_cont_closed cofinalUnary cUnary inverseRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row inverseRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row D ∨ hsame row R ∨ hsame row E ∨
              hsame row reciprocalRead ∨ hsame row cofinalRead ∨
                hsame row inverseRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W D lowerRead ∧
              Cont lowerRead R reciprocalRead ∧ Cont reciprocalRead E cofinalRead ∧
                Cont cofinalRead C inverseRead ∧ PkgSig bundle inverseRead pkg ∧
                  PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro inverseRead ⟨hsame_refl inverseRead, inverseUnary⟩
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
                  (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, lowerRoute, reciprocalRoute, cofinalRoute, inverseRoute,
          inversePkg, pkgN⟩
  }
  exact
    ⟨cert, lowerUnary, reciprocalUnary, cofinalUnary, inverseUnary, pkgN⟩

end BEDC.Derived.RegularCauchyApartnessBudgetUp
