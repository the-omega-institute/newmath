import BEDC.Derived.RegularCauchyApartnessBudgetUp.TasteGate
import BEDC.Derived.RegularCauchyApartnessBudgetUp.MatureConsumer

namespace BEDC.Derived.RegularCauchyApartnessBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyApartnessBudgetCarrier_window_axis_target [AskSetup] [PackageSetup]
    {X A M W D R E H C P N windowRead lowerRead sealRead formalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyApartnessBudgetCarrier X A M W D R E H C P N bundle pkg →
      Cont M W windowRead →
        Cont windowRead D lowerRead →
          Cont lowerRead E sealRead →
            Cont sealRead N formalRead →
              PkgSig bundle N pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row formalRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row A ∨ hsame row M ∨ hsame row W ∨ hsame row D ∨
                        hsame row R ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨
                          hsame row P ∨ hsame row N ∨ hsame row formalRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont M W windowRead ∧
                        Cont windowRead D lowerRead ∧ Cont lowerRead E sealRead ∧
                          Cont sealRead N formalRead ∧ PkgSig bundle N pkg)
                    hsame ∧
                  UnaryHistory windowRead ∧ UnaryHistory lowerRead ∧
                    UnaryHistory sealRead ∧ UnaryHistory formalRead := by
  -- BEDC touchpoint anchor: RegularCauchyApartnessBudgetCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier windowRoute lowerRoute sealRoute formalRoute formalPkg
  obtain ⟨_xUnary, _aUnary, mUnary, wUnary, dUnary, _rUnary, eUnary, _hUnary,
    _cUnary, _pUnary, nUnary, _apartnessWindow, _windowReadback, _pkgP, _pkgN⟩ :=
    carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed mUnary wUnary windowRoute
  have lowerUnary : UnaryHistory lowerRead :=
    unary_cont_closed windowUnary dUnary lowerRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed lowerUnary eUnary sealRoute
  have formalUnary : UnaryHistory formalRead :=
    unary_cont_closed sealUnary nUnary formalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row formalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row M ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨
              hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row formalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M W windowRead ∧ Cont windowRead D lowerRead ∧
              Cont lowerRead E sealRead ∧ Cont sealRead N formalRead ∧
                PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro formalRead ⟨hsame_refl formalRead, formalUnary⟩
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
      repeat (first | exact source.left | apply Or.inr)
    ledger_sound := by
      intro _row source
      exact ⟨source.right, windowRoute, lowerRoute, sealRoute, formalRoute, formalPkg⟩
  }
  exact ⟨cert, windowUnary, lowerUnary, sealUnary, formalUnary⟩

theorem RegularCauchyApartnessBudgetCarrier_formal_axis_target [AskSetup] [PackageSetup]
    {X A M W D R E H C P N lowerRead sealRead fieldRead reciprocalRead sharedRead
      matureRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyApartnessBudgetCarrier X A M W D R E H C P N bundle pkg →
      Cont D R lowerRead →
        Cont lowerRead E sealRead →
          Cont sealRead C fieldRead →
            Cont W D reciprocalRead →
              Cont fieldRead reciprocalRead sharedRead →
                Cont sharedRead N matureRead →
                  PkgSig bundle matureRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row matureRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row A ∨ hsame row M ∨ hsame row W ∨ hsame row D ∨
                            hsame row R ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨
                              hsame row P ∨ hsame row N ∨ hsame row lowerRead ∨
                                hsame row sealRead ∨ hsame row fieldRead ∨
                                  hsame row reciprocalRead ∨ hsame row sharedRead ∨
                                    hsame row matureRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont D R lowerRead ∧
                            Cont lowerRead E sealRead ∧ Cont sealRead C fieldRead ∧
                              Cont W D reciprocalRead ∧
                                Cont fieldRead reciprocalRead sharedRead ∧
                                  Cont sharedRead N matureRead ∧
                                    PkgSig bundle matureRead pkg)
                        hsame ∧
                      UnaryHistory lowerRead ∧ UnaryHistory sealRead ∧
                        UnaryHistory fieldRead ∧ UnaryHistory reciprocalRead ∧
                          UnaryHistory sharedRead ∧ UnaryHistory matureRead := by
  -- BEDC touchpoint anchor: RegularCauchyApartnessBudgetCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier lowerRoute sealRoute fieldRoute reciprocalRoute sharedRoute matureRoute maturePkg
  obtain ⟨_xUnary, _aUnary, _mUnary, wUnary, dUnary, rUnary, eUnary, _hUnary,
    cUnary, _pUnary, nUnary, _apartnessWindow, _windowReadback, _pkgP, _pkgN⟩ :=
      carrier
  have lowerUnary : UnaryHistory lowerRead :=
    unary_cont_closed dUnary rUnary lowerRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed lowerUnary eUnary sealRoute
  have fieldUnary : UnaryHistory fieldRead :=
    unary_cont_closed sealUnary cUnary fieldRoute
  have reciprocalUnary : UnaryHistory reciprocalRead :=
    unary_cont_closed wUnary dUnary reciprocalRoute
  have sharedUnary : UnaryHistory sharedRead :=
    unary_cont_closed fieldUnary reciprocalUnary sharedRoute
  have matureUnary : UnaryHistory matureRead :=
    unary_cont_closed sharedUnary nUnary matureRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row matureRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row M ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨
              hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row lowerRead ∨ hsame row sealRead ∨ hsame row fieldRead ∨
                  hsame row reciprocalRead ∨ hsame row sharedRead ∨ hsame row matureRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D R lowerRead ∧ Cont lowerRead E sealRead ∧
              Cont sealRead C fieldRead ∧ Cont W D reciprocalRead ∧
                Cont fieldRead reciprocalRead sharedRead ∧ Cont sharedRead N matureRead ∧
                  PkgSig bundle matureRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro matureRead ⟨hsame_refl matureRead, matureUnary⟩
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
      repeat (first | exact source.left | apply Or.inr)
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, lowerRoute, sealRoute, fieldRoute, reciprocalRoute, sharedRoute,
          matureRoute, maturePkg⟩
  }
  exact
    ⟨cert, lowerUnary, sealUnary, fieldUnary, reciprocalUnary, sharedUnary,
      matureUnary⟩

end BEDC.Derived.RegularCauchyApartnessBudgetUp
