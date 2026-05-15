import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_tail_budget_selector_lock [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n selected0 selected1 readback0 readback1 seal0 seal1 :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont t w selected0 ->
        Cont t w selected1 ->
          Cont selected0 q readback0 ->
            Cont selected1 q readback1 ->
              Cont readback0 e seal0 ->
                Cont readback1 e seal1 ->
                  PkgSig bundle seal0 pkg ->
                    PkgSig bundle seal1 pkg ->
                      hsame selected0 selected1 ∧ hsame readback0 readback1 ∧
                        hsame seal0 seal1 ∧ UnaryHistory selected0 ∧
                          UnaryHistory selected1 ∧ UnaryHistory readback0 ∧
                            UnaryHistory readback1 ∧ UnaryHistory seal0 ∧
                              UnaryHistory seal1 ∧ PkgSig bundle seal0 pkg ∧
                                PkgSig bundle seal1 pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame PkgSig
  intro carrier selectedRoute0 selectedRoute1 readbackRoute0 readbackRoute1 sealRoute0
    sealRoute1 sealPkg0 sealPkg1
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, tUnary, wUnary, qUnary, eUnary, _hUnary,
      _cUnary, _pUnary, _nUnary, _m0m1u, _uvt, _twq, _qeh, _pPkg, _hn⟩
  have sameSelected : hsame selected0 selected1 :=
    cont_respects_hsame (hsame_refl t) (hsame_refl w) selectedRoute0 selectedRoute1
  have selectedUnary0 : UnaryHistory selected0 :=
    unary_cont_closed tUnary wUnary selectedRoute0
  have selectedUnary1 : UnaryHistory selected1 :=
    unary_cont_closed tUnary wUnary selectedRoute1
  have sameReadback : hsame readback0 readback1 :=
    cont_respects_hsame sameSelected (hsame_refl q) readbackRoute0 readbackRoute1
  have readbackUnary0 : UnaryHistory readback0 :=
    unary_cont_closed selectedUnary0 qUnary readbackRoute0
  have readbackUnary1 : UnaryHistory readback1 :=
    unary_cont_closed selectedUnary1 qUnary readbackRoute1
  have sameSeal : hsame seal0 seal1 :=
    cont_respects_hsame sameReadback (hsame_refl e) sealRoute0 sealRoute1
  have sealUnary0 : UnaryHistory seal0 :=
    unary_cont_closed readbackUnary0 eUnary sealRoute0
  have sealUnary1 : UnaryHistory seal1 :=
    unary_cont_closed readbackUnary1 eUnary sealRoute1
  exact
    ⟨sameSelected, sameReadback, sameSeal, selectedUnary0, selectedUnary1, readbackUnary0,
      readbackUnary1, sealUnary0, sealUnary1, sealPkg0, sealPkg1⟩

end BEDC.Derived.CauchyModulusRefinementUp
