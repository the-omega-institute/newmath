import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_window_tolerance_exactness [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n selected tolerance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont t w selected ->
        Cont selected e tolerance ->
          PkgSig bundle tolerance pkg ->
            UnaryHistory t ∧ UnaryHistory w ∧ UnaryHistory selected ∧
              UnaryHistory tolerance ∧ Cont u v t ∧ Cont t w selected ∧
                Cont selected e tolerance ∧ hsame q selected ∧ PkgSig bundle p pkg ∧
                  PkgSig bundle tolerance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier selectedRoute toleranceRoute tolerancePkg
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, tUnary, wUnary, _qUnary, eUnary, _hUnary,
      _cUnary, _pUnary, _nUnary, _m0m1u, uvt, carrierWindow, _qeh, pPkg, _hn⟩
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed tUnary wUnary selectedRoute
  have toleranceUnary : UnaryHistory tolerance :=
    unary_cont_closed selectedUnary eUnary toleranceRoute
  have sameSelected : hsame q selected :=
    cont_respects_hsame (hsame_refl t) (hsame_refl w) carrierWindow selectedRoute
  exact
    ⟨tUnary, wUnary, selectedUnary, toleranceUnary, uvt, selectedRoute, toleranceRoute,
      sameSelected, pPkg, tolerancePkg⟩

end BEDC.Derived.CauchyModulusRefinementUp
