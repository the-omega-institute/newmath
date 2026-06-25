import BEDC.Derived.RegularCauchyApartnessBudgetUp.TasteGate

namespace BEDC.Derived.RegularCauchyApartnessBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyApartnessBudgetCarrier_cofinal_window_refinement
    [AskSetup] [PackageSetup]
    {X X' A M M' W W' D R E E' H H' C C' P P' N N' realRead reciprocalRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyApartnessBudgetCarrier X A M W D R E H C P N bundle pkg ->
      RegularCauchyApartnessBudgetCarrier X' A M' W' D R E' H' C' P' N' bundle pkg ->
        Cont M W D ->
          Cont M' W' D ->
            Cont D R realRead ->
              Cont R E reciprocalRead ->
                PkgSig bundle reciprocalRead pkg ->
                  UnaryHistory D ∧ UnaryHistory R ∧ UnaryHistory realRead ∧
                    UnaryHistory reciprocalRead ∧ PkgSig bundle N pkg ∧
                      PkgSig bundle N' pkg ∧ PkgSig bundle reciprocalRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory PkgSig
  intro leftCarrier rightCarrier _leftWindow _rightWindow realRoute reciprocalRoute
    reciprocalPkg
  obtain ⟨_xUnary, _aUnary, _mUnary, _wUnary, dUnary, rUnary, eUnary, _hUnary,
    _cUnary, _pUnary, _nUnary, _apartnessModulusWindow, _windowLowerReadback,
    _pkgP, pkgN⟩ := leftCarrier
  obtain ⟨_x'Unary, _a'Unary, _m'Unary, _w'Unary, _d'Unary, _r'Unary, _e'Unary,
    _h'Unary, _c'Unary, _p'Unary, _n'Unary, _apartnessModulusWindow',
    _windowLowerReadback', _pkgP', pkgN'⟩ := rightCarrier
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed dUnary rUnary realRoute
  have reciprocalUnary : UnaryHistory reciprocalRead :=
    unary_cont_closed rUnary eUnary reciprocalRoute
  exact ⟨dUnary, rUnary, realUnary, reciprocalUnary, pkgN, pkgN', reciprocalPkg⟩

end BEDC.Derived.RegularCauchyApartnessBudgetUp
