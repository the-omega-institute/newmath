import BEDC.Derived.DiagonalCofinalTailUp

namespace BEDC.Derived.DiagonalCofinalTailUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalCofinalTailCarrier_window_exhaustion [AskSetup] [PackageSetup]
    {q s g d r w h c p n observation : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalCofinalTailCarrier q s g d r w h c p n bundle pkg ->
      Cont g d observation ->
        PkgSig bundle observation pkg ->
          UnaryHistory q ∧ UnaryHistory s ∧ UnaryHistory g ∧ UnaryHistory d ∧
            UnaryHistory observation ∧ Cont q s g ∧ Cont g d observation ∧
              PkgSig bundle p pkg ∧ PkgSig bundle observation pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro carrier observationRoute observationPkg
  obtain ⟨qUnary, sUnary, gUnary, dUnary, _rUnary, _wUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, qsRoute, _gdRoute, _whRoute, pPkg⟩ := carrier
  have observationUnary : UnaryHistory observation :=
    unary_cont_closed gUnary dUnary observationRoute
  exact
    ⟨qUnary, sUnary, gUnary, dUnary, observationUnary, qsRoute, observationRoute, pPkg,
      observationPkg⟩

end BEDC.Derived.DiagonalCofinalTailUp
