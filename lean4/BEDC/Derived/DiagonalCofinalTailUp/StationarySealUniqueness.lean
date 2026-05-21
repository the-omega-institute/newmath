import BEDC.Derived.DiagonalCofinalTailUp

namespace BEDC.Derived.DiagonalCofinalTailUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalCofinalTailCarrier_stationary_seal_uniqueness [AskSetup] [PackageSetup]
    {q s g d r w h c p n _r2 w2 realRead realRead2 : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalCofinalTailCarrier q s g d r w h c p n bundle pkg ->
      hsame w w2 ->
        Cont r w realRead ->
          Cont r w2 realRead2 ->
            PkgSig bundle realRead pkg ->
              PkgSig bundle realRead2 pkg ->
                hsame realRead realRead2 ∧ UnaryHistory realRead ∧
                  UnaryHistory realRead2 ∧ PkgSig bundle p pkg ∧
                    PkgSig bundle realRead pkg ∧ PkgSig bundle realRead2 pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro carrier sameSeal leftRoute rightRoute leftPkg rightPkg
  obtain ⟨_qUnary, _sUnary, _gUnary, _dUnary, rUnary, wUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, _qsRoute, _gdRoute, _whRoute, pPkg⟩ := carrier
  have w2Unary : UnaryHistory w2 :=
    unary_transport wUnary sameSeal
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed rUnary wUnary leftRoute
  have realUnary2 : UnaryHistory realRead2 :=
    unary_cont_closed rUnary w2Unary rightRoute
  have sameReal : hsame realRead realRead2 :=
    cont_respects_hsame (hsame_refl r) sameSeal leftRoute rightRoute
  exact ⟨sameReal, realUnary, realUnary2, pPkg, leftPkg, rightPkg⟩

end BEDC.Derived.DiagonalCofinalTailUp
