import BEDC.Derived.DiagonalCofinalTailUp

namespace BEDC.Derived.DiagonalCofinalTailUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalCofinalTailCarrier_regseqrat_streamname_handoff [AskSetup]
    [PackageSetup]
    {q s g d r w h c p n streamRead dyadicRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalCofinalTailCarrier q s g d r w h c p n bundle pkg →
      Cont s g streamRead →
        Cont streamRead d dyadicRead →
          Cont dyadicRead r realRead →
            PkgSig bundle realRead pkg →
              UnaryHistory s ∧ UnaryHistory g ∧ UnaryHistory d ∧ UnaryHistory r ∧
                UnaryHistory streamRead ∧ UnaryHistory dyadicRead ∧
                  UnaryHistory realRead ∧ Cont s g streamRead ∧
                    Cont streamRead d dyadicRead ∧ Cont dyadicRead r realRead ∧
                      PkgSig bundle p pkg ∧ PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro carrier streamRoute dyadicRoute realRoute realPkg
  obtain ⟨_qUnary, sUnary, gUnary, dUnary, rUnary, _wUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, _qsRoute, _gdRoute, _whRoute, pPkg⟩ := carrier
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed sUnary gUnary streamRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed streamUnary dUnary dyadicRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed dyadicUnary rUnary realRoute
  exact
    ⟨sUnary, gUnary, dUnary, rUnary, streamUnary, dyadicUnary, realUnary,
      streamRoute, dyadicRoute, realRoute, pPkg, realPkg⟩

end BEDC.Derived.DiagonalCofinalTailUp
