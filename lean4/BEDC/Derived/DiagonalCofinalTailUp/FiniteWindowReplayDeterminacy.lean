import BEDC.Derived.DiagonalCofinalTailUp

namespace BEDC.Derived.DiagonalCofinalTailUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalCofinalTailCarrier_finite_window_replay_determinacy [AskSetup]
    [PackageSetup]
    {q s g d r r' w h c p n h' c' p' n' leftRead rightRead replay : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalCofinalTailCarrier q s g d r w h c p n bundle pkg →
      DiagonalCofinalTailCarrier q s g d r' w h' c' p' n' bundle pkg →
        hsame r r' →
          Cont c r leftRead →
            Cont c' r' rightRead →
              Cont leftRead rightRead replay →
                PkgSig bundle replay pkg →
                  UnaryHistory leftRead ∧ UnaryHistory rightRead ∧
                    UnaryHistory replay ∧ hsame r r' ∧ Cont c r leftRead ∧
                      Cont c' r' rightRead ∧ Cont leftRead rightRead replay ∧
                        PkgSig bundle p pkg ∧ PkgSig bundle p' pkg ∧
                          PkgSig bundle replay pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory hsame
  intro leftCarrier rightCarrier sameR leftRoute rightRoute replayRoute replayPkg
  obtain ⟨_qUnary, _sUnary, _gUnary, _dUnary, rUnary, _wUnary, _hUnary, cUnary,
    _pUnary, _nUnary, _qsRoute, _gdRoute, _whRoute, pPkg⟩ := leftCarrier
  obtain ⟨_qUnary', _sUnary', _gUnary', _dUnary', rUnary', _wUnary', _hUnary',
    cUnary', _pUnary', _nUnary', _qsRoute', _gdRoute', _whRoute', pPkg'⟩ :=
    rightCarrier
  have leftUnary : UnaryHistory leftRead :=
    unary_cont_closed cUnary rUnary leftRoute
  have rightUnary : UnaryHistory rightRead :=
    unary_cont_closed cUnary' rUnary' rightRoute
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed leftUnary rightUnary replayRoute
  exact
    ⟨leftUnary, rightUnary, replayUnary, sameR, leftRoute, rightRoute, replayRoute,
      pPkg, pPkg', replayPkg⟩

end BEDC.Derived.DiagonalCofinalTailUp
