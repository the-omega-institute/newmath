import BEDC.Derived.DiagonalCofinalTailUp
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.DiagonalCofinalTailUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalCofinalTailCarrier_tastegate_hidden_input_refusal
    [AskSetup] [PackageSetup]
    {q s g d r w h c p n consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalCofinalTailCarrier q s g d r w h c p n bundle pkg ->
      Cont c r consumer ->
        Cont consumer (BHist.e0 q) c ->
          False := by
  -- BEDC touchpoint anchor: BHist Cont
  intro carrier consumerRoute hiddenReturn
  obtain ⟨_qUnary, _sUnary, _gUnary, _dUnary, _rUnary, _wUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, _qsRoute, _gdRoute, _whRoute, _pPkg⟩ := carrier
  exact cont_mutual_extension_right_tail_absurd.left consumerRoute hiddenReturn

end BEDC.Derived.DiagonalCofinalTailUp
