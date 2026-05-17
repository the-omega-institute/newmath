import BEDC.Derived.AxisZeckendorfCannotClaimUp

namespace BEDC.Derived.AxisZeckendorfCannotClaimUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem AxisZeckendorfCannotClaimRegistryPacket_refusal_row_determinacy [AskSetup]
    [PackageSetup] {a b c d e f g h h' p n p' n' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg ->
      AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h' p' n' bundle pkg ->
        hsame h h' := by
  intro left right
  obtain
    ⟨_aUnary, _bUnary, _cUnary, _dUnary, _eUnary, _fUnary, _gUnary, routeAB,
      _routeCD, _routeEF, _pUnary, _sameProvenanceName, _pkgSig⟩ := left
  obtain
    ⟨_aUnary', _bUnary', _cUnary', _dUnary', _eUnary', _fUnary', _gUnary',
      routeAB', _routeCD', _routeEF', _pUnary', _sameProvenanceName', _pkgSig'⟩ :=
        right
  exact cont_deterministic routeAB routeAB'

end BEDC.Derived.AxisZeckendorfCannotClaimUp
