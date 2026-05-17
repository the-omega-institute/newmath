import BEDC.Derived.AxisZeckendorfCannotClaimUp

namespace BEDC.Derived.AxisZeckendorfCannotClaimUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AxisZeckendorfCannotClaimRegistryPacket_consumer_horizon_exhaustion [AskSetup]
    [PackageSetup] {a b c d e f g h p n downstream : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg ->
      Cont h p downstream ->
        PkgSig bundle downstream pkg ->
          UnaryHistory downstream ∧ Cont h p downstream ∧ hsame p n ∧
            PkgSig bundle p pkg ∧ PkgSig bundle downstream pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig hsame
  intro packet downstreamRoute downstreamPkg
  obtain
    ⟨aUnary, bUnary, _cUnary, _dUnary, _eUnary, _fUnary, _gUnary, sourceRoute,
      _routeCD, _routeEF, pUnary, sameProvenanceName, provenancePkg⟩ := packet
  have hUnary : UnaryHistory h :=
    unary_cont_closed aUnary bUnary sourceRoute
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed hUnary pUnary downstreamRoute
  exact
    ⟨downstreamUnary, downstreamRoute, sameProvenanceName, provenancePkg, downstreamPkg⟩

end BEDC.Derived.AxisZeckendorfCannotClaimUp
