import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ZnormalTerminalReadbackRouteCarrier [AskSetup] [PackageSetup]
    (typed fuel terminal normal continuation transports routes provenance name terminalRead : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig
  ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
      bundle pkg ∧
    Cont terminal continuation terminalRead ∧ PkgSig bundle terminalRead pkg

theorem ZnormalTerminalReadbackRouteCarrier_package [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalTerminalReadbackRouteCarrier typed fuel terminal normal continuation transports routes
        provenance name terminalRead bundle pkg →
      UnaryHistory terminalRead ∧ Cont terminal continuation terminalRead ∧
        PkgSig bundle provenance pkg ∧ PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro routeCarrier
  obtain ⟨packet, terminalContinuationTerminalRead, terminalReadPkg⟩ := routeCarrier
  obtain ⟨_typedUnary, _fuelUnary, terminalUnary, _normalUnary, continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed terminalUnary continuationUnary terminalContinuationTerminalRead
  exact
    ⟨terminalReadUnary, terminalContinuationTerminalRead, provenancePkg, terminalReadPkg⟩

end BEDC.Derived.ZnormalUp
