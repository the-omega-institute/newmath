import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalRouteTransport [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      normalRead routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg ->
      Cont typed fuel terminalRead ->
        Cont terminalRead normal normalRead ->
          Cont normalRead continuation routeRead ->
            PkgSig bundle routeRead pkg ->
              hsame terminalRead terminal ∧ UnaryHistory terminalRead ∧
                UnaryHistory normalRead ∧ UnaryHistory routeRead ∧
                  Cont terminalRead normal normalRead ∧
                    Cont normalRead continuation routeRead ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle routeRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro packet typedFuelTerminalRead terminalReadNormal normalReadContinuation routePkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have sameTerminal : hsame terminalRead terminal :=
    cont_deterministic typedFuelTerminalRead typedFuelTerminal
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have normalReadUnary : UnaryHistory normalRead :=
    unary_cont_closed terminalReadUnary normalUnary terminalReadNormal
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed normalReadUnary continuationUnary normalReadContinuation
  exact
    ⟨sameTerminal, terminalReadUnary, normalReadUnary, routeReadUnary, terminalReadNormal,
      normalReadContinuation, provenancePkg, routePkg⟩

end BEDC.Derived.ZnormalUp
