import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_terminal_route_component_totality [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      continuationRead routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont typed fuel terminalRead →
        Cont terminalRead normal continuationRead →
          Cont continuationRead transports routeRead →
            PkgSig bundle routeRead pkg →
              hsame terminalRead terminal ∧ UnaryHistory terminalRead ∧
                UnaryHistory continuationRead ∧ UnaryHistory routeRead ∧
                  Cont typed fuel terminalRead ∧ Cont terminalRead normal continuationRead ∧
                    Cont continuationRead transports routeRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle routeRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory PkgSig
  intro packet typedFuelTerminalRead terminalReadNormalContinuationRead
    continuationReadTransportsRoute routePkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, _continuationUnary,
    transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have terminalReadSame : hsame terminalRead terminal :=
    cont_deterministic typedFuelTerminalRead typedFuelTerminal
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have continuationReadUnary : UnaryHistory continuationRead :=
    unary_cont_closed terminalReadUnary normalUnary terminalReadNormalContinuationRead
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed continuationReadUnary transportsUnary continuationReadTransportsRoute
  exact
    ⟨terminalReadSame, terminalReadUnary, continuationReadUnary, routeReadUnary,
      typedFuelTerminalRead, terminalReadNormalContinuationRead,
      continuationReadTransportsRoute, provenancePkg, routePkg⟩

end BEDC.Derived.ZnormalUp
