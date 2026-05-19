import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalFiniteRouteReadbackBoundary [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      normalRead routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont typed fuel terminalRead →
        Cont terminalRead normal normalRead →
          Cont normalRead transports routeRead →
            PkgSig bundle routeRead pkg →
              hsame terminalRead terminal ∧ UnaryHistory normalRead ∧
                UnaryHistory routeRead ∧ Cont normalRead transports routeRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle routeRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame PkgSig UnaryHistory
  intro packet typedFuelTerminalRead terminalReadNormalRead normalReadTransportsRouteRead
    routeReadPkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, _continuationUnary,
    transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg,
    provenancePkg⟩ := packet
  have terminalReadSame : hsame terminalRead terminal :=
    cont_deterministic typedFuelTerminalRead typedFuelTerminal
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have normalReadUnary : UnaryHistory normalRead :=
    unary_cont_closed terminalReadUnary normalUnary terminalReadNormalRead
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed normalReadUnary transportsUnary normalReadTransportsRouteRead
  exact
    ⟨terminalReadSame, normalReadUnary, routeReadUnary, normalReadTransportsRouteRead,
      provenancePkg, routeReadPkg⟩

end BEDC.Derived.ZnormalUp
