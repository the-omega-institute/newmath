import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacketDownstreamNormalRouteExhaustion [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name handoff
      terminalRead normalRead routeRead structuralRead packageRead localNameRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg ->
      Cont typed fuel terminalRead ->
        Cont terminalRead terminal normalRead ->
          Cont normalRead normal routeRead ->
            Cont routeRead continuation structuralRead ->
              Cont structuralRead provenance packageRead ->
                Cont packageRead name localNameRead ->
                  UnaryHistory terminalRead ∧ UnaryHistory normalRead ∧
                    UnaryHistory routeRead ∧ UnaryHistory structuralRead ∧
                      UnaryHistory packageRead ∧ UnaryHistory localNameRead ∧
                        PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro packet terminalReadRoute normalReadRoute routeReadRoute structuralReadRoute
    packageReadRoute localNameReadRoute
  obtain ⟨typedUnary, fuelUnary, terminalUnary, normalUnary, continuationUnary,
    _transportsUnary, _routesUnary, provenanceUnary, nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, namePkg, provenancePkg⟩ :=
    packet
  have _handoffRow : BHist := handoff
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary terminalReadRoute
  have normalReadUnary : UnaryHistory normalRead :=
    unary_cont_closed terminalReadUnary terminalUnary normalReadRoute
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed normalReadUnary normalUnary routeReadRoute
  have structuralReadUnary : UnaryHistory structuralRead :=
    unary_cont_closed routeReadUnary continuationUnary structuralReadRoute
  have packageReadUnary : UnaryHistory packageRead :=
    unary_cont_closed structuralReadUnary provenanceUnary packageReadRoute
  have localNameReadUnary : UnaryHistory localNameRead :=
    unary_cont_closed packageReadUnary nameUnary localNameReadRoute
  exact
    ⟨terminalReadUnary, normalReadUnary, routeReadUnary, structuralReadUnary,
      packageReadUnary, localNameReadUnary, namePkg, provenancePkg⟩

end BEDC.Derived.ZnormalUp
