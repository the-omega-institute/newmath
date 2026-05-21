import BEDC.Derived.CriticalStripZetaZeroWitnessUp

namespace BEDC.Derived.CriticalStripZetaZeroWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CriticalStripZetaZeroWitnessPacket_source_boundary_closure [AskSetup] [PackageSetup]
    {strip zero line boundary transport route provenance name endpoint sourceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CriticalStripZetaZeroWitnessPacket strip zero line boundary transport route provenance name
        endpoint bundle pkg ->
      Cont strip zero sourceRead ->
        Cont sourceRead route endpoint ->
          PkgSig bundle sourceRead pkg ->
            UnaryHistory strip ∧ UnaryHistory zero ∧ UnaryHistory sourceRead ∧
              hsame sourceRead transport ∧ Cont strip zero sourceRead ∧
                Cont strip zero transport ∧ PkgSig bundle endpoint pkg ∧
                  PkgSig bundle sourceRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet sourceRoute sourceEndpoint sourcePkg
  have exhausted :=
    CriticalStripZetaZeroWitnessPacket_source_route_exhaustion
      (strip := strip) (zero := zero) (line := line) (boundary := boundary)
      (transport := transport) (route := route) (provenance := provenance)
      (name := name) (endpoint := endpoint) (sourceRead := sourceRead)
      (bundle := bundle) (pkg := pkg) packet sourceEndpoint
  obtain ⟨sameSourceTransport, sourceUnary, _stripZeroSource, endpointPkg⟩ := exhausted
  obtain ⟨stripUnary, zeroUnary, _lineUnary, _boundaryUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameUnary, _endpointUnary, stripZeroTransport, _lineBoundaryRoute,
    _transportRouteEndpoint, _endpointProvenanceName, _endpointSameTransportRoute,
    _endpointPkg⟩ := packet
  exact
    ⟨stripUnary, zeroUnary, sourceUnary, sameSourceTransport, sourceRoute,
      stripZeroTransport, endpointPkg, sourcePkg⟩

end BEDC.Derived.CriticalStripZetaZeroWitnessUp
