import BEDC.Derived.CriticalStripZetaZeroWitnessUp

namespace BEDC.Derived.CriticalStripZetaZeroWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CriticalStripZetaZeroWitnessPacket_shared_source_scope [AskSetup] [PackageSetup]
    {strip zero line boundary transport route provenance name endpoint sharedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CriticalStripZetaZeroWitnessPacket strip zero line boundary transport route provenance name
        endpoint bundle pkg →
      Cont strip zero sharedRead →
        hsame endpoint (append transport route) →
          UnaryHistory strip ∧ UnaryHistory zero ∧ UnaryHistory transport ∧
            UnaryHistory route ∧ UnaryHistory sharedRead ∧ Cont strip zero transport ∧
              Cont strip zero sharedRead ∧ hsame endpoint (append transport route) ∧
                PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet sharedRoute endpointSame
  obtain ⟨stripUnary, zeroUnary, _lineUnary, _boundaryUnary, transportUnary, routeUnary,
    _provenanceUnary, _nameUnary, _endpointUnary, stripZeroTransport, _lineBoundaryRoute,
    _transportRouteEndpoint, _endpointProvenanceName, _storedEndpointSame, endpointPkg⟩ :=
    packet
  have sharedUnary : UnaryHistory sharedRead :=
    unary_cont_closed stripUnary zeroUnary sharedRoute
  exact
    ⟨stripUnary, zeroUnary, transportUnary, routeUnary, sharedUnary, stripZeroTransport,
      sharedRoute, endpointSame, endpointPkg⟩

end BEDC.Derived.CriticalStripZetaZeroWitnessUp
