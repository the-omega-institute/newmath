import BEDC.Derived.CriticalStripZetaZeroWitnessUp

namespace BEDC.Derived.CriticalStripZetaZeroWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CriticalStripZetaZeroWitnessPacket_witness_consumer_boundary
    [AskSetup] [PackageSetup]
    {strip zero line boundary transport route provenance name endpoint consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CriticalStripZetaZeroWitnessPacket strip zero line boundary transport route provenance name
        endpoint bundle pkg ->
      Cont endpoint name consumerRead ->
        PkgSig bundle consumerRead pkg ->
          SemanticNameCert
            (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row ∧
              PkgSig bundle row pkg)
            (fun row : BHist => Cont endpoint name row ∧ Cont line boundary route ∧
              Cont transport route endpoint)
            (fun row : BHist => PkgSig bundle row pkg ∧
              hsame endpoint (append transport route))
            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro packet consumerRoute consumerPkg
  obtain ⟨_stripUnary, _zeroUnary, _lineUnary, _boundaryUnary, _transportUnary, _routeUnary,
    _provenanceUnary, nameUnary, endpointUnary, _stripZeroTransport, lineBoundaryRoute,
    transportRouteEndpoint, _endpointProvenanceName, endpointSameTransportRoute,
    _endpointPkg⟩ := packet
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed endpointUnary nameUnary consumerRoute
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro consumerRead
          ⟨hsame_refl consumerRead, consumerUnary, consumerPkg⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro _row source
      cases source.left
      exact ⟨consumerRoute, lineBoundaryRoute, transportRouteEndpoint⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.right.right, endpointSameTransportRoute⟩
  }

end BEDC.Derived.CriticalStripZetaZeroWitnessUp
