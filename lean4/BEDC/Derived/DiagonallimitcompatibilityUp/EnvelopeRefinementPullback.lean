import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCarrier_envelope_refinement_pullback [AskSetup]
    [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      terminal envelopeRoute refinementRoute pullback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont readback realSeal terminal ->
        Cont terminal route envelopeRoute ->
          Cont terminal transport refinementRoute ->
            Cont envelopeRoute refinementRoute pullback ->
              PkgSig bundle pullback pkg ->
                UnaryHistory terminal ∧ UnaryHistory envelopeRoute ∧
                  UnaryHistory refinementRoute ∧ UnaryHistory pullback ∧
                    Cont readback realSeal terminal ∧ Cont terminal route envelopeRoute ∧
                      Cont terminal transport refinementRoute ∧
                        Cont envelopeRoute refinementRoute pullback ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle pullback pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory DiagonalLimitCompatibilityCarrier
  intro carrier readbackRealSealTerminal terminalRouteEnvelope terminalTransportRefinement
    envelopeRefinementPullback pullbackPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealRowUnary, _dyadicUnary, _windowsUnary,
    readbackUnary, realSealUnary, transportUnary, routeUnary, _provenanceUnary, _certUnary,
    _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed readbackUnary realSealUnary readbackRealSealTerminal
  have envelopeUnary : UnaryHistory envelopeRoute :=
    unary_cont_closed terminalUnary routeUnary terminalRouteEnvelope
  have refinementUnary : UnaryHistory refinementRoute :=
    unary_cont_closed terminalUnary transportUnary terminalTransportRefinement
  have pullbackUnary : UnaryHistory pullback :=
    unary_cont_closed envelopeUnary refinementUnary envelopeRefinementPullback
  exact
    ⟨terminalUnary, envelopeUnary, refinementUnary, pullbackUnary, readbackRealSealTerminal,
      terminalRouteEnvelope, terminalTransportRefinement, envelopeRefinementPullback,
      provenancePkg, pullbackPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
