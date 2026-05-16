import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityUniformCauchyThreeWayTerminalComparison
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      envelope refinement uniform endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont readback realSeal endpoint ->
        UnaryHistory envelope ->
          Cont endpoint envelope refinement ->
            Cont endpoint refinement uniform ->
              PkgSig bundle uniform pkg ->
                UnaryHistory diagonal ∧ UnaryHistory dyadic ∧ UnaryHistory windows ∧
                  UnaryHistory readback ∧ UnaryHistory realSeal ∧ UnaryHistory endpoint ∧
                    UnaryHistory envelope ∧ UnaryHistory refinement ∧ UnaryHistory uniform ∧
                      Cont readback realSeal endpoint ∧ Cont endpoint envelope refinement ∧
                        Cont endpoint refinement uniform ∧ PkgSig bundle provenance pkg ∧
                          PkgSig bundle uniform pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier readbackRealSealEndpoint envelopeUnary endpointEnvelopeRefinement
    endpointRefinementUniform uniformPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed readbackUnary realSealUnary readbackRealSealEndpoint
  have refinementUnary : UnaryHistory refinement :=
    unary_cont_closed endpointUnary envelopeUnary endpointEnvelopeRefinement
  have uniformUnary : UnaryHistory uniform :=
    unary_cont_closed endpointUnary refinementUnary endpointRefinementUniform
  exact
    ⟨diagonalUnary, dyadicUnary, windowsUnary, readbackUnary, realSealUnary, endpointUnary,
      envelopeUnary, refinementUnary, uniformUnary, readbackRealSealEndpoint,
      endpointEnvelopeRefinement, endpointRefinementUniform, provenancePkg, uniformPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
