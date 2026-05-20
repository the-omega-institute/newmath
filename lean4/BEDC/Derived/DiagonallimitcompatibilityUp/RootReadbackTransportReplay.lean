import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCarrier_root_readback_transport_replay [AskSetup]
    [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      rootReplay replayRead endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont transport route rootReplay ->
        Cont rootReplay readback replayRead ->
          Cont replayRead realSeal endpoint ->
            PkgSig bundle endpoint pkg ->
              UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory readback ∧
                UnaryHistory realSeal ∧ UnaryHistory rootReplay ∧ UnaryHistory replayRead ∧
                  UnaryHistory endpoint ∧ Cont transport route rootReplay ∧
                    Cont rootReplay readback replayRead ∧ Cont replayRead realSeal endpoint ∧
                      Cont route cert transport ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier rootReplayRoute replayReadRoute endpointRoute endpointPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealUnary, _dyadicUnary, _windowsUnary,
    readbackUnary, realSealUnary, transportUnary, routeUnary, _provenanceUnary, _certUnary,
    _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    routeCertTransport, provenancePkg⟩ := carrier
  have rootReplayUnary : UnaryHistory rootReplay :=
    unary_cont_closed transportUnary routeUnary rootReplayRoute
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed rootReplayUnary readbackUnary replayReadRoute
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed replayReadUnary realSealUnary endpointRoute
  exact
    ⟨transportUnary, routeUnary, readbackUnary, realSealUnary, rootReplayUnary,
      replayReadUnary, endpointUnary, rootReplayRoute, replayReadRoute, endpointRoute,
      routeCertTransport, provenancePkg, endpointPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
