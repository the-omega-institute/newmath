import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCarrier_root_transport_replay [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      transported replay endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      hsame transported readback →
        Cont transported realSeal replay →
          Cont replay cert endpoint →
            PkgSig bundle endpoint pkg →
              UnaryHistory readback ∧ UnaryHistory transported ∧ UnaryHistory realSeal ∧
                UnaryHistory replay ∧ UnaryHistory endpoint ∧ hsame transported readback ∧
                  Cont transported realSeal replay ∧ Cont replay cert endpoint ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont PkgSig UnaryHistory
  intro carrier transportedReadback transportedRealSealReplay replayCertEndpoint endpointPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealUnary, _dyadicUnary, _windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, certUnary,
    _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have transportedUnary : UnaryHistory transported := by
    cases transportedReadback
    exact readbackUnary
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed transportedUnary realSealUnary transportedRealSealReplay
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed replayUnary certUnary replayCertEndpoint
  exact
    ⟨readbackUnary, transportedUnary, realSealUnary, replayUnary, endpointUnary,
      transportedReadback, transportedRealSealReplay, replayCertEndpoint, provenancePkg,
      endpointPkg⟩

theorem DiagonalLimitCompatibility_root_transport_replay_exactness [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      transported replay endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      hsame transported readback →
        Cont transported realSeal replay →
          Cont replay cert endpoint →
            PkgSig bundle endpoint pkg →
              UnaryHistory diagonal ∧ UnaryHistory dyadic ∧ UnaryHistory windows ∧
                UnaryHistory readback ∧ UnaryHistory transported ∧ UnaryHistory replay ∧
                  UnaryHistory endpoint ∧ hsame transported readback ∧
                    Cont dyadic windows readback ∧ Cont transported realSeal replay ∧
                      Cont replay cert endpoint ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont PkgSig UnaryHistory
  intro carrier transportedReadback transportedRealSealReplay replayCertEndpoint endpointPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, certUnary,
    _diagonalTriangleSeal, dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have transportedUnary : UnaryHistory transported := by
    cases transportedReadback
    exact readbackUnary
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed transportedUnary realSealUnary transportedRealSealReplay
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed replayUnary certUnary replayCertEndpoint
  exact
    ⟨diagonalUnary, dyadicUnary, windowsUnary, readbackUnary, transportedUnary, replayUnary,
      endpointUnary, transportedReadback, dyadicWindowsReadback, transportedRealSealReplay,
      replayCertEndpoint, provenancePkg, endpointPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
