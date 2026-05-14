import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityRootConsumerCoverage [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      rootReadback replayedRoot consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal dyadic rootReadback ->
        Cont rootReadback windows replayedRoot ->
          Cont replayedRoot readback consumer ->
            PkgSig bundle consumer pkg ->
              UnaryHistory rootReadback ∧ UnaryHistory replayedRoot ∧ UnaryHistory consumer ∧
                Cont diagonal dyadic rootReadback ∧ Cont rootReadback windows replayedRoot ∧
                  Cont replayedRoot readback consumer ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle UnaryHistory
  intro carrier diagonalDyadicRoot rootWindowsReplay replayReadbackConsumer consumerPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealUnary, dyadicUnary, windowsUnary,
    readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have rootUnary : UnaryHistory rootReadback :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicRoot
  have replayUnary : UnaryHistory replayedRoot :=
    unary_cont_closed rootUnary windowsUnary rootWindowsReplay
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed replayUnary readbackUnary replayReadbackConsumer
  exact
    ⟨rootUnary, replayUnary, consumerUnary, diagonalDyadicRoot, rootWindowsReplay,
      replayReadbackConsumer, provenancePkg, consumerPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
