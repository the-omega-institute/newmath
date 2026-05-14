import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityConsumerThreshold [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont readback realSeal consumer ->
        PkgSig bundle consumer pkg ->
          UnaryHistory diagonal ∧ UnaryHistory triangle ∧ UnaryHistory sealRow ∧
            UnaryHistory dyadic ∧ UnaryHistory windows ∧ UnaryHistory readback ∧
              UnaryHistory realSeal ∧ UnaryHistory consumer ∧
                Cont diagonal triangle sealRow ∧ Cont dyadic windows readback ∧
                  Cont readback realSeal consumer ∧ Cont route cert transport ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle UnaryHistory
  intro carrier readbackRealSealConsumer consumerPkg
  obtain ⟨diagonalUnary, triangleUnary, sealUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, diagonalTriangleSeal, dyadicWindowsReadback, _readbackRealSealRoute,
    routeCertTransport, provenancePkg⟩ := carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed readbackUnary realSealUnary readbackRealSealConsumer
  exact
    ⟨diagonalUnary, triangleUnary, sealUnary, dyadicUnary, windowsUnary, readbackUnary,
      realSealUnary, consumerUnary, diagonalTriangleSeal, dyadicWindowsReadback,
      readbackRealSealConsumer, routeCertTransport, provenancePkg, consumerPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
