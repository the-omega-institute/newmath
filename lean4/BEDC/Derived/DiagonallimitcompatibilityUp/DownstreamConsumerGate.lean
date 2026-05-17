import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityDownstreamConsumerGate [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont dyadic readback consumer ->
        PkgSig bundle consumer pkg ->
          UnaryHistory diagonal ∧ UnaryHistory triangle ∧ UnaryHistory dyadic ∧
            UnaryHistory windows ∧ UnaryHistory readback ∧ UnaryHistory consumer ∧
              Cont diagonal triangle sealRow ∧ Cont dyadic windows readback ∧
                Cont dyadic readback consumer ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg
  intro carrier dyadicReadbackConsumer consumerPkg
  obtain ⟨diagonalUnary, triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, diagonalTriangleSeal, dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed dyadicUnary readbackUnary dyadicReadbackConsumer
  exact
    ⟨diagonalUnary, triangleUnary, dyadicUnary, windowsUnary, readbackUnary, consumerUnary,
      diagonalTriangleSeal, dyadicWindowsReadback, dyadicReadbackConsumer, provenancePkg,
      consumerPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
