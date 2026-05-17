import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityRealSealSourceLock [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      sealRead endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont sealRow readback sealRead ->
        Cont sealRead realSeal endpoint ->
          PkgSig bundle endpoint pkg ->
            UnaryHistory sealRow ∧ UnaryHistory readback ∧ UnaryHistory sealRead ∧
              UnaryHistory realSeal ∧ UnaryHistory endpoint ∧ Cont sealRow readback sealRead ∧
                Cont sealRead realSeal endpoint ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier sealRowReadback sealReadRealSeal endpointPkg
  obtain ⟨_diagonalUnary, _triangleUnary, sealRowUnary, _dyadicUnary, _windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed sealRowUnary readbackUnary sealRowReadback
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed sealReadUnary realSealUnary sealReadRealSeal
  exact
    ⟨sealRowUnary, readbackUnary, sealReadUnary, realSealUnary, endpointUnary,
      sealRowReadback, sealReadRealSeal, provenancePkg, endpointPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
