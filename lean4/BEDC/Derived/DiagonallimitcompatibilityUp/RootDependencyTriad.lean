import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibility_root_dependency_triad [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      triadRead sealEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont dyadic windows triadRead ->
        Cont triadRead readback sealEndpoint ->
          PkgSig bundle sealEndpoint pkg ->
            UnaryHistory dyadic ∧ UnaryHistory windows ∧ UnaryHistory readback ∧
              UnaryHistory triadRead ∧ UnaryHistory sealEndpoint ∧ UnaryHistory realSeal ∧
                Cont dyadic windows triadRead ∧ Cont triadRead readback sealEndpoint ∧
                  Cont readback realSeal route ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle sealEndpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier dyadicWindowsTriad triadReadbackEndpoint endpointPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _certUnary,
    _diagonalTriangleSeal, _dyadicWindowsReadback, readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have triadReadUnary : UnaryHistory triadRead :=
    unary_cont_closed dyadicUnary windowsUnary dyadicWindowsTriad
  have sealEndpointUnary : UnaryHistory sealEndpoint :=
    unary_cont_closed triadReadUnary readbackUnary triadReadbackEndpoint
  exact
    ⟨dyadicUnary, windowsUnary, readbackUnary, triadReadUnary, sealEndpointUnary,
      realSealUnary, dyadicWindowsTriad, triadReadbackEndpoint, readbackRealSealRoute,
      provenancePkg, endpointPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
