import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibility_seal_route_compatibility [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont sealRow readback sealRead ->
        PkgSig bundle sealRead pkg ->
          UnaryHistory sealRow ∧ UnaryHistory readback ∧ UnaryHistory realSeal ∧
            UnaryHistory sealRead ∧ Cont diagonal triangle sealRow ∧
              Cont dyadic windows readback ∧ Cont sealRow readback sealRead ∧
                Cont readback realSeal route ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory
  intro carrier sealReadRoute sealReadPkg
  obtain ⟨_diagonalUnary, _triangleUnary, sealUnary, _dyadicUnary, _windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, diagonalTriangleSeal, dyadicWindowsReadback, readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed sealUnary readbackUnary sealReadRoute
  exact
    ⟨sealUnary, readbackUnary, realSealUnary, sealReadUnary, diagonalTriangleSeal,
      dyadicWindowsReadback, sealReadRoute, readbackRealSealRoute, provenancePkg,
      sealReadPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
