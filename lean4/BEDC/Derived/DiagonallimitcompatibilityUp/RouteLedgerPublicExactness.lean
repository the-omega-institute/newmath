import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityRouteLedgerPublicExactness [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance
      cert routeLedger routeEndpoint publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal triangle routeLedger ->
        Cont routeLedger dyadic routeEndpoint ->
          Cont routeEndpoint windows publicRead ->
            PkgSig bundle publicRead pkg ->
              UnaryHistory diagonal ∧ UnaryHistory triangle ∧ UnaryHistory dyadic ∧
                UnaryHistory windows ∧ UnaryHistory routeLedger ∧
                  UnaryHistory routeEndpoint ∧ UnaryHistory publicRead ∧
                    Cont diagonal triangle routeLedger ∧
                      Cont routeLedger dyadic routeEndpoint ∧
                        Cont routeEndpoint windows publicRead ∧ Cont readback realSeal route ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier diagonalTriangleRouteLedger routeLedgerDyadicRouteEndpoint
    routeEndpointWindowsPublicRead publicReadPkg
  obtain ⟨diagonalUnary, triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSealRow, _dyadicWindowsReadback, readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have routeLedgerUnary : UnaryHistory routeLedger :=
    unary_cont_closed diagonalUnary triangleUnary diagonalTriangleRouteLedger
  have routeEndpointUnary : UnaryHistory routeEndpoint :=
    unary_cont_closed routeLedgerUnary dyadicUnary routeLedgerDyadicRouteEndpoint
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed routeEndpointUnary windowsUnary routeEndpointWindowsPublicRead
  exact
    ⟨diagonalUnary, triangleUnary, dyadicUnary, windowsUnary, routeLedgerUnary,
      routeEndpointUnary, publicReadUnary, diagonalTriangleRouteLedger,
      routeLedgerDyadicRouteEndpoint, routeEndpointWindowsPublicRead, readbackRealSealRoute,
      provenancePkg, publicReadPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
