import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibility_source_route_budget_lock [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      sourceRoute sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal triangle sourceRoute ->
        Cont sourceRoute dyadic readback ->
          Cont readback realSeal sealRead ->
            PkgSig bundle sealRead pkg ->
              UnaryHistory diagonal ∧ UnaryHistory triangle ∧ UnaryHistory dyadic ∧
                UnaryHistory windows ∧ UnaryHistory readback ∧ UnaryHistory realSeal ∧
                  UnaryHistory sourceRoute ∧ UnaryHistory sealRead ∧
                    Cont diagonal triangle sourceRoute ∧ Cont sourceRoute dyadic readback ∧
                      Cont readback realSeal sealRead ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle UnaryHistory
  intro carrier diagonalTriangleSourceRoute sourceRouteDyadicReadback readbackRealSealSealRead
    sealReadPkg
  obtain ⟨diagonalUnary, triangleUnary, _sealUnary, dyadicUnary, windowsUnary, readbackUnary,
    realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _certUnary,
    _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have sourceRouteUnary : UnaryHistory sourceRoute :=
    unary_cont_closed diagonalUnary triangleUnary diagonalTriangleSourceRoute
  have readbackUnaryFromRoute : UnaryHistory readback :=
    unary_cont_closed sourceRouteUnary dyadicUnary sourceRouteDyadicReadback
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary realSealUnary readbackRealSealSealRead
  exact
    ⟨diagonalUnary, triangleUnary, dyadicUnary, windowsUnary, readbackUnaryFromRoute,
      realSealUnary, sourceRouteUnary, sealReadUnary, diagonalTriangleSourceRoute,
      sourceRouteDyadicReadback, readbackRealSealSealRead, provenancePkg, sealReadPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
