import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityRealSealRouteExhaustion [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      budgetRead sealRead endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal dyadic budgetRead ->
        Cont budgetRead windows sealRead ->
          Cont sealRead realSeal endpoint ->
            PkgSig bundle endpoint pkg ->
              UnaryHistory diagonal ∧ UnaryHistory triangle ∧ UnaryHistory sealRow ∧
                UnaryHistory dyadic ∧ UnaryHistory windows ∧ UnaryHistory readback ∧
                  UnaryHistory realSeal ∧ UnaryHistory budgetRead ∧ UnaryHistory sealRead ∧
                    UnaryHistory endpoint ∧ Cont diagonal triangle sealRow ∧
                      Cont diagonal dyadic budgetRead ∧ Cont budgetRead windows sealRead ∧
                        Cont sealRead realSeal endpoint ∧ Cont dyadic windows readback ∧
                          Cont readback realSeal route ∧ PkgSig bundle provenance pkg ∧
                            PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg
  intro carrier diagonalDyadicBudgetRead budgetReadWindowsSealRead sealReadRealSealEndpoint
    endpointPkg
  obtain ⟨diagonalUnary, triangleUnary, sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, diagonalTriangleSeal, dyadicWindowsReadback, readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have budgetReadUnary : UnaryHistory budgetRead :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicBudgetRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed budgetReadUnary windowsUnary budgetReadWindowsSealRead
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed sealReadUnary realSealUnary sealReadRealSealEndpoint
  exact
    ⟨diagonalUnary, triangleUnary, sealRowUnary, dyadicUnary, windowsUnary, readbackUnary,
      realSealUnary, budgetReadUnary, sealReadUnary, endpointUnary, diagonalTriangleSeal,
      diagonalDyadicBudgetRead, budgetReadWindowsSealRead, sealReadRealSealEndpoint,
      dyadicWindowsReadback, readbackRealSealRoute, provenancePkg, endpointPkg⟩

theorem DiagonalLimitCompatibility_real_seal_route_exhaustion [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      sealRoute terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont sealRow readback sealRoute ->
        Cont sealRoute realSeal terminal ->
          PkgSig bundle terminal pkg ->
            UnaryHistory sealRow ∧ UnaryHistory readback ∧ UnaryHistory realSeal ∧
              UnaryHistory sealRoute ∧ UnaryHistory terminal ∧
                Cont sealRow readback sealRoute ∧ Cont sealRoute realSeal terminal ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig DiagonalLimitCompatibilityCarrier
  intro carrier sealRowReadbackSealRoute sealRouteRealSealTerminal terminalPkg
  obtain ⟨_diagonalUnary, _triangleUnary, sealRowUnary, _dyadicUnary, _windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have sealRouteUnary : UnaryHistory sealRoute :=
    unary_cont_closed sealRowUnary readbackUnary sealRowReadbackSealRoute
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed sealRouteUnary realSealUnary sealRouteRealSealTerminal
  exact
    ⟨sealRowUnary, readbackUnary, realSealUnary, sealRouteUnary, terminalUnary,
      sealRowReadbackSealRoute, sealRouteRealSealTerminal, provenancePkg, terminalPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
