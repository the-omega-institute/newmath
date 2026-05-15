import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityRootFormalLeanTargetBoundary [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      budgetWindow selectorRoute sealEndpoint support : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal dyadic budgetWindow ->
        Cont budgetWindow windows selectorRoute ->
          Cont selectorRoute readback sealEndpoint ->
            Cont route cert support ->
              PkgSig bundle support pkg ->
                UnaryHistory diagonal ∧ UnaryHistory dyadic ∧ UnaryHistory windows ∧
                  UnaryHistory readback ∧ UnaryHistory route ∧ UnaryHistory cert ∧
                    UnaryHistory budgetWindow ∧ UnaryHistory selectorRoute ∧
                      UnaryHistory sealEndpoint ∧ UnaryHistory support ∧
                        Cont diagonal dyadic budgetWindow ∧
                          Cont budgetWindow windows selectorRoute ∧
                            Cont selectorRoute readback sealEndpoint ∧
                              Cont route cert support ∧ PkgSig bundle provenance pkg ∧
                                PkgSig bundle support pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle UnaryHistory
  intro carrier diagonalDyadicBudget budgetWindowSelector selectorReadbackSeal routeCertSupport
    supportPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, _realSealUnary, _transportUnary, routeUnary, _provenanceUnary,
    certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have budgetWindowUnary : UnaryHistory budgetWindow :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicBudget
  have selectorRouteUnary : UnaryHistory selectorRoute :=
    unary_cont_closed budgetWindowUnary windowsUnary budgetWindowSelector
  have sealEndpointUnary : UnaryHistory sealEndpoint :=
    unary_cont_closed selectorRouteUnary readbackUnary selectorReadbackSeal
  have supportUnary : UnaryHistory support :=
    unary_cont_closed routeUnary certUnary routeCertSupport
  exact
    ⟨diagonalUnary, dyadicUnary, windowsUnary, readbackUnary, routeUnary, certUnary,
      budgetWindowUnary, selectorRouteUnary, sealEndpointUnary, supportUnary,
      diagonalDyadicBudget, budgetWindowSelector, selectorReadbackSeal, routeCertSupport,
      provenancePkg, supportPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
