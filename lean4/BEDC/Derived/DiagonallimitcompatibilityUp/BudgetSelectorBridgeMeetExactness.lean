import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityBudgetSelectorBridgeMeetExactness [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selector locked endpoint selectorEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal windows selector ->
        Cont selector readback locked ->
          Cont locked realSeal endpoint ->
            Cont route cert selectorEndpoint ->
              hsame selectorEndpoint endpoint ->
                PkgSig bundle endpoint pkg ->
                  PkgSig bundle selectorEndpoint pkg ->
                    hsame endpoint selectorEndpoint ∧ UnaryHistory selector ∧
                      UnaryHistory locked ∧ UnaryHistory endpoint ∧
                        UnaryHistory selectorEndpoint ∧ Cont diagonal windows selector ∧
                          Cont selector readback locked ∧ Cont locked realSeal endpoint ∧
                            Cont route cert selectorEndpoint ∧ PkgSig bundle provenance pkg ∧
                              PkgSig bundle endpoint pkg ∧
                                PkgSig bundle selectorEndpoint pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle PkgSig UnaryHistory
  intro carrier diagonalWindowsSelector selectorReadbackLocked lockedRealSealEndpoint
    routeCertSelectorEndpoint selectorEndpointSame endpointPkg selectorEndpointPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, _dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, routeUnary, provenanceUnary, certUnary,
    _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindowsSelector
  have lockedUnary : UnaryHistory locked :=
    unary_cont_closed selectorUnary readbackUnary selectorReadbackLocked
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed lockedUnary realSealUnary lockedRealSealEndpoint
  have selectorEndpointUnary : UnaryHistory selectorEndpoint :=
    unary_cont_closed routeUnary certUnary routeCertSelectorEndpoint
  exact
    ⟨hsame_symm selectorEndpointSame, selectorUnary, lockedUnary, endpointUnary,
      selectorEndpointUnary, diagonalWindowsSelector, selectorReadbackLocked,
      lockedRealSealEndpoint, routeCertSelectorEndpoint, provenancePkg, endpointPkg,
      selectorEndpointPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
