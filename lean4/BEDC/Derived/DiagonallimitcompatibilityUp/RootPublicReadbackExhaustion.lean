import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCarrier_selector_budget_root_public_readback_exhaustion
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selector locked sealEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal windows selector ->
        Cont selector readback locked ->
          Cont locked realSeal sealEndpoint ->
            PkgSig bundle sealEndpoint pkg ->
              UnaryHistory diagonal ∧ UnaryHistory windows ∧ UnaryHistory readback ∧
                UnaryHistory realSeal ∧ UnaryHistory selector ∧ UnaryHistory locked ∧
                  UnaryHistory sealEndpoint ∧ Cont diagonal windows selector ∧
                    Cont selector readback locked ∧ Cont locked realSeal sealEndpoint ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle sealEndpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier diagonalWindowsSelector selectorReadbackLocked lockedRealSealEndpoint
    endpointPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, _dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindowsSelector
  have lockedUnary : UnaryHistory locked :=
    unary_cont_closed selectorUnary readbackUnary selectorReadbackLocked
  have sealEndpointUnary : UnaryHistory sealEndpoint :=
    unary_cont_closed lockedUnary realSealUnary lockedRealSealEndpoint
  exact
    ⟨diagonalUnary, windowsUnary, readbackUnary, realSealUnary, selectorUnary, lockedUnary,
      sealEndpointUnary, diagonalWindowsSelector, selectorReadbackLocked,
      lockedRealSealEndpoint, provenancePkg, endpointPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
