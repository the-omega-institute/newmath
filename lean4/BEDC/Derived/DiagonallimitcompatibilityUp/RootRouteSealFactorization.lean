import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityRootRouteSealFactorization [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selector locked endpoint final : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal windows selector ->
        Cont selector readback locked ->
          Cont locked realSeal endpoint ->
            Cont endpoint cert final ->
              PkgSig bundle final pkg ->
                UnaryHistory selector ∧ UnaryHistory locked ∧ UnaryHistory endpoint ∧
                  UnaryHistory final ∧ Cont diagonal windows selector ∧
                    Cont selector readback locked ∧ Cont locked realSeal endpoint ∧
                      Cont endpoint cert final ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle final pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle UnaryHistory
  intro carrier diagonalWindowsSelector selectorReadbackLocked lockedRealSealEndpoint
    endpointCertFinal finalPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, _dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindowsSelector
  have lockedUnary : UnaryHistory locked :=
    unary_cont_closed selectorUnary readbackUnary selectorReadbackLocked
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed lockedUnary realSealUnary lockedRealSealEndpoint
  have finalUnary : UnaryHistory final :=
    unary_cont_closed endpointUnary certUnary endpointCertFinal
  exact
    ⟨selectorUnary, lockedUnary, endpointUnary, finalUnary, diagonalWindowsSelector,
      selectorReadbackLocked, lockedRealSealEndpoint, endpointCertFinal, provenancePkg,
      finalPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
