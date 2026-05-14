import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityRootRequestSelectorExhaustion [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      rootRequest selector locked sealEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal dyadic rootRequest ->
        Cont rootRequest windows selector ->
          Cont selector readback locked ->
            Cont locked realSeal sealEndpoint ->
              PkgSig bundle sealEndpoint pkg ->
                UnaryHistory rootRequest ∧ UnaryHistory selector ∧ UnaryHistory locked ∧
                  UnaryHistory sealEndpoint ∧ Cont diagonal dyadic rootRequest ∧
                    Cont rootRequest windows selector ∧ Cont selector readback locked ∧
                      Cont locked realSeal sealEndpoint ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle sealEndpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier diagonalDyadicRootRequest rootRequestWindowsSelector selectorReadbackLocked
    lockedRealSealEndpoint sealEndpointPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have rootRequestUnary : UnaryHistory rootRequest :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicRootRequest
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed rootRequestUnary windowsUnary rootRequestWindowsSelector
  have lockedUnary : UnaryHistory locked :=
    unary_cont_closed selectorUnary readbackUnary selectorReadbackLocked
  have sealEndpointUnary : UnaryHistory sealEndpoint :=
    unary_cont_closed lockedUnary realSealUnary lockedRealSealEndpoint
  exact
    ⟨rootRequestUnary, selectorUnary, lockedUnary, sealEndpointUnary,
      diagonalDyadicRootRequest, rootRequestWindowsSelector, selectorReadbackLocked,
      lockedRealSealEndpoint, provenancePkg, sealEndpointPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
