import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityRootSupportProjectionNonescape [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      supportProjection supportEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont route provenance supportProjection ->
        Cont supportProjection cert supportEndpoint ->
          PkgSig bundle supportEndpoint pkg ->
            UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory supportProjection ∧
              UnaryHistory cert ∧ UnaryHistory supportEndpoint ∧
                Cont route provenance supportProjection ∧
                  Cont supportProjection cert supportEndpoint ∧ Cont route cert transport ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle supportEndpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier routeProvenanceSupport supportCertEndpoint supportEndpointPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealUnary, _dyadicUnary, _windowsUnary,
    _readbackUnary, _realSealUnary, _transportUnary, routeUnary, provenanceUnary,
    certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    routeCertTransport, provenancePkg⟩ := carrier
  have supportProjectionUnary : UnaryHistory supportProjection :=
    unary_cont_closed routeUnary provenanceUnary routeProvenanceSupport
  have supportEndpointUnary : UnaryHistory supportEndpoint :=
    unary_cont_closed supportProjectionUnary certUnary supportCertEndpoint
  exact
    ⟨routeUnary, provenanceUnary, supportProjectionUnary, certUnary, supportEndpointUnary,
      routeProvenanceSupport, supportCertEndpoint, routeCertTransport, provenancePkg,
      supportEndpointPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
