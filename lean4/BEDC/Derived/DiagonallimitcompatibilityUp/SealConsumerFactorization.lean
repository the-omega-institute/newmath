import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilitySealConsumerFactorization [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      sealRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont sealRow readback sealRead ->
        Cont sealRead realSeal consumerRead ->
          PkgSig bundle consumerRead pkg ->
            UnaryHistory sealRead ∧ UnaryHistory consumerRead ∧
              Cont diagonal triangle sealRow ∧ Cont dyadic windows readback ∧
                Cont sealRow readback sealRead ∧ Cont sealRead realSeal consumerRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle UnaryHistory
  intro carrier sealRowReadbackSealRead sealReadRealSealConsumerRead consumerPkg
  obtain ⟨_diagonalUnary, _triangleUnary, sealRowUnary, _dyadicUnary, _windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, diagonalTriangleSealRow, dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed sealRowUnary readbackUnary sealRowReadbackSealRead
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed sealReadUnary realSealUnary sealReadRealSealConsumerRead
  exact
    ⟨sealReadUnary, consumerReadUnary, diagonalTriangleSealRow, dyadicWindowsReadback,
      sealRowReadbackSealRead, sealReadRealSealConsumerRead, provenancePkg, consumerPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
