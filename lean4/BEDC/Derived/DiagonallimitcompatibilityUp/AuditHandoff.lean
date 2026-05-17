import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityAuditHandoff [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      triadRead sealEndpoint consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback
        realSeal transport route provenance cert bundle pkg →
      Cont dyadic windows triadRead →
        Cont triadRead readback sealEndpoint →
          Cont readback realSeal consumer →
            PkgSig bundle sealEndpoint pkg →
              PkgSig bundle consumer pkg →
                UnaryHistory dyadic ∧ UnaryHistory windows ∧ UnaryHistory readback ∧
                  UnaryHistory triadRead ∧ UnaryHistory sealEndpoint ∧
                    UnaryHistory consumer ∧ Cont dyadic windows triadRead ∧
                      Cont triadRead readback sealEndpoint ∧
                        Cont readback realSeal consumer ∧
                          PkgSig bundle provenance pkg ∧
                            PkgSig bundle sealEndpoint pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig Cont UnaryHistory
  intro carrier dyadicWindowsTriad triadReadReadbackSeal readbackRealConsumer
    sealEndpointPkg consumerPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _carrierDyadicWindowsReadback,
    _readbackRealSealRoute, _routeCertTransport, provenancePkg⟩ := carrier
  have triadReadUnary : UnaryHistory triadRead :=
    unary_cont_closed dyadicUnary windowsUnary dyadicWindowsTriad
  have sealEndpointUnary : UnaryHistory sealEndpoint :=
    unary_cont_closed triadReadUnary readbackUnary triadReadReadbackSeal
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed readbackUnary realSealUnary readbackRealConsumer
  exact
    ⟨dyadicUnary, windowsUnary, readbackUnary, triadReadUnary, sealEndpointUnary,
      consumerUnary, dyadicWindowsTriad, triadReadReadbackSeal, readbackRealConsumer,
      provenancePkg, sealEndpointPkg, consumerPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
