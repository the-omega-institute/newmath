import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibility_seal_readback_exactness [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      gateOut endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont readback realSeal gateOut →
        Cont gateOut cert endpoint →
          PkgSig bundle endpoint pkg →
            UnaryHistory readback ∧ UnaryHistory realSeal ∧ UnaryHistory gateOut ∧
              UnaryHistory cert ∧ UnaryHistory endpoint ∧ Cont readback realSeal gateOut ∧
                Cont gateOut cert endpoint ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier readbackRealSealGateOut gateOutCertEndpoint endpointPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealRowUnary, _dyadicUnary, _windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have gateOutUnary : UnaryHistory gateOut :=
    unary_cont_closed readbackUnary realSealUnary readbackRealSealGateOut
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed gateOutUnary certUnary gateOutCertEndpoint
  exact
    ⟨readbackUnary, realSealUnary, gateOutUnary, certUnary, endpointUnary,
      readbackRealSealGateOut, gateOutCertEndpoint, provenancePkg, endpointPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
