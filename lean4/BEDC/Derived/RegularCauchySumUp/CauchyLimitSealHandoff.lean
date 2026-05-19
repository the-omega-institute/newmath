import BEDC.Derived.CauchyLimitSealUp
import BEDC.Derived.RegularCauchySumUp

namespace BEDC.Derived.RegularCauchySumUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchySumCarrier_cauchy_limit_seal_handoff [AskSetup] [PackageSetup]
    {leftSource rightSource leftWindow rightWindow leftEndpoint rightEndpoint sumEndpoint budget
      readback transports routes provenance localCert : BHist}
    {sealSource sealSchedule sealDyadic sealDiagonal sealRow sealTransport sealProvenance
      sealLocalCert sealEndpoint publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchySumCarrier leftSource rightSource leftWindow rightWindow leftEndpoint
        rightEndpoint sumEndpoint budget readback transports routes provenance localCert bundle pkg ->
      BEDC.Derived.CauchyLimitSealUp.CauchyLimitSealCarrier sealSource sealSchedule
          sealDyadic sealDiagonal sealRow sealTransport sealProvenance sealLocalCert
          sealEndpoint bundle pkg ->
        Cont readback sealEndpoint publicRead ->
          PkgSig bundle publicRead pkg ->
            UnaryHistory readback ∧ UnaryHistory sealEndpoint ∧ UnaryHistory publicRead ∧
              Cont sumEndpoint budget readback ∧ Cont readback sealEndpoint publicRead ∧
                hsame sealEndpoint (append sealProvenance sealLocalCert) ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle sealEndpoint pkg ∧
                    PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle PkgSig
  intro sumCarrier sealCarrier publicRoute publicPkg
  obtain ⟨_leftSourceUnary, _rightSourceUnary, _leftWindowUnary, _rightWindowUnary,
    leftEndpointUnary, rightEndpointUnary, budgetUnary, _transportsUnary, _routesUnary,
    _provenanceUnary, _localCertUnary, _leftRoute, _rightRoute, sumRoute, readbackRoute,
    _provenanceRoute, provenancePkg⟩ := sumCarrier
  obtain ⟨_sealSourceUnary, _sealScheduleUnary, _sealDyadicUnary, _sealDiagonalUnary,
    _sealRowUnary, _sealTransportUnary, _sealProvenanceUnary, _sealLocalCertUnary,
    sealEndpointUnary, _sealSourceSchedule, _sealDyadicDiagonal, _sealTransportRoute,
    _sealEndpointRoute, sameSealEndpoint, sealEndpointPkg⟩ := sealCarrier
  have sumEndpointUnary : UnaryHistory sumEndpoint :=
    unary_cont_closed leftEndpointUnary rightEndpointUnary sumRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed sumEndpointUnary budgetUnary readbackRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed readbackUnary sealEndpointUnary publicRoute
  exact
    ⟨readbackUnary, sealEndpointUnary, publicUnary, readbackRoute, publicRoute,
      sameSealEndpoint, provenancePkg, sealEndpointPkg, publicPkg⟩

end BEDC.Derived.RegularCauchySumUp
