import BEDC.Derived.CauchyLimitSealUp
import BEDC.Derived.RegularCauchySumUp

namespace BEDC.Derived.RegularCauchySumUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchySumCarrier_real_seal_route [AskSetup] [PackageSetup]
    {leftSource rightSource leftWindow rightWindow leftEndpoint rightEndpoint sumEndpoint budget
      readback transports routes provenance localCert : BHist}
    {sealSource sealSchedule sealDyadic sealDiagonal sealRow sealTransport sealProvenance
      sealLocalCert sealEndpoint publicRead finalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchySumCarrier leftSource rightSource leftWindow rightWindow leftEndpoint
        rightEndpoint sumEndpoint budget readback transports routes provenance localCert bundle pkg ->
      BEDC.Derived.CauchyLimitSealUp.CauchyLimitSealCarrier sealSource sealSchedule
          sealDyadic sealDiagonal sealRow sealTransport sealProvenance sealLocalCert
          sealEndpoint bundle pkg ->
        Cont readback sealEndpoint publicRead ->
          Cont publicRead routes finalRead ->
            PkgSig bundle publicRead pkg ->
              PkgSig bundle finalRead pkg ->
                UnaryHistory leftSource ∧ UnaryHistory rightSource ∧ UnaryHistory readback ∧
                  UnaryHistory sealEndpoint ∧ UnaryHistory publicRead ∧
                    UnaryHistory finalRead ∧ Cont leftEndpoint rightEndpoint sumEndpoint ∧
                      Cont sumEndpoint budget readback ∧
                        Cont readback sealEndpoint publicRead ∧
                          Cont publicRead routes finalRead ∧
                            hsame sealEndpoint (append sealProvenance sealLocalCert) ∧
                              PkgSig bundle provenance pkg ∧ PkgSig bundle finalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro sumCarrier sealCarrier publicRoute finalRoute _publicPkg finalPkg
  obtain ⟨leftSourceUnary, rightSourceUnary, _leftWindowUnary, _rightWindowUnary,
    leftEndpointUnary, rightEndpointUnary, budgetUnary, _transportsUnary, routesUnary,
    _provenanceUnary, _localCertUnary, _leftRoute, _rightRoute, sumRoute, readbackRoute,
    _provenanceRoute, provenancePkg⟩ := sumCarrier
  obtain ⟨_sealSourceUnary, _sealScheduleUnary, _sealDyadicUnary, _sealDiagonalUnary,
    _sealRowUnary, _sealTransportUnary, _sealProvenanceUnary, _sealLocalCertUnary,
    sealEndpointUnary, _sealSourceSchedule, _sealDyadicDiagonal, _sealTransportRoute,
    _sealEndpointRoute, sameSealEndpoint, _sealEndpointPkg⟩ := sealCarrier
  have sumEndpointUnary : UnaryHistory sumEndpoint :=
    unary_cont_closed leftEndpointUnary rightEndpointUnary sumRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed sumEndpointUnary budgetUnary readbackRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed readbackUnary sealEndpointUnary publicRoute
  have finalUnary : UnaryHistory finalRead :=
    unary_cont_closed publicUnary routesUnary finalRoute
  exact
    ⟨leftSourceUnary,
      rightSourceUnary,
      readbackUnary,
      sealEndpointUnary,
      publicUnary,
      finalUnary,
      sumRoute,
      readbackRoute,
      publicRoute,
      finalRoute,
      sameSealEndpoint,
      provenancePkg,
      finalPkg⟩

end BEDC.Derived.RegularCauchySumUp
