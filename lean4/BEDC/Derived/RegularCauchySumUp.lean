import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.RegularCauchySumUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchySumCarrier [AskSetup] [PackageSetup]
    (leftSource rightSource leftWindow rightWindow leftEndpoint rightEndpoint sumEndpoint budget
      readback transports routes provenance localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory leftSource ∧ UnaryHistory rightSource ∧ UnaryHistory leftWindow ∧
    UnaryHistory rightWindow ∧ UnaryHistory leftEndpoint ∧ UnaryHistory rightEndpoint ∧
      UnaryHistory budget ∧ UnaryHistory transports ∧ UnaryHistory routes ∧
        UnaryHistory provenance ∧ UnaryHistory localCert ∧ Cont leftWindow leftEndpoint transports ∧
          Cont rightWindow rightEndpoint routes ∧ Cont leftEndpoint rightEndpoint sumEndpoint ∧
            Cont sumEndpoint budget readback ∧ Cont readback routes provenance ∧
              PkgSig bundle provenance pkg

theorem RegularCauchySumCarrier_window_budget [AskSetup] [PackageSetup]
    {leftSource rightSource leftWindow rightWindow leftEndpoint rightEndpoint sumEndpoint budget
      readback transports routes provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchySumCarrier leftSource rightSource leftWindow rightWindow leftEndpoint
        rightEndpoint sumEndpoint budget readback transports routes provenance localCert bundle pkg ->
      UnaryHistory sumEndpoint ∧ UnaryHistory readback ∧ Cont leftEndpoint rightEndpoint
        sumEndpoint ∧ Cont sumEndpoint budget readback ∧ PkgSig bundle provenance pkg := by
  intro carrier
  cases carrier with
  | intro leftSourceUnary carrier =>
      cases carrier with
      | intro rightSourceUnary carrier =>
          cases carrier with
          | intro leftWindowUnary carrier =>
              cases carrier with
              | intro rightWindowUnary carrier =>
                  cases carrier with
                  | intro leftEndpointUnary carrier =>
                      cases carrier with
                      | intro rightEndpointUnary carrier =>
                          cases carrier with
                          | intro budgetUnary carrier =>
                              cases carrier with
                              | intro transportsUnary carrier =>
                                  cases carrier with
                                  | intro routesUnary carrier =>
                                      cases carrier with
                                      | intro provenanceUnary carrier =>
                                          cases carrier with
                                          | intro localCertUnary carrier =>
                                              cases carrier with
                                              | intro leftRoute carrier =>
                                                  cases carrier with
                                                  | intro rightRoute carrier =>
                                                      cases carrier with
                                                      | intro sumEndpointRoute carrier =>
                                                          cases carrier with
                                                          | intro readbackRoute carrier =>
                                                              cases carrier with
                                                              | intro provenanceRoute pkgSig =>
                                                                  have sumEndpointUnary :
                                                                      UnaryHistory sumEndpoint :=
                                                                    unary_cont_closed
                                                                      leftEndpointUnary
                                                                      rightEndpointUnary
                                                                      sumEndpointRoute
                                                                  have readbackUnary :
                                                                      UnaryHistory readback :=
                                                                    unary_cont_closed
                                                                      sumEndpointUnary
                                                                      budgetUnary
                                                                      readbackRoute
                                                                  exact
                                                                    ⟨sumEndpointUnary,
                                                                      readbackUnary,
                                                                      sumEndpointRoute,
                                                                      readbackRoute,
                                                                      pkgSig⟩

theorem RegularCauchySumCarrier_regseqrat_handoff [AskSetup] [PackageSetup]
    {leftSource rightSource leftWindow rightWindow leftEndpoint rightEndpoint sumEndpoint budget
      readback transports routes provenance localCert consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchySumCarrier leftSource rightSource leftWindow rightWindow leftEndpoint
        rightEndpoint sumEndpoint budget readback transports routes provenance localCert bundle pkg ->
      Cont readback routes consumer ->
        UnaryHistory readback ∧ UnaryHistory consumer ∧ Cont sumEndpoint budget readback ∧
          Cont readback routes provenance ∧ hsame consumer (append readback routes) ∧
            PkgSig bundle provenance pkg := by
  intro carrier consumerRoute
  cases carrier with
  | intro leftSourceUnary carrier =>
      cases carrier with
      | intro rightSourceUnary carrier =>
          cases carrier with
          | intro leftWindowUnary carrier =>
              cases carrier with
              | intro rightWindowUnary carrier =>
                  cases carrier with
                  | intro leftEndpointUnary carrier =>
                      cases carrier with
                      | intro rightEndpointUnary carrier =>
                          cases carrier with
                          | intro budgetUnary carrier =>
                              cases carrier with
                              | intro transportsUnary carrier =>
                                  cases carrier with
                                  | intro routesUnary carrier =>
                                      cases carrier with
                                      | intro provenanceUnary carrier =>
                                          cases carrier with
                                          | intro localCertUnary carrier =>
                                              cases carrier with
                                              | intro leftRoute carrier =>
                                                  cases carrier with
                                                  | intro rightRoute carrier =>
                                                      cases carrier with
                                                      | intro sumEndpointRoute carrier =>
                                                          cases carrier with
                                                          | intro readbackRoute carrier =>
                                                              cases carrier with
                                                              | intro provenanceRoute pkgSig =>
                                                                  have sumEndpointUnary :
                                                                      UnaryHistory sumEndpoint :=
                                                                    unary_cont_closed
                                                                      leftEndpointUnary
                                                                      rightEndpointUnary
                                                                      sumEndpointRoute
                                                                  have readbackUnary :
                                                                      UnaryHistory readback :=
                                                                    unary_cont_closed
                                                                      sumEndpointUnary
                                                                      budgetUnary
                                                                      readbackRoute
                                                                  have consumerUnary :
                                                                      UnaryHistory consumer :=
                                                                    unary_cont_closed
                                                                      readbackUnary routesUnary
                                                                      consumerRoute
                                                                  exact
                                                                    ⟨readbackUnary,
                                                                      consumerUnary,
                                                                      readbackRoute,
                                                                      provenanceRoute,
                                                                      consumerRoute,
                                                                      pkgSig⟩

end BEDC.Derived.RegularCauchySumUp
