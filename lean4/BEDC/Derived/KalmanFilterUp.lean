import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.KalmanFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def KalmanFilterCarrier [AskSetup] [PackageSetup]
    (prior transition prediction observation residual covariance gain posterior innovation update
      provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory prior ∧
    UnaryHistory transition ∧
      UnaryHistory prediction ∧
        UnaryHistory observation ∧
          UnaryHistory residual ∧
            UnaryHistory covariance ∧
              UnaryHistory gain ∧
                UnaryHistory posterior ∧
                  UnaryHistory innovation ∧
                    UnaryHistory update ∧
                      UnaryHistory provenance ∧
                        UnaryHistory endpoint ∧
                          Cont prior transition prediction ∧
                            Cont prediction observation residual ∧
                              Cont covariance observation innovation ∧
                                Cont innovation gain update ∧
                                  Cont update posterior endpoint ∧
                                    Cont endpoint provenance endpoint ∧
                                      PkgSig bundle endpoint pkg

theorem KalmanFilterCarrier_prediction_update_obligation [AskSetup] [PackageSetup]
    {prior transition prediction observation residual covariance gain posterior innovation update
      provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KalmanFilterCarrier prior transition prediction observation residual covariance gain posterior
        innovation update provenance endpoint bundle pkg ->
      Cont prior transition prediction ∧
        Cont prediction observation residual ∧
          Cont covariance observation innovation ∧
            Cont innovation gain update ∧
              Cont update posterior endpoint ∧ PkgSig bundle endpoint pkg := by
  intro carrier
  exact And.intro carrier.right.right.right.right.right.right.right.right.right.right.right.right.left
    (And.intro
      carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.left
      (And.intro
        carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left
        (And.intro
          carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left
          (And.intro
            carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left
            carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right))))

theorem KalmanFilterCarrier_observation_innovation_ledger [AskSetup] [PackageSetup]
    {prior transition prediction observation residual covariance gain posterior innovation update
      provenance endpoint innovationEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KalmanFilterCarrier prior transition prediction observation residual covariance gain posterior
        innovation update provenance endpoint bundle pkg ->
      Cont innovation residual innovationEndpoint ->
        UnaryHistory residual ∧
          UnaryHistory innovation ∧
            UnaryHistory innovationEndpoint ∧
              Cont prediction observation residual ∧
                Cont covariance observation innovation ∧
                  hsame residual (append prediction observation) ∧
                    hsame innovation (append covariance observation) ∧
                      hsame innovationEndpoint (append innovation residual) ∧
                        PkgSig bundle endpoint pkg := by
  intro carrier innovationCont
  cases carrier with
  | intro priorUnary carrier =>
      cases carrier with
      | intro transitionUnary carrier =>
          cases carrier with
          | intro predictionUnary carrier =>
              cases carrier with
              | intro observationUnary carrier =>
                  cases carrier with
                  | intro residualUnary carrier =>
                      cases carrier with
                      | intro covarianceUnary carrier =>
                          cases carrier with
                          | intro gainUnary carrier =>
                              cases carrier with
                              | intro posteriorUnary carrier =>
                                  cases carrier with
                                  | intro innovationUnary carrier =>
                                      cases carrier with
                                      | intro updateUnary carrier =>
                                          cases carrier with
                                          | intro provenanceUnary carrier =>
                                              cases carrier with
                                              | intro endpointUnary carrier =>
                                                  cases carrier with
                                                  | intro predictionCont carrier =>
                                                      cases carrier with
                                                      | intro residualCont carrier =>
                                                          cases carrier with
                                                          | intro innovationLedgerCont carrier =>
                                                              cases carrier with
                                                              | intro updateCont carrier =>
                                                                  cases carrier with
                                                                  | intro endpointCont carrier =>
                                                                      cases carrier with
                                                                      | intro provenanceCont pkgSig =>
                                                                          have innovationEndpointUnary :
                                                                              UnaryHistory
                                                                                innovationEndpoint :=
                                                                            unary_cont_closed
                                                                              innovationUnary
                                                                              residualUnary
                                                                              innovationCont
                                                                          exact And.intro residualUnary
                                                                            (And.intro innovationUnary
                                                                              (And.intro
                                                                                innovationEndpointUnary
                                                                                (And.intro
                                                                                  residualCont
                                                                                  (And.intro
                                                                                    innovationLedgerCont
                                                                                    (And.intro
                                                                                      residualCont
                                                                                      (And.intro
                                                                                        innovationLedgerCont
                                                                                        (And.intro
                                                                                          innovationCont
                                                                                          pkgSig)))))))

end BEDC.Derived.KalmanFilterUp
