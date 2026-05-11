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

theorem KalmanFilterCarrier_estimate_transport_stability [AskSetup] [PackageSetup]
    {prior transition prediction observation residual covariance gain posterior innovation update
      provenance endpoint prior' transition' prediction' observation' residual' covariance' gain'
      posterior' innovation' update' provenance' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KalmanFilterCarrier prior transition prediction observation residual covariance gain posterior
        innovation update provenance endpoint bundle pkg ->
      hsame prior prior' ->
        hsame transition transition' ->
          hsame observation observation' ->
            hsame covariance covariance' ->
              hsame gain gain' ->
                hsame posterior posterior' ->
                  hsame provenance provenance' ->
                    Cont prior' transition' prediction' ->
                      Cont prediction' observation' residual' ->
                        Cont covariance' observation' innovation' ->
                          Cont innovation' gain' update' ->
                            Cont update' posterior' endpoint' ->
                              Cont endpoint' provenance' endpoint' ->
                                PkgSig bundle endpoint' pkg ->
                                  KalmanFilterCarrier prior' transition' prediction' observation'
                                      residual' covariance' gain' posterior' innovation' update'
                                      provenance' endpoint' bundle pkg ∧
                                    hsame prediction prediction' ∧
                                      hsame residual residual' ∧
                                        hsame innovation innovation' ∧ hsame update update' ∧
                                          hsame endpoint endpoint' := by
  intro carrier samePrior sameTransition sameObservation sameCovariance sameGain samePosterior
    sameProvenance predictionRoute' residualRoute' innovationRoute' updateRoute' endpointRoute'
    provenanceRoute' pkgSig'
  have priorUnary' : UnaryHistory prior' :=
    unary_transport carrier.left samePrior
  have transitionUnary' : UnaryHistory transition' :=
    unary_transport carrier.right.left sameTransition
  have observationUnary' : UnaryHistory observation' :=
    unary_transport carrier.right.right.right.left sameObservation
  have covarianceUnary' : UnaryHistory covariance' :=
    unary_transport carrier.right.right.right.right.right.left sameCovariance
  have gainUnary' : UnaryHistory gain' :=
    unary_transport carrier.right.right.right.right.right.right.left sameGain
  have posteriorUnary' : UnaryHistory posterior' :=
    unary_transport carrier.right.right.right.right.right.right.right.left samePosterior
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport carrier.right.right.right.right.right.right.right.right.right.right.left
      sameProvenance
  have predictionUnary' : UnaryHistory prediction' :=
    unary_cont_closed priorUnary' transitionUnary' predictionRoute'
  have residualUnary' : UnaryHistory residual' :=
    unary_cont_closed predictionUnary' observationUnary' residualRoute'
  have innovationUnary' : UnaryHistory innovation' :=
    unary_cont_closed covarianceUnary' observationUnary' innovationRoute'
  have updateUnary' : UnaryHistory update' :=
    unary_cont_closed innovationUnary' gainUnary' updateRoute'
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed updateUnary' posteriorUnary' endpointRoute'
  have samePrediction : hsame prediction prediction' :=
    cont_respects_hsame samePrior sameTransition
      carrier.right.right.right.right.right.right.right.right.right.right.right.right.left
      predictionRoute'
  have sameResidual : hsame residual residual' :=
    cont_respects_hsame samePrediction sameObservation
      carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.left
      residualRoute'
  have sameInnovation : hsame innovation innovation' :=
    cont_respects_hsame sameCovariance sameObservation
      carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left
      innovationRoute'
  have sameUpdate : hsame update update' :=
    cont_respects_hsame sameInnovation sameGain
      carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left
      updateRoute'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameUpdate samePosterior
      carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left
      endpointRoute'
  constructor
  · exact
      ⟨priorUnary', transitionUnary', predictionUnary', observationUnary', residualUnary',
        covarianceUnary', gainUnary', posteriorUnary', innovationUnary', updateUnary',
        provenanceUnary', endpointUnary', predictionRoute', residualRoute', innovationRoute',
        updateRoute', endpointRoute', provenanceRoute', pkgSig'⟩
  · exact And.intro samePrediction
      (And.intro sameResidual
        (And.intro sameInnovation (And.intro sameUpdate sameEndpoint)))

end BEDC.Derived.KalmanFilterUp
