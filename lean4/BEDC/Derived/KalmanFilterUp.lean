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
      covariancePosterior provenance endpoint : BHist)
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
                      UnaryHistory covariancePosterior ∧
                        UnaryHistory provenance ∧
                          UnaryHistory endpoint ∧
                            Cont prior transition prediction ∧
                              Cont prediction observation residual ∧
                                Cont covariance observation innovation ∧
                                  Cont innovation gain update ∧
                                    Cont innovation gain posterior ∧
                                      Cont update posterior covariancePosterior ∧
                                        Cont posterior covariancePosterior endpoint ∧
                                          PkgSig bundle endpoint pkg

theorem KalmanFilterCarrier_estimate_transport [AskSetup] [PackageSetup]
    {prior transition prediction observation residual covariance gain posterior innovation update
      covariancePosterior provenance endpoint prior' transition' prediction' observation' residual'
      covariance' gain' posterior' innovation' update' covariancePosterior' provenance'
      endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KalmanFilterCarrier prior transition prediction observation residual covariance gain posterior
        innovation update covariancePosterior provenance endpoint bundle pkg ->
      hsame prior prior' ->
        hsame transition transition' ->
          hsame covariance covariance' ->
            hsame observation observation' ->
              hsame gain gain' ->
                hsame update update' ->
                  hsame covariancePosterior covariancePosterior' ->
                    hsame provenance provenance' ->
                      Cont prior' transition' prediction' ->
                        Cont prediction' observation' residual' ->
                          Cont covariance' observation' innovation' ->
                            Cont innovation' gain' update' ->
                              Cont innovation' gain' posterior' ->
                                Cont update' posterior' covariancePosterior' ->
                                  Cont posterior' covariancePosterior' endpoint' ->
                                    PkgSig bundle endpoint' pkg ->
                                      KalmanFilterCarrier prior' transition' prediction'
                                          observation' residual' covariance' gain' posterior'
                                          innovation' update' covariancePosterior' provenance'
                                          endpoint' bundle pkg ∧
                                        hsame prediction prediction' ∧
                                          hsame residual residual' ∧
                                            hsame innovation innovation' ∧
                                              hsame posterior posterior' ∧
                                                hsame endpoint endpoint' := by
  intro carrier samePrior sameTransition sameCovariance sameObservation sameGain sameUpdate
    sameCovariancePosterior sameProvenance predictionRow' residualRow' innovationRow' updateRow'
    posteriorRow' covariancePosteriorRow' endpointRow' pkgSig'
  rcases carrier with
    ⟨priorUnary, transitionUnary, _predictionUnary, observationUnary, _residualUnary,
      covarianceUnary, gainUnary, _posteriorUnary, _innovationUnary, updateUnary,
      covariancePosteriorUnary, provenanceUnary, _endpointUnary, predictionRow, residualRow,
      innovationRow, _updateRow, posteriorRow, _covariancePosteriorRow, endpointRow, _pkgSig⟩
  have priorUnary' : UnaryHistory prior' :=
    unary_transport priorUnary samePrior
  have transitionUnary' : UnaryHistory transition' :=
    unary_transport transitionUnary sameTransition
  have covarianceUnary' : UnaryHistory covariance' :=
    unary_transport covarianceUnary sameCovariance
  have observationUnary' : UnaryHistory observation' :=
    unary_transport observationUnary sameObservation
  have gainUnary' : UnaryHistory gain' :=
    unary_transport gainUnary sameGain
  have updateUnary' : UnaryHistory update' :=
    unary_transport updateUnary sameUpdate
  have covariancePosteriorUnary' : UnaryHistory covariancePosterior' :=
    unary_transport covariancePosteriorUnary sameCovariancePosterior
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have predictionUnary' : UnaryHistory prediction' :=
    unary_cont_closed priorUnary' transitionUnary' predictionRow'
  have residualUnary' : UnaryHistory residual' :=
    unary_cont_closed predictionUnary' observationUnary' residualRow'
  have innovationUnary' : UnaryHistory innovation' :=
    unary_cont_closed covarianceUnary' observationUnary' innovationRow'
  have posteriorUnary' : UnaryHistory posterior' :=
    unary_cont_closed innovationUnary' gainUnary' posteriorRow'
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed posteriorUnary' covariancePosteriorUnary' endpointRow'
  have samePrediction : hsame prediction prediction' :=
    cont_respects_hsame samePrior sameTransition predictionRow predictionRow'
  have sameResidual : hsame residual residual' :=
    cont_respects_hsame samePrediction sameObservation residualRow residualRow'
  have sameInnovation : hsame innovation innovation' :=
    cont_respects_hsame sameCovariance sameObservation innovationRow innovationRow'
  have samePosterior : hsame posterior posterior' :=
    cont_respects_hsame sameInnovation sameGain posteriorRow posteriorRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame samePosterior sameCovariancePosterior endpointRow endpointRow'
  have targetCarrier :
      KalmanFilterCarrier prior' transition' prediction' observation' residual' covariance' gain'
        posterior' innovation' update' covariancePosterior' provenance' endpoint' bundle pkg :=
    ⟨priorUnary', transitionUnary', predictionUnary', observationUnary', residualUnary',
      covarianceUnary', gainUnary', posteriorUnary', innovationUnary', updateUnary',
      covariancePosteriorUnary', provenanceUnary', endpointUnary', predictionRow', residualRow',
      innovationRow', updateRow', posteriorRow', covariancePosteriorRow', endpointRow', pkgSig'⟩
  exact And.intro targetCarrier
    (And.intro samePrediction
      (And.intro sameResidual
        (And.intro sameInnovation (And.intro samePosterior sameEndpoint))))

theorem KalmanFilterCarrier_prediction_update_obligation [AskSetup] [PackageSetup]
    {prior transition prediction observation residual covariance gain posterior innovation update
      covariancePosterior provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KalmanFilterCarrier prior transition prediction observation residual covariance gain posterior
        innovation update covariancePosterior provenance endpoint bundle pkg ->
      Cont prior transition prediction ∧
        Cont prediction observation residual ∧
          Cont covariance observation innovation ∧
            Cont innovation gain update ∧
              Cont update posterior covariancePosterior ∧ PkgSig bundle endpoint pkg := by
  intro carrier
  rcases carrier with
    ⟨_priorUnary, _transitionUnary, _predictionUnary, _observationUnary, _residualUnary,
      _covarianceUnary, _gainUnary, _posteriorUnary, _innovationUnary, _updateUnary,
      _covariancePosteriorUnary, _provenanceUnary, _endpointUnary, predictionRow, residualRow,
      innovationRow, updateRow, _posteriorRow, covariancePosteriorRow, _endpointRow, pkgSig⟩
  exact And.intro predictionRow
    (And.intro residualRow
      (And.intro innovationRow
        (And.intro updateRow (And.intro covariancePosteriorRow pkgSig))))

theorem KalmanFilterCarrier_observation_innovation_ledger [AskSetup] [PackageSetup]
    {prior transition prediction observation residual covariance gain posterior innovation update
      covariancePosterior provenance endpoint innovationEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KalmanFilterCarrier prior transition prediction observation residual covariance gain posterior
        innovation update covariancePosterior provenance endpoint bundle pkg ->
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
  rcases carrier with
    ⟨_priorUnary, _transitionUnary, _predictionUnary, _observationUnary, residualUnary,
      _covarianceUnary, _gainUnary, _posteriorUnary, innovationUnary, _updateUnary,
      _covariancePosteriorUnary, _provenanceUnary, _endpointUnary, _predictionCont,
      residualCont, innovationLedgerCont, _updateCont, _posteriorCont,
      _covariancePosteriorCont, _endpointCont, pkgSig⟩
  have innovationEndpointUnary : UnaryHistory innovationEndpoint :=
    unary_cont_closed innovationUnary residualUnary innovationCont
  exact And.intro residualUnary
    (And.intro innovationUnary
      (And.intro innovationEndpointUnary
        (And.intro residualCont
          (And.intro innovationLedgerCont
            (And.intro residualCont
              (And.intro innovationLedgerCont
                (And.intro innovationCont pkgSig)))))))

theorem KalmanFilterCarrier_estimate_transport_stability [AskSetup] [PackageSetup]
    {prior transition prediction observation residual covariance gain posterior innovation update
      covariancePosterior provenance endpoint prior' transition' prediction' observation' residual'
      covariance' gain' posterior' innovation' update' covariancePosterior' provenance'
      endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KalmanFilterCarrier prior transition prediction observation residual covariance gain posterior
        innovation update covariancePosterior provenance endpoint bundle pkg ->
      hsame prior prior' ->
        hsame transition transition' ->
          hsame observation observation' ->
            hsame covariance covariance' ->
              hsame gain gain' ->
                hsame posterior posterior' ->
                  hsame update update' ->
                    hsame provenance provenance' ->
                      Cont prior' transition' prediction' ->
                        Cont prediction' observation' residual' ->
                          Cont covariance' observation' innovation' ->
                            Cont innovation' gain' update' ->
                              Cont innovation' gain' posterior' ->
                                Cont update' posterior' covariancePosterior' ->
                                  Cont posterior' covariancePosterior' endpoint' ->
                                    PkgSig bundle endpoint' pkg ->
                                      KalmanFilterCarrier prior' transition' prediction'
                                          observation' residual' covariance' gain' posterior'
                                          innovation' update' covariancePosterior' provenance'
                                          endpoint' bundle pkg ∧
                                        hsame prediction prediction' ∧
                                          hsame residual residual' ∧
                                            hsame innovation innovation' ∧ hsame update update' ∧
                                              hsame covariancePosterior covariancePosterior' ∧
                                                hsame endpoint endpoint' := by
  intro carrier samePrior sameTransition sameObservation sameCovariance sameGain samePosterior
    sameUpdate sameProvenance predictionRoute' residualRoute' innovationRoute' updateRoute'
    posteriorRoute' covariancePosteriorRoute' endpointRoute' pkgSig'
  rcases carrier with
    ⟨priorUnary, transitionUnary, _predictionUnary, observationUnary, _residualUnary,
      covarianceUnary, gainUnary, posteriorUnary, _innovationUnary, updateUnary,
      _covariancePosteriorUnary, provenanceUnary, _endpointUnary, predictionRoute,
      residualRoute, innovationRoute, _updateRoute, _posteriorRoute, covariancePosteriorRoute,
      endpointRoute, _pkgSig⟩
  have priorUnary' : UnaryHistory prior' :=
    unary_transport priorUnary samePrior
  have transitionUnary' : UnaryHistory transition' :=
    unary_transport transitionUnary sameTransition
  have observationUnary' : UnaryHistory observation' :=
    unary_transport observationUnary sameObservation
  have covarianceUnary' : UnaryHistory covariance' :=
    unary_transport covarianceUnary sameCovariance
  have gainUnary' : UnaryHistory gain' :=
    unary_transport gainUnary sameGain
  have posteriorUnary' : UnaryHistory posterior' :=
    unary_transport posteriorUnary samePosterior
  have updateUnary' : UnaryHistory update' :=
    unary_transport updateUnary sameUpdate
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have predictionUnary' : UnaryHistory prediction' :=
    unary_cont_closed priorUnary' transitionUnary' predictionRoute'
  have residualUnary' : UnaryHistory residual' :=
    unary_cont_closed predictionUnary' observationUnary' residualRoute'
  have innovationUnary' : UnaryHistory innovation' :=
    unary_cont_closed covarianceUnary' observationUnary' innovationRoute'
  have covariancePosteriorUnary' : UnaryHistory covariancePosterior' :=
    unary_cont_closed updateUnary' posteriorUnary' covariancePosteriorRoute'
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed posteriorUnary' covariancePosteriorUnary' endpointRoute'
  have samePrediction : hsame prediction prediction' :=
    cont_respects_hsame samePrior sameTransition predictionRoute predictionRoute'
  have sameResidual : hsame residual residual' :=
    cont_respects_hsame samePrediction sameObservation residualRoute residualRoute'
  have sameInnovation : hsame innovation innovation' :=
    cont_respects_hsame sameCovariance sameObservation innovationRoute innovationRoute'
  have sameCovariancePosterior : hsame covariancePosterior covariancePosterior' :=
    cont_respects_hsame sameUpdate samePosterior covariancePosteriorRoute
      covariancePosteriorRoute'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame samePosterior sameCovariancePosterior endpointRoute
      endpointRoute'
  constructor
  · exact
      ⟨priorUnary', transitionUnary', predictionUnary', observationUnary', residualUnary',
        covarianceUnary', gainUnary', posteriorUnary', innovationUnary', updateUnary',
        covariancePosteriorUnary', provenanceUnary', endpointUnary', predictionRoute',
        residualRoute', innovationRoute', updateRoute', posteriorRoute', covariancePosteriorRoute',
        endpointRoute', pkgSig'⟩
  · exact And.intro samePrediction
      (And.intro sameResidual
        (And.intro sameInnovation
          (And.intro sameUpdate (And.intro sameCovariancePosterior sameEndpoint))))

theorem KalmanFilterCarrier_downstream_consumer_boundary [AskSetup] [PackageSetup]
    {prior transition prediction observation residual covariance gain posterior innovation update
      covariancePosterior provenance endpoint predictionConsumer updateConsumer finalConsumer
      finalConsumer' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KalmanFilterCarrier prior transition prediction observation residual covariance gain posterior
        innovation update covariancePosterior provenance endpoint bundle pkg ->
      Cont prediction residual predictionConsumer ->
        Cont update posterior updateConsumer ->
          Cont predictionConsumer updateConsumer finalConsumer ->
            hsame finalConsumer finalConsumer' ->
              UnaryHistory finalConsumer' ∧
                hsame finalConsumer' (append (append prediction residual) (append update posterior)) ∧
                  Cont posterior covariancePosterior endpoint ∧ PkgSig bundle endpoint pkg := by
  intro carrier predictionConsumerRow updateConsumerRow finalConsumerRow sameFinal
  rcases carrier with
    ⟨_priorUnary, _transitionUnary, predictionUnary, _observationUnary, residualUnary,
      _covarianceUnary, _gainUnary, posteriorUnary, _innovationUnary, updateUnary,
      covariancePosteriorUnary, _provenanceUnary, _endpointUnary, _predictionRow,
      _residualRow, _innovationRow, _updateRow, _posteriorRow, _covariancePosteriorRow,
      endpointRow, pkgSig⟩
  have predictionConsumerUnary : UnaryHistory predictionConsumer :=
    unary_cont_closed predictionUnary residualUnary predictionConsumerRow
  have updateConsumerUnary : UnaryHistory updateConsumer :=
    unary_cont_closed updateUnary posteriorUnary updateConsumerRow
  have finalConsumerUnary : UnaryHistory finalConsumer :=
    unary_cont_closed predictionConsumerUnary updateConsumerUnary finalConsumerRow
  have finalConsumerUnary' : UnaryHistory finalConsumer' :=
    unary_transport finalConsumerUnary sameFinal
  have sameFinalAppend : hsame finalConsumer' (append (append prediction residual)
      (append update posterior)) := by
    cases predictionConsumerRow
    cases updateConsumerRow
    cases finalConsumerRow
    cases sameFinal
    rfl
  exact And.intro finalConsumerUnary'
    (And.intro sameFinalAppend (And.intro endpointRow pkgSig))

end BEDC.Derived.KalmanFilterUp
