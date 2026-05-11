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
    (prior predicted covariance observation innovation gain posterior covariancePosterior provenance
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory prior ∧
    UnaryHistory predicted ∧
      UnaryHistory covariance ∧
        UnaryHistory observation ∧
          UnaryHistory innovation ∧
            UnaryHistory gain ∧
              UnaryHistory posterior ∧
                UnaryHistory covariancePosterior ∧
                  UnaryHistory provenance ∧
                    UnaryHistory endpoint ∧
                      Cont prior covariance predicted ∧
                        Cont predicted observation innovation ∧
                          Cont innovation gain posterior ∧
                            Cont posterior covariancePosterior endpoint ∧
                              PkgSig bundle endpoint pkg

theorem KalmanFilterCarrier_estimate_transport [AskSetup] [PackageSetup]
    {prior predicted covariance observation innovation gain posterior covariancePosterior provenance
      endpoint prior' predicted' covariance' observation' innovation' gain' posterior'
      covariancePosterior' provenance' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KalmanFilterCarrier prior predicted covariance observation innovation gain posterior
        covariancePosterior provenance endpoint bundle pkg ->
      hsame prior prior' ->
        hsame covariance covariance' ->
          hsame observation observation' ->
            hsame gain gain' ->
              hsame covariancePosterior covariancePosterior' ->
                hsame provenance provenance' ->
                  Cont prior' covariance' predicted' ->
                    Cont predicted' observation' innovation' ->
                      Cont innovation' gain' posterior' ->
                        Cont posterior' covariancePosterior' endpoint' ->
                          PkgSig bundle endpoint' pkg ->
                            KalmanFilterCarrier prior' predicted' covariance' observation'
                                innovation' gain' posterior' covariancePosterior' provenance'
                                endpoint' bundle pkg ∧
                              hsame predicted predicted' ∧
                                hsame innovation innovation' ∧
                                  hsame posterior posterior' ∧ hsame endpoint endpoint' := by
  intro carrier samePrior sameCovariance sameObservation sameGain sameCovariancePosterior
    sameProvenance predictedRow' innovationRow' posteriorRow' endpointRow' pkgSig'
  have priorUnary' : UnaryHistory prior' :=
    unary_transport carrier.left samePrior
  have covarianceUnary' : UnaryHistory covariance' :=
    unary_transport carrier.right.right.left sameCovariance
  have observationUnary' : UnaryHistory observation' :=
    unary_transport carrier.right.right.right.left sameObservation
  have gainUnary' : UnaryHistory gain' :=
    unary_transport carrier.right.right.right.right.right.left sameGain
  have covariancePosteriorUnary' : UnaryHistory covariancePosterior' :=
    unary_transport carrier.right.right.right.right.right.right.right.left
      sameCovariancePosterior
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport carrier.right.right.right.right.right.right.right.right.left sameProvenance
  have predictedUnary' : UnaryHistory predicted' :=
    unary_cont_closed priorUnary' covarianceUnary' predictedRow'
  have innovationUnary' : UnaryHistory innovation' :=
    unary_cont_closed predictedUnary' observationUnary' innovationRow'
  have posteriorUnary' : UnaryHistory posterior' :=
    unary_cont_closed innovationUnary' gainUnary' posteriorRow'
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed posteriorUnary' covariancePosteriorUnary' endpointRow'
  have samePredicted : hsame predicted predicted' :=
    cont_respects_hsame samePrior sameCovariance
      carrier.right.right.right.right.right.right.right.right.right.right.left predictedRow'
  have sameInnovation : hsame innovation innovation' :=
    cont_respects_hsame samePredicted sameObservation
      carrier.right.right.right.right.right.right.right.right.right.right.right.left
      innovationRow'
  have samePosterior : hsame posterior posterior' :=
    cont_respects_hsame sameInnovation sameGain
      carrier.right.right.right.right.right.right.right.right.right.right.right.right.left
      posteriorRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame samePosterior sameCovariancePosterior
      carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.left
      endpointRow'
  have targetCarrier :
      KalmanFilterCarrier prior' predicted' covariance' observation' innovation' gain'
        posterior' covariancePosterior' provenance' endpoint' bundle pkg :=
    ⟨priorUnary', predictedUnary', covarianceUnary', observationUnary', innovationUnary',
      gainUnary', posteriorUnary', covariancePosteriorUnary', provenanceUnary', endpointUnary',
      predictedRow', innovationRow', posteriorRow', endpointRow', pkgSig'⟩
  exact And.intro targetCarrier
    (And.intro samePredicted
      (And.intro sameInnovation (And.intro samePosterior sameEndpoint)))

end BEDC.Derived.KalmanFilterUp
