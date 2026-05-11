import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package

namespace BEDC.Derived.KalmanFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem KalmanFilterPredictionUpdatePacket_obligation [AskSetup] [PackageSetup]
    {prior transition prediction covariance predicted observation innovation gain update posterior
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont transition prior prediction ->
      Cont prediction covariance predicted ->
        Cont observation predicted innovation ->
          Cont gain innovation update ->
            Cont update posterior endpoint ->
              PkgSig bundle endpoint pkg ->
                hsame prediction (append transition prior) ∧
                  hsame predicted (append prediction covariance) ∧
                    hsame innovation (append observation predicted) ∧
                      hsame update (append gain innovation) ∧
                        Cont update posterior endpoint ∧ PkgSig bundle endpoint pkg := by
  intro transitionRow covarianceRow innovationRow gainRow posteriorRow packageRow
  have predictionExact : hsame prediction (append transition prior) := by
    exact transitionRow
  have predictedExact : hsame predicted (append prediction covariance) := by
    exact covarianceRow
  have innovationExact : hsame innovation (append observation predicted) := by
    exact innovationRow
  have updateExact : hsame update (append gain innovation) := by
    exact gainRow
  exact
    And.intro predictionExact
      (And.intro predictedExact
        (And.intro innovationExact
          (And.intro updateExact (And.intro posteriorRow packageRow))))

end BEDC.Derived.KalmanFilterUp
