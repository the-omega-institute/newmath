import BEDC.Derived.RatUp

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

def DyadicRatCoreObservationRow (d radius : BHist) : Prop :=
  RatHistoryCarrier d ∧ PositiveUnaryDenominator d ∧ UnaryHistory radius

theorem DyadicRatCoreObservationRow_classifier_transport
    {d e d' e' radiusD radiusE : BHist} :
    DyadicRatCoreObservationRow d radiusD -> DyadicRatCoreObservationRow e radiusE ->
      RatHistoryClassifier d e -> hsame d d' -> hsame e e' ->
        DyadicRatCoreObservationRow d' radiusD ∧
          DyadicRatCoreObservationRow e' radiusE ∧ RatHistoryClassifier d' e' := by
  intro rowD rowE classified sameD sameE
  have classified' : RatHistoryClassifier d' e' :=
    RatHistoryClassifier_hsame_transport sameD sameE classified
  have rowD' : DyadicRatCoreObservationRow d' radiusD :=
    And.intro (RatHistoryCarrier_hsame_transport sameD rowD.left)
      (And.intro (PositiveUnaryDenominator_hsame_transport sameD rowD.right.left)
        rowD.right.right)
  have rowE' : DyadicRatCoreObservationRow e' radiusE :=
    And.intro (RatHistoryCarrier_hsame_transport sameE rowE.left)
      (And.intro (PositiveUnaryDenominator_hsame_transport sameE rowE.right.left)
        rowE.right.right)
  exact And.intro rowD' (And.intro rowE' classified')

end BEDC.Derived.RealUp
