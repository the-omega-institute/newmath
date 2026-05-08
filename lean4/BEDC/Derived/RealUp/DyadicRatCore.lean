import BEDC.Derived.RealUp.Core

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

theorem DyadicRatCoreObservationRow_public_hsame_transport {d d' radius : BHist} :
    DyadicRatCoreObservationRow d radius -> hsame d d' ->
      DyadicRatCoreObservationRow d' radius ∧ RealConstantHistoryCarrier (BHist.e1 d') ∧
        hsame (BHist.e1 d) (BHist.e1 d') ∧ PositiveUnaryDenominator d' ∧
          UnaryHistory radius := by
  intro row sameD
  have row' : DyadicRatCoreObservationRow d' radius :=
    And.intro (RatHistoryCarrier_hsame_transport sameD row.left)
      (And.intro (PositiveUnaryDenominator_hsame_transport sameD row.right.left)
        row.right.right)
  have realCarrier : RealConstantHistoryCarrier (BHist.e1 d') :=
    RealConstantHistoryCarrier_e1_iff_rat.mpr row'.left
  have sameReal : hsame (BHist.e1 d) (BHist.e1 d') :=
    hsame_e1_congr sameD
  exact And.intro row'
    (And.intro realCarrier
      (And.intro sameReal (And.intro row'.right.left row'.right.right)))

theorem DyadicRatCoreObservationRow_realup_window_feed
    {d e d' e' radiusD radiusE : BHist} :
    DyadicRatCoreObservationRow d radiusD -> DyadicRatCoreObservationRow e radiusE ->
      RatHistoryClassifier d e -> hsame d d' -> hsame e e' ->
        RealConstantHistoryCarrier (BHist.e1 d') ∧
          RealConstantHistoryCarrier (BHist.e1 e') ∧
            RealConstantHistoryClassifier (BHist.e1 d') (BHist.e1 e') ∧
              PositiveUnaryDenominator d' ∧ PositiveUnaryDenominator e' ∧
                UnaryHistory radiusD ∧ UnaryHistory radiusE ∧ hsame d' e' := by
  intro rowD rowE classified sameD sameE
  have transported :=
    DyadicRatCoreObservationRow_classifier_transport rowD rowE classified sameD sameE
  have rowD' : DyadicRatCoreObservationRow d' radiusD := transported.left
  have rowE' : DyadicRatCoreObservationRow e' radiusE := transported.right.left
  have classified' : RatHistoryClassifier d' e' := transported.right.right
  have realCarrierD : RealConstantHistoryCarrier (BHist.e1 d') :=
    RealConstantHistoryCarrier_e1_iff_rat.mpr rowD'.left
  have realCarrierE : RealConstantHistoryCarrier (BHist.e1 e') :=
    RealConstantHistoryCarrier_e1_iff_rat.mpr rowE'.left
  have realClassifier : RealConstantHistoryClassifier (BHist.e1 d') (BHist.e1 e') :=
    RealConstantHistoryClassifier_e1_iff_rat.mpr classified'
  exact And.intro realCarrierD
    (And.intro realCarrierE
      (And.intro realClassifier
        (And.intro rowD'.right.left
        (And.intro rowE'.right.left
          (And.intro rowD'.right.right
            (And.intro rowE'.right.right classified'.right.right))))))

theorem RegSeqRatDyadicLedger_real_seal_obligation {d e d' e' radiusD radiusE : BHist} :
    DyadicRatCoreObservationRow d radiusD -> DyadicRatCoreObservationRow e radiusE ->
      RatHistoryClassifier d e -> hsame d d' -> hsame e e' ->
        RealConstantHistoryCarrier (BHist.e1 d') ∧
          RealConstantHistoryCarrier (BHist.e1 e') ∧
            RealConstantHistoryClassifier (BHist.e1 d') (BHist.e1 e') ∧
              PositiveUnaryDenominator d' ∧ PositiveUnaryDenominator e' ∧
                UnaryHistory radiusD ∧ UnaryHistory radiusE ∧ hsame d' e' ∧
                  DyadicRatCoreObservationRow d' radiusD ∧
                    DyadicRatCoreObservationRow e' radiusE := by
  intro rowD rowE classified sameD sameE
  have feed :=
    DyadicRatCoreObservationRow_realup_window_feed rowD rowE classified sameD sameE
  have transported :=
    DyadicRatCoreObservationRow_classifier_transport rowD rowE classified sameD sameE
  exact And.intro feed.left
    (And.intro feed.right.left
      (And.intro feed.right.right.left
        (And.intro feed.right.right.right.left
          (And.intro feed.right.right.right.right.left
            (And.intro feed.right.right.right.right.right.left
              (And.intro feed.right.right.right.right.right.right.left
                (And.intro feed.right.right.right.right.right.right.right
                  (And.intro transported.left transported.right.left))))))))

end BEDC.Derived.RealUp
