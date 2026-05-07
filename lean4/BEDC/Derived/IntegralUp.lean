import BEDC.Derived.ContourIntegralUp
import BEDC.Derived.MeasureUp
import BEDC.Derived.RealUp.Core
import BEDC.Derived.RatUp.HistoryClassifier

namespace BEDC.Derived.IntegralUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.ContourIntegralUp
open BEDC.Derived.MeasureUp
open BEDC.Derived.RealUp
open BEDC.Derived.RatUp

def IntegralVisibleCarrierRow
    (measure contour integrand value measureContour integrandValue row : BHist) : Prop :=
  MeasureZeroBHistCarrier measure ∧
    PLContour contour ∧
      UnaryHistory integrand ∧
        RealConstantHistoryCarrier value ∧
          Cont measure contour measureContour ∧
            Cont integrand value integrandValue ∧
              Cont measureContour integrandValue row

theorem IntegralVisibleCarrierRow_readback
    {measure contour integrand value measureContour integrandValue row : BHist} :
    IntegralVisibleCarrierRow measure contour integrand value measureContour integrandValue row ->
      MeasureZeroBHistCarrier measure ∧
        PLContour contour ∧
          UnaryHistory integrand ∧
            RealConstantHistoryCarrier value ∧
              Cont measureContour integrandValue row ∧ UnaryHistory row := by
  intro carrier
  have measureUnary : UnaryHistory measure := unary_transport unary_empty (hsame_symm carrier.left)
  let rec contourUnary : {gamma : BHist} -> PLContour gamma -> UnaryHistory gamma
    | _, PLContour.segment segment =>
        by
          cases PLContourSegment_unary_result segment with
          | intro _z0 rest =>
              cases rest with
              | intro _z1 data =>
                  exact data.right.right.right
    | _, PLContour.concat leftContour rightContour join =>
        unary_cont_closed (contourUnary leftContour) (contourUnary rightContour) join
  have contourCarrier : UnaryHistory contour := contourUnary carrier.right.left
  have measureContourCarrier : UnaryHistory measureContour :=
    unary_cont_closed measureUnary contourCarrier carrier.right.right.right.right.left
  have valueUnary : UnaryHistory value := by
    cases carrier.right.right.right.left with
    | intro valueTail valueData =>
      have valueTailUnary : UnaryHistory valueTail :=
        (PositiveUnaryDenominator_unary_and_nonempty
          (RatHistoryCarrier_iff_positive_denominator.mp valueData.right)).left
      exact unary_transport (unary_e1_closed valueTailUnary) (hsame_symm valueData.left)
  have integrandValueCarrier : UnaryHistory integrandValue :=
    unary_cont_closed carrier.right.right.left valueUnary carrier.right.right.right.right.right.left
  have rowUnary : UnaryHistory row :=
    unary_cont_closed measureContourCarrier integrandValueCarrier
      carrier.right.right.right.right.right.right
  exact And.intro carrier.left
    (And.intro carrier.right.left
      (And.intro carrier.right.right.left
        (And.intro carrier.right.right.right.left
          (And.intro carrier.right.right.right.right.right.right rowUnary))))

theorem IntegralVisibleCarrierRow_measure_respecting_classifier
    {measure contour integrand value measureContour integrandValue row measure' contour'
      integrand' value' measureContour' integrandValue' row' : BHist} :
    IntegralVisibleCarrierRow measure contour integrand value measureContour integrandValue row ->
      IntegralVisibleCarrierRow measure' contour' integrand' value' measureContour'
          integrandValue' row' ->
        hsame measure measure' -> hsame contour contour' -> hsame integrand integrand' ->
          hsame value value' ->
            MeasureZeroBHistClassifier measure measure' ∧
              Cont measureContour integrandValue row ∧
                Cont measureContour' integrandValue' row' ∧
                  hsame measureContour measureContour' ∧
                    hsame integrandValue integrandValue' ∧ hsame row row' := by
  intro leftCarrier rightCarrier sameMeasure sameContour sameIntegrand sameValue
  have measureClassified : MeasureZeroBHistClassifier measure measure' :=
    And.intro leftCarrier.left (And.intro rightCarrier.left sameMeasure)
  have leftMeasureContour : Cont measure contour measureContour :=
    leftCarrier.right.right.right.right.left
  have rightMeasureContour : Cont measure' contour' measureContour' :=
    rightCarrier.right.right.right.right.left
  have sameMeasureContour : hsame measureContour measureContour' :=
    cont_respects_hsame sameMeasure sameContour leftMeasureContour rightMeasureContour
  have leftIntegrandValue : Cont integrand value integrandValue :=
    leftCarrier.right.right.right.right.right.left
  have rightIntegrandValue : Cont integrand' value' integrandValue' :=
    rightCarrier.right.right.right.right.right.left
  have sameIntegrandValue : hsame integrandValue integrandValue' :=
    cont_respects_hsame sameIntegrand sameValue leftIntegrandValue rightIntegrandValue
  have leftRow : Cont measureContour integrandValue row :=
    leftCarrier.right.right.right.right.right.right
  have rightRow : Cont measureContour' integrandValue' row' :=
    rightCarrier.right.right.right.right.right.right
  have sameRow : hsame row row' :=
    cont_respects_hsame sameMeasureContour sameIntegrandValue leftRow rightRow
  exact And.intro measureClassified
    (And.intro leftRow
      (And.intro rightRow
        (And.intro sameMeasureContour (And.intro sameIntegrandValue sameRow))))

theorem IntegralVisibleCarrierRow_measure_prefix_scope (events values : Nat -> BHist)
    {measure contour integrand value measureContour integrandValue row : BHist} :
    (forall n : Nat, MeasureZeroBHistClassifier (events n) (values n)) ->
      IntegralVisibleCarrierRow measure contour integrand value measureContour integrandValue row ->
        forall n : Nat,
          MeasureZeroBHistClassifier (MeasureZeroBHistPrefix events n)
              (MeasureZeroBHistPrefix values n) ∧
            Cont (MeasureZeroBHistPrefix events n) (events n)
              (MeasureZeroBHistPrefix events (Nat.succ n)) ∧
              Cont (MeasureZeroBHistPrefix values n) (values n)
                (MeasureZeroBHistPrefix values (Nat.succ n)) ∧
                MeasureZeroBHistCarrier measure ∧ PLContour contour ∧ UnaryHistory row := by
  intro pointwise carrier n
  have eventsZero : forall m : Nat, MeasureZeroBHistCarrier (events m) := by
    intro m
    exact (pointwise m).left
  have valuesZero : forall m : Nat, MeasureZeroBHistCarrier (values m) := by
    intro m
    exact (pointwise m).right.left
  have eventStep :=
    (MeasureZeroBHist_sigma_additivity events eventsZero n).left
  have valueStep :=
    (MeasureZeroBHist_sigma_additivity values valuesZero n).left
  have prefixClassified :=
    MeasureZeroBHistPrefix_classifier_stability events values pointwise n
  have readback := IntegralVisibleCarrierRow_readback carrier
  exact And.intro prefixClassified
    (And.intro eventStep
      (And.intro valueStep
        (And.intro readback.left
          (And.intro readback.right.left readback.right.right.right.right.right))))

end BEDC.Derived.IntegralUp
