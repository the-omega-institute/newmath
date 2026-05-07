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

end BEDC.Derived.IntegralUp
