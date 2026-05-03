import BEDC.Derived.ComplexUp

namespace BEDC.Derived.ComplexAnalyticUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexUp
open BEDC.Derived.ProdUp
open BEDC.Derived.RatUp

def CplxPureImaginary (theta z : BHist) : Prop :=
  UnaryHistory theta ∧ hsame z (append (BHist.e1 BHist.Empty) (BHist.e1 theta))

theorem CplxPureImaginary_complex_carrier_witness {theta z : BHist} :
    CplxPureImaginary theta z ->
      UnaryHistory theta ∧ hsame z (append (BHist.e1 BHist.Empty) (BHist.e1 theta)) ∧
        ComplexHistoryCarrier z := by
  intro pureImaginary
  cases pureImaginary with
  | intro thetaUnary sameZ =>
      have realCarrier : RatHistoryCarrier (BHist.e1 BHist.Empty) := by
        exact RatHistoryCarrier_iff_positive_denominator.mpr
          (PositiveUnaryDenominator_e1_iff_unary.mpr unary_empty)
      have imagCarrier : RatHistoryCarrier (BHist.e1 theta) := by
        exact RatHistoryCarrier_iff_positive_denominator.mpr
          (PositiveUnaryDenominator_e1_iff_unary.mpr thetaUnary)
      have pureCarrier :
          ComplexHistoryCarrier (append (BHist.e1 BHist.Empty) (BHist.e1 theta)) := by
        exact ProdHistoryCarrier_append_intro realCarrier imagCarrier
      exact And.intro thetaUnary
        (And.intro sameZ
          (ProdHistoryCarrier_hsame_transport (hsame_symm sameZ) pureCarrier))

end BEDC.Derived.ComplexAnalyticUp
