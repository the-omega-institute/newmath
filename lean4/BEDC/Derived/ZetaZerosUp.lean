import BEDC.Derived.ComplexUp

namespace BEDC.Derived.ZetaZerosUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexUp
open BEDC.Derived.ProdUp
open BEDC.Derived.RatUp

theorem ZetaZeroComplexHistory_carrier :
    ComplexHistoryCarrier (append (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty)) := by
  have ratUnit : RatHistoryCarrier (BHist.e1 BHist.Empty) := by
    exact RatHistoryCarrier_iff_positive_denominator.mpr
      (PositiveUnaryDenominator_e1_iff_unary.mpr unary_empty)
  exact ProdHistoryCarrier_append_intro ratUnit ratUnit

def ZetaZeroSourceSpec (s : BHist) : Prop :=
  ComplexHistoryCarrier s ∧ hsame s (append (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty))

theorem ZetaZeroSourceSpec_zero_classifier {s : BHist} :
    ZetaZeroSourceSpec s ->
      ComplexHistoryClassifier s (append (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty)) := by
  intro source
  exact And.intro source.left
    (And.intro ZetaZeroComplexHistory_carrier source.right)

end BEDC.Derived.ZetaZerosUp
