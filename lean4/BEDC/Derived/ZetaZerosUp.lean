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

theorem ZetaZeroSourceSpec_hsame_transport_classifier {s t : BHist} :
    hsame s t ->
      ZetaZeroSourceSpec s ->
        ZetaZeroSourceSpec t ∧
          ComplexHistoryClassifier t
            (append (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty)) := by
  intro sameST source
  have carrierT : ComplexHistoryCarrier t :=
    ProdHistoryCarrier_hsame_transport sameST source.left
  have sameTZero : hsame t (append (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty)) :=
    hsame_trans (hsame_symm sameST) source.right
  have sourceT : ZetaZeroSourceSpec t :=
    And.intro carrierT sameTZero
  exact And.intro sourceT (ZetaZeroSourceSpec_zero_classifier sourceT)

end BEDC.Derived.ZetaZerosUp
