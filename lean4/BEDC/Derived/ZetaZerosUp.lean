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

def ZetaZeroPatternSpec (s z : BHist) : Prop :=
  ZetaZeroSourceSpec s ∧ hsame z (append (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty))

theorem ZetaZeroSourceSpec_zero_classifier {s : BHist} :
    ZetaZeroSourceSpec s ->
      ComplexHistoryClassifier s (append (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty)) := by
  intro source
  exact And.intro source.left
    (And.intro ZetaZeroComplexHistory_carrier source.right)

theorem ZetaZeroPatternSpec_zero_result_classifier {s z : BHist} :
    ZetaZeroPatternSpec s z ->
      ComplexHistoryClassifier z (append (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty)) := by
  intro pattern
  have carrierZ : ComplexHistoryCarrier z :=
    ProdHistoryCarrier_hsame_transport (hsame_symm pattern.right) ZetaZeroComplexHistory_carrier
  exact And.intro carrierZ
    (And.intro ZetaZeroComplexHistory_carrier pattern.right)

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

theorem ZetaZeroPatternSpec_hsame_transport_classifier {s t z w : BHist} :
    hsame s t -> hsame z w -> ZetaZeroPatternSpec s z ->
      ZetaZeroPatternSpec t w ∧
        ComplexHistoryClassifier w (append (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty)) := by
  intro sameST sameZW pattern
  have sourceT : ZetaZeroSourceSpec t :=
    (ZetaZeroSourceSpec_hsame_transport_classifier sameST pattern.left).left
  have sameWZero : hsame w (append (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty)) :=
    hsame_trans (hsame_symm sameZW) pattern.right
  have patternTW : ZetaZeroPatternSpec t w :=
    And.intro sourceT sameWZero
  exact And.intro patternTW (ZetaZeroPatternSpec_zero_result_classifier patternTW)

theorem ZetaZeroSourceSpec_zero_anchor_unique {s t : BHist} :
    ZetaZeroSourceSpec s ->
      ZetaZeroSourceSpec t ->
        hsame s t ∧
          hsame s (append (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty)) ∧
            hsame t (append (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty)) := by
  intro sourceS sourceT
  exact And.intro (hsame_trans sourceS.right (hsame_symm sourceT.right))
    (And.intro sourceS.right sourceT.right)

theorem ZetaZeroSourceSpec_pair_classifier {s t : BHist} :
    ZetaZeroSourceSpec s -> ZetaZeroSourceSpec t ->
      ComplexHistoryClassifier s t ∧
        hsame s (append (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty)) ∧
          hsame t (append (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty)) := by
  intro sourceS sourceT
  have sameST : hsame s t := hsame_trans sourceS.right (hsame_symm sourceT.right)
  exact And.intro (And.intro sourceS.left (And.intro sourceT.left sameST))
    (And.intro sourceS.right sourceT.right)

theorem ZetaZeroPatternSpec_pair_classifier {s t z w : BHist} :
    ZetaZeroPatternSpec s z -> ZetaZeroPatternSpec t w ->
      ComplexHistoryClassifier s t ∧ ComplexHistoryClassifier z w ∧
        hsame s (append (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty)) ∧
          hsame t (append (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty)) ∧
            hsame z (append (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty)) ∧
              hsame w (append (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty)) := by
  intro patternSZ patternTW
  have sourcePair := ZetaZeroSourceSpec_pair_classifier patternSZ.left patternTW.left
  have zZero := ZetaZeroPatternSpec_zero_result_classifier patternSZ
  have wZero := ZetaZeroPatternSpec_zero_result_classifier patternTW
  have classifiedZW : ComplexHistoryClassifier z w :=
    ComplexHistoryClassifier_trans zZero (ComplexHistoryClassifier_symm wZero)
  exact And.intro sourcePair.left
    (And.intro classifiedZW
      (And.intro sourcePair.right.left
        (And.intro sourcePair.right.right
          (And.intro patternSZ.right patternTW.right))))

end BEDC.Derived.ZetaZerosUp
