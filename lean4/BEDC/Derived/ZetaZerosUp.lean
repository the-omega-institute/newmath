import BEDC.Derived.ComplexUp

namespace BEDC.Derived.ZetaZerosUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.FKernel.NameCert
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

def ZetaBoundaryNonvanishingWitness (s sigma : BHist) : Prop :=
  ComplexHistoryCarrier s ∧ RatHistoryCarrier sigma ∧ hsame sigma (BHist.e1 BHist.Empty) ∧
    ∃ imag : BHist, RatHistoryCarrier imag ∧ Cont sigma imag s ∧ (ZetaZeroSourceSpec s -> False)

theorem ZetaBoundaryNonvanishingWitness_sigma_nonempty {s sigma : BHist} :
    ZetaBoundaryNonvanishingWitness s sigma -> (hsame sigma BHist.Empty -> False) := by
  intro witness sameEmpty
  have sameUnit : hsame sigma (BHist.e1 BHist.Empty) := witness.right.right.left
  have unitEmpty : hsame (BHist.e1 BHist.Empty) BHist.Empty :=
    hsame_trans (hsame_symm sameUnit) sameEmpty
  exact not_hsame_e1_empty unitEmpty

def ZetaZeroPatternSpec (s z : BHist) : Prop :=
  ZetaZeroSourceSpec s ∧ hsame z (append (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty))

def ZetaZeroClassifierSpec (s t : BHist) : Prop :=
  ZetaZeroSourceSpec s ∧ ZetaZeroSourceSpec t ∧ hsame s t ∧
    hsame s (append (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty)) ∧
      hsame t (append (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty))

theorem ZetaZeroClassifierSpec_zero_anchor_pair {s t : BHist} :
    ZetaZeroClassifierSpec s t ->
      hsame s t ∧
        hsame s (append (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty)) ∧
          hsame t (append (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty)) := by
  intro classifier
  exact And.intro classifier.right.right.left
    (And.intro classifier.right.right.right.left classifier.right.right.right.right)

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

theorem ZetaZeroPatternSpec_source_result_classifier {s z : BHist} :
    ZetaZeroPatternSpec s z ->
      ComplexHistoryClassifier s z ∧
        hsame s (append (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty)) ∧
          hsame z (append (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty)) := by
  intro pattern
  have resultClassifier := ZetaZeroPatternSpec_zero_result_classifier pattern
  have sameSourceResult : hsame s z :=
    hsame_trans pattern.left.right (hsame_symm pattern.right)
  exact And.intro (And.intro pattern.left.left (And.intro resultClassifier.left sameSourceResult))
    (And.intro pattern.left.right pattern.right)

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

theorem ZetaZeroSourceSpec_name_certificate :
    NameCert ZetaZeroSourceSpec ComplexHistoryClassifier := by
  constructor
  · exact Exists.intro (append (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty))
      (And.intro ZetaZeroComplexHistory_carrier (hsame_refl _))
  · intro s source
    exact And.intro source.left (And.intro source.left (hsame_refl s))
  · intro s t classified
    exact ComplexHistoryClassifier_symm classified
  · intro s t u classifiedST classifiedTU
    exact ComplexHistoryClassifier_trans classifiedST classifiedTU
  · intro s t classified source
    exact (ZetaZeroSourceSpec_hsame_transport_classifier classified.right.right source).left

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

theorem ZetaZeros_semanticNameCert :
    SemanticNameCert ZetaZeroSourceSpec
      (fun h : BHist => exists z : BHist, ZetaZeroPatternSpec h z)
      ZetaZeroSourceSpec ComplexHistoryClassifier := by
  constructor
  · constructor
    · exact Exists.intro (append (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty))
        (And.intro ZetaZeroComplexHistory_carrier
          (hsame_refl (append (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty))))
    · intro h source
      exact And.intro source.left (And.intro source.left (hsame_refl h))
    · intro h k classified
      exact ComplexHistoryClassifier_symm classified
    · intro h k r classifiedHK classifiedKR
      exact ComplexHistoryClassifier_trans classifiedHK classifiedKR
    · intro h k classified source
      exact And.intro classified.right.left
        (hsame_trans (hsame_symm classified.right.right) source.right)
  · intro h source
    exact Exists.intro (append (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty))
      (And.intro source
        (hsame_refl (append (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty))))
  · intro h source
    exact source

end BEDC.Derived.ZetaZerosUp
