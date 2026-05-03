import BEDC.Derived.FieldUp.RatDenomUnit

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem RatDenomUnitClassifier_contextual_product_rat_classifier_iff
    {p q p' q' h k h' k' : BHist} :
    hsame p BHist.Empty -> hsame q BHist.Empty -> hsame p' BHist.Empty ->
      hsame q' BHist.Empty -> RatDenomUnitClassifier h h' ->
        RatDenomUnitClassifier k k' ->
          (RatHistoryClassifier (append p (append (append h k) q))
            (append p' (append (append h' k') q')) ↔ RatHistoryCarrier (append h k)) := by
  intro sameP sameQ sameP' sameQ' classifiedH classifiedK
  have leftContextSame :
      hsame (append p (append (append h k) q)) (append h k) := by
    cases sameP
    cases sameQ
    exact hsame_trans (append_empty_left (append (append h k) BHist.Empty))
      (append_empty_right (append h k))
  have rightContextSame :
      hsame (append p' (append (append h' k') q')) (append h' k') := by
    cases sameP'
    cases sameQ'
    exact hsame_trans (append_empty_left (append (append h' k') BHist.Empty))
      (append_empty_right (append h' k'))
  have productClassified : RatDenomUnitClassifier (append h k) (append h' k') :=
    field_rat_denominator_empty_unit_continuation_monoid_laws.right.right.right.right
      classifiedH classifiedK
  constructor
  · intro contextualClassifier
    exact RatHistoryCarrier_hsame_transport leftContextSame contextualClassifier.left
  · intro productCarrier
    have productCarrier' : RatHistoryCarrier (append h' k') :=
      RatHistoryCarrier_hsame_transport productClassified.right.right productCarrier
    have productClassifier : RatHistoryClassifier (append h k) (append h' k') :=
      And.intro productCarrier (And.intro productCarrier' productClassified.right.right)
    exact RatHistoryClassifier_hsame_transport (hsame_symm leftContextSame)
      (hsame_symm rightContextSame) productClassifier

end BEDC.Derived.FieldUp
