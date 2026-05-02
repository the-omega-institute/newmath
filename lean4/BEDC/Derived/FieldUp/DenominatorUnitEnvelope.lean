import BEDC.Derived.FieldUp.RatContinuation

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem field_rat_denominator_unit_envelope_classifier_append_closed {h h' k k' : BHist} :
    ((RatHistoryCarrier h ∧ RatHistoryCarrier h' ∧ RatHistoryClassifier h h') ∨
        (hsame h BHist.Empty ∧ hsame h' BHist.Empty)) ->
      ((RatHistoryCarrier k ∧ RatHistoryCarrier k' ∧ RatHistoryClassifier k k') ∨
        (hsame k BHist.Empty ∧ hsame k' BHist.Empty)) ->
        ((RatHistoryCarrier (append h k) ∧ RatHistoryCarrier (append h' k') ∧
            RatHistoryClassifier (append h k) (append h' k')) ∨
          (hsame (append h k) BHist.Empty ∧ hsame (append h' k') BHist.Empty)) := by
  intro left right
  cases left with
  | inl leftCarried =>
      cases right with
      | inl rightCarried =>
          apply Or.inl
          have rightClassifier : RatHistoryClassifier k k' := rightCarried.right.right
          have tailSame : hsame k k' := rightClassifier.right.right
          have tailUnary : UnaryHistory k :=
            (PositiveUnaryDenominator_unary_and_nonempty
              (RatHistoryCarrier_iff_positive_denominator.mp rightCarried.left)).left
          have appendedClassifier :
              RatHistoryClassifier (append h k) (append h' k') :=
            RatHistoryClassifier_append_unary_denominator_closed leftCarried.right.right
              tailUnary tailSame
          exact And.intro appendedClassifier.left
            (And.intro appendedClassifier.right.left appendedClassifier)
      | inr rightEmpty =>
          apply Or.inl
          cases rightEmpty.left
          cases rightEmpty.right
          have appendedClassifier :
              RatHistoryClassifier (append h BHist.Empty) (append h' BHist.Empty) :=
            RatHistoryClassifier_hsame_transport
              (hsame_symm (append_empty_right h)) (hsame_symm (append_empty_right h'))
              leftCarried.right.right
          exact And.intro appendedClassifier.left
            (And.intro appendedClassifier.right.left appendedClassifier)
  | inr leftEmpty =>
      cases right with
      | inl rightCarried =>
          apply Or.inl
          cases leftEmpty.left
          cases leftEmpty.right
          have appendedClassifier :
              RatHistoryClassifier (append BHist.Empty k) (append BHist.Empty k') :=
            RatHistoryClassifier_hsame_transport
              (hsame_symm (append_empty_left k)) (hsame_symm (append_empty_left k'))
              rightCarried.right.right
          exact And.intro appendedClassifier.left
            (And.intro appendedClassifier.right.left appendedClassifier)
      | inr rightEmpty =>
          apply Or.inr
          cases leftEmpty.left
          cases leftEmpty.right
          cases rightEmpty.left
          cases rightEmpty.right
          exact And.intro rfl rfl

end BEDC.Derived.FieldUp
