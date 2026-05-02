import BEDC.Derived.FieldUp.RatContinuation

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

theorem FieldRatDenominatorUnitEnvelopeClassifier_empty_right_iff {h : BHist} :
    FieldRatDenominatorUnitEnvelopeClassifier h BHist.Empty ↔ hsame h BHist.Empty := by
  constructor
  · intro classified
    cases classified with
    | inl ratData =>
        exact False.elim (RatHistoryCarrier_not_empty ratData.right.left (hsame_refl BHist.Empty))
    | inr emptyData =>
        exact emptyData.left
  · intro sameEmpty
    exact Or.inr ⟨sameEmpty, hsame_refl BHist.Empty⟩

theorem FieldRatDenominatorUnitEnvelopeClassifier_continuation_closed
    {h h' k k' r r' : BHist} :
    FieldRatDenominatorUnitEnvelopeClassifier h h' ->
      FieldRatDenominatorUnitEnvelopeClassifier k k' ->
        Cont h k r -> Cont h' k' r' ->
          FieldRatDenominatorUnitEnvelopeClassifier r r' := by
  intro classifiedH classifiedK leftContinuation rightContinuation
  cases classifiedH with
  | inl ratH =>
      cases classifiedK with
      | inl ratK =>
          have classifiedRR' : RatHistoryClassifier r r' :=
            field_rat_denominator_continuation_binary_classifier_congruence
              ratH.right.right ratK.right.right leftContinuation rightContinuation
          exact Or.inl ⟨classifiedRR'.left, classifiedRR'.right.left, classifiedRR'⟩
      | inr emptyK =>
          have sameRR' : hsame r r' :=
            cont_respects_hsame ratH.right.right.right.right
              (hsame_trans emptyK.left (hsame_symm emptyK.right))
              leftContinuation rightContinuation
          have sameRH : hsame r h :=
            cont_respects_hsame (hsame_refl h) emptyK.left leftContinuation
              (cont_right_unit h)
          have sameR'H' : hsame r' h' :=
            cont_respects_hsame (hsame_refl h') emptyK.right rightContinuation
              (cont_right_unit h')
          have carrierR : RatHistoryCarrier r :=
            RatHistoryCarrier_hsame_transport (hsame_symm sameRH) ratH.left
          have carrierR' : RatHistoryCarrier r' :=
            RatHistoryCarrier_hsame_transport (hsame_symm sameR'H') ratH.right.left
          exact Or.inl ⟨carrierR, carrierR', carrierR, carrierR', sameRR'⟩
  | inr emptyH =>
      cases classifiedK with
      | inl ratK =>
          have sameRR' : hsame r r' :=
            cont_respects_hsame
              (hsame_trans emptyH.left (hsame_symm emptyH.right))
              ratK.right.right.right.right leftContinuation rightContinuation
          have sameRK : hsame r k :=
            cont_respects_hsame emptyH.left (hsame_refl k) leftContinuation
              (cont_left_unit k)
          have sameR'K' : hsame r' k' :=
            cont_respects_hsame emptyH.right (hsame_refl k') rightContinuation
              (cont_left_unit k')
          have carrierR : RatHistoryCarrier r :=
            RatHistoryCarrier_hsame_transport (hsame_symm sameRK) ratK.left
          have carrierR' : RatHistoryCarrier r' :=
            RatHistoryCarrier_hsame_transport (hsame_symm sameR'K') ratK.right.left
          exact Or.inl ⟨carrierR, carrierR', carrierR, carrierR', sameRR'⟩
      | inr emptyK =>
          have emptyR : hsame r BHist.Empty :=
            cont_respects_hsame emptyH.left emptyK.left leftContinuation
              (cont_left_unit BHist.Empty)
          have emptyR' : hsame r' BHist.Empty :=
            cont_respects_hsame emptyH.right emptyK.right rightContinuation
              (cont_left_unit BHist.Empty)
          exact Or.inr ⟨emptyR, emptyR'⟩

end BEDC.Derived.FieldUp
