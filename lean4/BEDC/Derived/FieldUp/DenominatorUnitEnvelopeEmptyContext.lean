import BEDC.Derived.FieldUp.DenominatorUnitEnvelope

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

theorem FieldRatDenominatorUnitEnvelopeClassifier_empty_context_hsame_iff {h k : BHist} :
    FieldRatDenominatorUnitEnvelopeCarrier h -> FieldRatDenominatorUnitEnvelopeCarrier k ->
      (FieldRatDenominatorUnitEnvelopeClassifier (append BHist.Empty h) (append k BHist.Empty) <->
        hsame h k) := by
  intro carrierH carrierK
  constructor
  · intro classified
    cases carrierH with
    | inl ratH =>
        cases carrierK with
        | inl _ratK =>
            cases classified with
            | inl ratData =>
                have coreClassifier : RatHistoryClassifier h k :=
                  RatHistoryClassifier_hsame_transport (append_empty_left h) (append_empty_right k)
                    ratData.right.right
                exact coreClassifier.right.right
            | inr emptyData =>
                have hEmpty : hsame h BHist.Empty :=
                  hsame_trans (hsame_symm (append_empty_left h)) emptyData.left
                exact False.elim (RatHistoryCarrier_not_empty ratH hEmpty)
        | inr emptyK =>
            cases classified with
            | inl ratData =>
                have kEmpty : hsame k BHist.Empty :=
                  emptyK
                have appendKEmpty : hsame (append k BHist.Empty) BHist.Empty :=
                  hsame_trans (append_empty_right k) kEmpty
                exact False.elim (RatHistoryCarrier_not_empty ratData.right.left appendKEmpty)
            | inr emptyData =>
                have hEmpty : hsame h BHist.Empty :=
                  hsame_trans (hsame_symm (append_empty_left h)) emptyData.left
                have kEmpty : hsame k BHist.Empty :=
                  hsame_trans (hsame_symm (append_empty_right k)) emptyData.right
                exact hsame_trans hEmpty (hsame_symm kEmpty)
    | inr emptyH =>
        cases carrierK with
        | inl ratK =>
            cases classified with
            | inl ratData =>
                have hEmpty : hsame (append BHist.Empty h) BHist.Empty :=
                  hsame_trans (append_empty_left h) emptyH
                exact False.elim (RatHistoryCarrier_not_empty ratData.left hEmpty)
            | inr emptyData =>
                have kEmpty : hsame k BHist.Empty :=
                  hsame_trans (hsame_symm (append_empty_right k)) emptyData.right
                exact False.elim (RatHistoryCarrier_not_empty ratK kEmpty)
        | inr emptyK =>
            exact hsame_trans emptyH (hsame_symm emptyK)
  · intro sameHK
    cases carrierH with
    | inl ratH =>
        cases carrierK with
        | inl ratK =>
            have coreClassifier : RatHistoryClassifier h k :=
              ⟨ratH, ratK, sameHK⟩
            have contextClassifier :
                RatHistoryClassifier (append BHist.Empty h) (append k BHist.Empty) :=
              RatHistoryClassifier_hsame_transport (hsame_symm (append_empty_left h))
                (hsame_symm (append_empty_right k)) coreClassifier
            exact Or.inl
              ⟨contextClassifier.left, contextClassifier.right.left, contextClassifier⟩
        | inr emptyK =>
            exact False.elim
              (RatHistoryCarrier_not_empty ratH (hsame_trans sameHK emptyK))
    | inr emptyH =>
        cases carrierK with
        | inl ratK =>
            exact False.elim
              (RatHistoryCarrier_not_empty ratK (hsame_trans (hsame_symm sameHK) emptyH))
        | inr emptyK =>
            exact Or.inr
              ⟨hsame_trans (append_empty_left h) emptyH,
                hsame_trans (append_empty_right k) emptyK⟩

end BEDC.Derived.FieldUp
