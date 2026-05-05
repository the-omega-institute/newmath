import BEDC.Derived.FieldExtUp

namespace BEDC.Derived.FieldExtUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

def FieldExtRatReflexiveCarrier (h : BHist) : Prop :=
  RatHistoryCarrier h ∧ RatHistoryCarrier (FieldExtSingletonEmbedding h) ∧
    Cont BHist.Empty h (FieldExtSingletonEmbedding h)

theorem FieldExtRatReflexiveCarrier_rat_history_closure {h : BHist} :
    RatHistoryCarrier h -> FieldExtRatReflexiveCarrier h := by
  intro carrier
  have embeddedCarrier : RatHistoryCarrier (FieldExtSingletonEmbedding h) := by
    unfold FieldExtSingletonEmbedding
    exact RatHistoryCarrier_hsame_transport (hsame_symm (append_empty_left h)) carrier
  have identityContinuation : Cont BHist.Empty h (FieldExtSingletonEmbedding h) := by
    unfold FieldExtSingletonEmbedding
    exact cont_intro rfl
  exact And.intro carrier (And.intro embeddedCarrier identityContinuation)

def FieldExtRatReflexiveExactnessLedgerInterface (h k : BHist) : Prop :=
  RatHistoryClassifier h k ∧ RatHistoryCarrier (FieldExtSingletonEmbedding h) ∧
    RatHistoryCarrier (FieldExtSingletonEmbedding k) ∧
      RatHistoryLedgerPolicy h (FieldExtSingletonEmbedding h) ∧
        RatHistoryLedgerPolicy k (FieldExtSingletonEmbedding k) ∧
          Cont BHist.Empty h (FieldExtSingletonEmbedding h) ∧
            Cont BHist.Empty k (FieldExtSingletonEmbedding k)

theorem FieldExtRatReflexiveExactnessLedgerInterface_of_classifier {h k : BHist} :
    RatHistoryClassifier h k -> FieldExtRatReflexiveExactnessLedgerInterface h k := by
  intro classified
  have locked := FieldExtRatReflexiveEmbedding_ledger_source_lock classified
  have hCarrier : RatHistoryCarrier (FieldExtSingletonEmbedding h) :=
    RatHistoryLedgerPolicy_visible_carrier locked.left
  have kCarrier : RatHistoryCarrier (FieldExtSingletonEmbedding k) :=
    RatHistoryLedgerPolicy_visible_carrier locked.right.left
  exact And.intro classified
    (And.intro hCarrier
      (And.intro kCarrier
        (And.intro locked.left
          (And.intro locked.right.left (And.intro locked.right.right.right.left
            locked.right.right.right.right)))))

end BEDC.Derived.FieldExtUp
