import BEDC.Derived.FieldExtUp.SingletonLedger

namespace BEDC.Derived.FieldExtUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.Derived.FieldUp
open BEDC.Derived.VecSpaceUp

theorem FieldExtUp_StdBridge :
    FieldExtSingletonCarrier BHist.Empty ∧
      SemanticNameCert FieldExtSingletonCarrier FieldExtSingletonCarrier
        FieldExtSingletonCarrier FieldExtSingletonClassifier ∧
        FieldExtSingletonLedgerPolicy BHist.Empty ∧
          Cont BHist.Empty BHist.Empty (FieldExtSingletonEmbedding BHist.Empty) ∧
            hsame (FieldExtSingletonEmbedding BHist.Empty) BHist.Empty := by
  have bridgeObligations := FieldExtSingleton_embedding_obligations
  have emptyCarrier : FieldExtSingletonCarrier BHist.Empty :=
    And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty)
  have emptyLedger : FieldExtSingletonLedgerPolicy BHist.Empty := by
    exact And.intro (hsame_refl BHist.Empty)
      (And.intro (hsame_refl BHist.Empty)
        (And.intro (hsame_refl BHist.Empty)
          (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))))
  have embeddingCont : Cont BHist.Empty BHist.Empty
      (FieldExtSingletonEmbedding BHist.Empty) := by
    unfold FieldExtSingletonEmbedding
    exact cont_intro rfl
  have embeddingSame : hsame (FieldExtSingletonEmbedding BHist.Empty) BHist.Empty := by
    unfold FieldExtSingletonEmbedding
    exact hsame_refl BHist.Empty
  exact And.intro emptyCarrier
    (And.intro bridgeObligations.left
      (And.intro emptyLedger (And.intro embeddingCont embeddingSame)))

end BEDC.Derived.FieldExtUp
