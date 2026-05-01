import BEDC.Derived.SumUp

namespace BEDC.Derived.SumUp

open BEDC.FKernel.Hist

def SumHistoryLedgerPolicy (Left Right : BHist -> Prop) (raw visible : BHist) : Prop :=
  SumHistoryCarrier Left Right raw ∧ hsame raw visible

theorem SumHistoryLedgerPolicy_visible_carrier {Left Right : BHist -> Prop}
    {raw visible : BHist} :
    SumHistoryLedgerPolicy Left Right raw visible -> SumHistoryCarrier Left Right visible := by
  intro ledger
  cases ledger with
  | intro rawCarrier sameRawVisible =>
      exact SumHistoryCarrier_hsame_transport sameRawVisible rawCarrier

theorem SumHistoryLedgerPolicy_raw_visible_classifier {Left Right : BHist -> Prop}
    {raw visible : BHist} :
    SumHistoryLedgerPolicy Left Right raw visible ->
      SumHistoryClassifier Left Right hsame hsame raw visible := by
  intro ledger
  cases ledger with
  | intro rawCarrier sameRawVisible =>
      cases rawCarrier with
      | inl leftData =>
          cases leftData with
          | intro leftHist data =>
              cases data with
              | intro sameRawTag _ =>
                  exact Or.inl
                    (Exists.intro leftHist
                      (Exists.intro leftHist
                        (And.intro sameRawTag
                          (And.intro (hsame_trans (hsame_symm sameRawVisible) sameRawTag)
                            (hsame_refl leftHist)))))
      | inr rightData =>
          cases rightData with
          | intro rightHist data =>
              cases data with
              | intro sameRawTag _ =>
                  exact Or.inr
                    (Exists.intro rightHist
                      (Exists.intro rightHist
                        (And.intro sameRawTag
                          (And.intro (hsame_trans (hsame_symm sameRawVisible) sameRawTag)
                            (hsame_refl rightHist)))))

theorem SumHistoryLedgerPolicy_hsame_transport {Left Right : BHist -> Prop}
    {raw raw' visible visible' : BHist} :
    SumHistoryLedgerPolicy Left Right raw visible -> hsame raw raw' -> hsame visible visible' ->
      SumHistoryLedgerPolicy Left Right raw' visible' := by
  intro ledger sameRaw sameVisible
  cases ledger with
  | intro rawCarrier sameRawVisible =>
      exact And.intro (SumHistoryCarrier_hsame_transport sameRaw rawCarrier)
        (hsame_trans (hsame_symm sameRaw) (hsame_trans sameRawVisible sameVisible))

theorem SumHistoryLedgerPolicy_visible_tag_separation {Left Right : BHist → Prop}
    {raw visible l r : BHist} :
    SumHistoryLedgerPolicy Left Right raw visible →
      ((hsame raw (BHist.e0 l) ∧ hsame visible (BHist.e1 r)) → False) ∧
        ((hsame raw (BHist.e1 r) ∧ hsame visible (BHist.e0 l)) → False) := by
  intro ledger
  have classifier : SumHistoryClassifier Left Right hsame hsame raw visible :=
    SumHistoryLedgerPolicy_raw_visible_classifier ledger
  constructor
  · intro mixed
    exact SumHistoryClassifier_mixed_tags_absurd mixed.left mixed.right classifier
  · intro mixed
    exact SumHistoryClassifier_mixed_tags_absurd mixed.right mixed.left
      (SumHistoryClassifier_hsame_symm classifier)

end BEDC.Derived.SumUp
