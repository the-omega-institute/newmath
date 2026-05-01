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

end BEDC.Derived.SumUp
