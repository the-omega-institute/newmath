import BEDC.Derived.SumUp.Classifier

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

theorem SumHistoryLedgerPolicy_classifier_composition {Left Right : BHist → Prop}
    {rho v w : BHist} :
    SumHistoryLedgerPolicy Left Right rho v →
      SumHistoryClassifier Left Right hsame hsame v w →
        SumHistoryClassifier Left Right hsame hsame rho w := by
  intro ledger classifier
  exact SumHistoryClassifier_trans (Left := Left) (Right := Right)
    (LeftEq := hsame) (RightEq := hsame) (@hsame_trans) (@hsame_trans)
    (SumHistoryLedgerPolicy_raw_visible_classifier ledger)
    classifier

theorem SumHistoryLedgerPolicy_two_step_classifier_composition {Left Right : BHist -> Prop}
    {rho v w : BHist} :
    SumHistoryLedgerPolicy Left Right rho v ->
      SumHistoryLedgerPolicy Left Right v w ->
        SumHistoryClassifier Left Right hsame hsame rho w := by
  intro firstLedger secondLedger
  exact SumHistoryClassifier_trans (Left := Left) (Right := Right)
    (LeftEq := hsame) (RightEq := hsame) (@hsame_trans) (@hsame_trans)
    (SumHistoryLedgerPolicy_raw_visible_classifier firstLedger)
    (SumHistoryLedgerPolicy_raw_visible_classifier secondLedger)

theorem SumHistoryLedgerPolicy_two_step_endpoint_exactness {Left Right : BHist -> Prop}
    {rho v w l l' r r' : BHist} :
    SumHistoryLedgerPolicy Left Right rho v ->
      SumHistoryLedgerPolicy Left Right v w ->
        (((hsame rho (BHist.e0 l) ∧ hsame w (BHist.e1 r')) -> False) ∧
          ((hsame rho (BHist.e1 r) ∧ hsame w (BHist.e0 l')) -> False) ∧
          ((hsame rho (BHist.e0 l) ∧ hsame w (BHist.e0 l')) -> hsame l l') ∧
          ((hsame rho (BHist.e1 r) ∧ hsame w (BHist.e1 r')) -> hsame r r') ∧
          (hsame w (BHist.e0 l') -> ∃ a : BHist, Left a ∧ hsame l' a) ∧
          (hsame w (BHist.e1 r') -> ∃ b : BHist, Right b ∧ hsame r' b)) := by
  intro firstLedger secondLedger
  have classifier : SumHistoryClassifier Left Right hsame hsame rho w :=
    SumHistoryLedgerPolicy_two_step_classifier_composition firstLedger secondLedger
  have carrierW : SumHistoryCarrier Left Right w :=
    SumHistoryLedgerPolicy_visible_carrier secondLedger
  constructor
  · intro mixed
    exact SumHistoryClassifier_mixed_tags_absurd mixed.left mixed.right classifier
  · constructor
    · intro mixed
      exact SumHistoryClassifier_mixed_tags_absurd mixed.right mixed.left
        (SumHistoryClassifier_hsame_symm classifier)
    · constructor
      · intro sameTagged
        exact SumHistoryClassifier_left_hsame_inversion
          (SumHistoryClassifier_hsame_transport sameTagged.left sameTagged.right classifier)
      · constructor
        · intro sameTagged
          exact SumHistoryClassifier_right_hsame_inversion
            (SumHistoryClassifier_hsame_transport sameTagged.left sameTagged.right classifier)
        · constructor
          · intro sameW
            have carrierAt : SumHistoryCarrier Left Right (BHist.e0 l') :=
              SumHistoryCarrier_hsame_transport sameW carrierW
            cases SumHistoryCarrier_e0_inversion carrierAt with
            | intro a data =>
                exact Exists.intro a (And.intro data.right data.left)
          · intro sameW
            have carrierAt : SumHistoryCarrier Left Right (BHist.e1 r') :=
              SumHistoryCarrier_hsame_transport sameW carrierW
            cases SumHistoryCarrier_e1_inversion carrierAt with
            | intro b data =>
                exact Exists.intro b (And.intro data.right data.left)

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

theorem SumHistoryLedgerPolicy_raw_visible_branch_exactness {Left Right : BHist → Prop}
    {raw visible : BHist} :
    SumHistoryLedgerPolicy Left Right raw visible ↔
      ((∃ l : BHist, Left l ∧ hsame raw (BHist.e0 l) ∧ hsame visible (BHist.e0 l)) ∨
        (∃ r : BHist, Right r ∧ hsame raw (BHist.e1 r) ∧ hsame visible (BHist.e1 r))) := by
  constructor
  · intro ledger
    cases ledger with
    | intro rawCarrier sameRawVisible =>
        cases rawCarrier with
        | inl leftData =>
            cases leftData with
            | intro l data =>
                cases data with
                | intro sameRawTag leftL =>
                    exact Or.inl
                      (Exists.intro l
                        (And.intro leftL
                          (And.intro sameRawTag
                            (hsame_trans (hsame_symm sameRawVisible) sameRawTag))))
        | inr rightData =>
            cases rightData with
            | intro r data =>
                cases data with
                | intro sameRawTag rightR =>
                    exact Or.inr
                      (Exists.intro r
                        (And.intro rightR
                          (And.intro sameRawTag
                            (hsame_trans (hsame_symm sameRawVisible) sameRawTag))))
  · intro branch
    cases branch with
    | inl leftData =>
        cases leftData with
        | intro l data =>
            cases data with
            | intro leftL rest =>
                cases rest with
                | intro sameRawTag sameVisibleTag =>
                    exact And.intro
                      (Or.inl (Exists.intro l (And.intro sameRawTag leftL)))
                      (hsame_trans sameRawTag (hsame_symm sameVisibleTag))
    | inr rightData =>
        cases rightData with
        | intro r data =>
            cases data with
            | intro rightR rest =>
                cases rest with
                | intro sameRawTag sameVisibleTag =>
                    exact And.intro
                      (Or.inr (Exists.intro r (And.intro sameRawTag rightR)))
                      (hsame_trans sameRawTag (hsame_symm sameVisibleTag))

end BEDC.Derived.SumUp
