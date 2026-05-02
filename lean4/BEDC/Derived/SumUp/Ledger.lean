import BEDC.Derived.SumUp.Classifier

namespace BEDC.Derived.SumUp

open BEDC.FKernel.Hist

def SumHistoryLedgerPolicy (Left Right : BHist -> Prop) (raw visible : BHist) : Prop :=
  SumHistoryCarrier Left Right raw ∧ hsame raw visible

inductive SumHistoryLedgerChain (Left Right : BHist → Prop) : BHist → BHist → Prop where
  | single {raw visible : BHist} :
      SumHistoryLedgerPolicy Left Right raw visible →
        SumHistoryLedgerChain Left Right raw visible
  | cons {raw mid visible : BHist} :
      SumHistoryLedgerPolicy Left Right raw mid →
        SumHistoryLedgerChain Left Right mid visible →
          SumHistoryLedgerChain Left Right raw visible

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

theorem SumHistoryLedgerChain_classifier_composition {Left Right : BHist -> Prop}
    {raw visible : BHist} :
    SumHistoryLedgerChain Left Right raw visible ->
      SumHistoryClassifier Left Right hsame hsame raw visible := by
  intro chain
  induction chain with
  | single ledger =>
      exact SumHistoryLedgerPolicy_raw_visible_classifier ledger
  | cons ledger _ ih =>
      exact SumHistoryLedgerPolicy_classifier_composition ledger ih

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

theorem SumHistoryLedgerPolicy_same_tag_payload_exactness {Left Right : BHist -> Prop}
    {raw visible l l' r r' : BHist} :
    SumHistoryLedgerPolicy Left Right raw visible ->
      (((hsame raw (BHist.e0 l) ∧ hsame visible (BHist.e0 l')) -> hsame l l') ∧
        ((hsame raw (BHist.e1 r) ∧ hsame visible (BHist.e1 r')) -> hsame r r')) := by
  intro ledger
  have classifier : SumHistoryClassifier Left Right hsame hsame raw visible :=
    SumHistoryLedgerPolicy_raw_visible_classifier ledger
  constructor
  · intro sameTagged
    exact SumHistoryClassifier_left_hsame_inversion
      (SumHistoryClassifier_hsame_transport sameTagged.left sameTagged.right classifier)
  · intro sameTagged
    exact SumHistoryClassifier_right_hsame_inversion
      (SumHistoryClassifier_hsame_transport sameTagged.left sameTagged.right classifier)

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

theorem SumHistoryLedgerPolicy_two_step_branch_exactness {Left Right : BHist -> Prop}
    {rho v w : BHist} :
    SumHistoryLedgerPolicy Left Right rho v ->
      SumHistoryLedgerPolicy Left Right v w ->
        ((∃ l : BHist, ∃ l' : BHist,
            Left l ∧ Left l' ∧ hsame rho (BHist.e0 l) ∧ hsame w (BHist.e0 l') ∧
              hsame l l') ∨
          (∃ r : BHist, ∃ r' : BHist,
            Right r ∧ Right r' ∧ hsame rho (BHist.e1 r) ∧ hsame w (BHist.e1 r') ∧
              hsame r r')) := by
  intro firstLedger secondLedger
  have firstBranches :
      (∃ l : BHist, Left l ∧ hsame rho (BHist.e0 l) ∧ hsame v (BHist.e0 l)) ∨
        (∃ r : BHist, Right r ∧ hsame rho (BHist.e1 r) ∧ hsame v (BHist.e1 r)) :=
    (SumHistoryLedgerPolicy_raw_visible_branch_exactness.mp firstLedger)
  have secondBranches :
      (∃ l' : BHist, Left l' ∧ hsame v (BHist.e0 l') ∧ hsame w (BHist.e0 l')) ∨
        (∃ r' : BHist, Right r' ∧ hsame v (BHist.e1 r') ∧ hsame w (BHist.e1 r')) :=
    (SumHistoryLedgerPolicy_raw_visible_branch_exactness.mp secondLedger)
  cases firstBranches with
  | inl firstLeft =>
      cases firstLeft with
      | intro l firstData =>
          cases firstData with
          | intro leftL firstRest =>
              cases firstRest with
              | intro sameRhoLeft sameVLeft =>
                  cases secondBranches with
                  | inl secondLeft =>
                      cases secondLeft with
                      | intro l' secondData =>
                          cases secondData with
                          | intro leftL' secondRest =>
                              cases secondRest with
                              | intro sameVLeft' sameWLeft =>
                                  have samePayload : hsame l l' :=
                                    hsame_e0_iff.mp
                                      (hsame_trans (hsame_symm sameVLeft) sameVLeft')
                                  exact Or.inl
                                    (Exists.intro l
                                      (Exists.intro l'
                                        (And.intro leftL
                                          (And.intro leftL'
                                            (And.intro sameRhoLeft
                                              (And.intro sameWLeft samePayload))))))
                  | inr secondRight =>
                      cases secondRight with
                      | intro r' secondData =>
                          cases secondData with
                          | intro _ secondRest =>
                              cases secondRest with
                              | intro sameVRight' _ =>
                                  exact False.elim
                                    (not_hsame_e0_e1
                                      (hsame_trans (hsame_symm sameVLeft) sameVRight'))
  | inr firstRight =>
      cases firstRight with
      | intro r firstData =>
          cases firstData with
          | intro rightR firstRest =>
              cases firstRest with
              | intro sameRhoRight sameVRight =>
                  cases secondBranches with
                  | inl secondLeft =>
                      cases secondLeft with
                      | intro l' secondData =>
                          cases secondData with
                          | intro _ secondRest =>
                              cases secondRest with
                              | intro sameVLeft' _ =>
                                  exact False.elim
                                    (not_hsame_e1_e0
                                      (hsame_trans (hsame_symm sameVRight) sameVLeft'))
                  | inr secondRight =>
                      cases secondRight with
                      | intro r' secondData =>
                          cases secondData with
                          | intro rightR' secondRest =>
                              cases secondRest with
                              | intro sameVRight' sameWRight =>
                                  have samePayload : hsame r r' :=
                                    hsame_e1_iff.mp
                                      (hsame_trans (hsame_symm sameVRight) sameVRight')
                                  exact Or.inr
                                    (Exists.intro r
                                      (Exists.intro r'
                                        (And.intro rightR
                                          (And.intro rightR'
                                            (And.intro sameRhoRight
                                              (And.intro sameWRight samePayload))))))

theorem SumHistoryLedgerChain_branch_exactness {Left Right : BHist -> Prop}
    {rho z : BHist} :
    SumHistoryLedgerChain Left Right rho z ->
      ((exists l : BHist, exists l' : BHist,
          Left l /\ Left l' /\ hsame rho (BHist.e0 l) /\ hsame z (BHist.e0 l') /\
            hsame l l') \/
        (exists r : BHist, exists r' : BHist,
          Right r /\ Right r' /\ hsame rho (BHist.e1 r) /\ hsame z (BHist.e1 r') /\
            hsame r r')) := by
  intro chain
  induction chain with
  | single ledger =>
      have branches := SumHistoryLedgerPolicy_raw_visible_branch_exactness.mp ledger
      cases branches with
      | inl leftBranch =>
          cases leftBranch with
          | intro l leftData =>
              cases leftData with
              | intro leftL leftRest =>
                  exact Or.inl
                    (Exists.intro l
                      (Exists.intro l
                        (And.intro leftL
                          (And.intro leftL
                            (And.intro leftRest.left
                              (And.intro leftRest.right (hsame_refl l)))))))
      | inr rightBranch =>
          cases rightBranch with
          | intro r rightData =>
              cases rightData with
              | intro rightR rightRest =>
                  exact Or.inr
                    (Exists.intro r
                      (Exists.intro r
                        (And.intro rightR
                          (And.intro rightR
                            (And.intro rightRest.left
                              (And.intro rightRest.right (hsame_refl r)))))))
  | cons ledger _ ih =>
      have firstBranches := SumHistoryLedgerPolicy_raw_visible_branch_exactness.mp ledger
      cases firstBranches with
      | inl firstLeft =>
          cases firstLeft with
          | intro l firstData =>
              cases firstData with
              | intro leftL firstRest =>
                  cases ih with
                  | inl chainLeft =>
                      cases chainLeft with
                      | intro lMid chainLeftRest =>
                          cases chainLeftRest with
                          | intro l' chainLeftData =>
                              cases chainLeftData with
                              | intro leftMid chainLeftRest =>
                                  cases chainLeftRest with
                                  | intro leftL' chainLeftRest =>
                                      have samePayload : hsame l lMid :=
                                        hsame_e0_iff.mp
                                          (hsame_trans (hsame_symm firstRest.right)
                                            chainLeftRest.left)
                                      exact Or.inl
                                        (Exists.intro l
                                          (Exists.intro l'
                                            (And.intro leftL
                                              (And.intro leftL'
                                                (And.intro firstRest.left
                                                  (And.intro chainLeftRest.right.left
                                                    (hsame_trans samePayload
                                                      chainLeftRest.right.right)))))))
                  | inr chainRight =>
                      cases chainRight with
                      | intro rMid chainRightRest =>
                          cases chainRightRest with
                          | intro r' chainRightData =>
                              cases chainRightData with
                              | intro _rightMid chainRightRest =>
                                  exact False.elim
                                    (not_hsame_e0_e1
                                      (hsame_trans (hsame_symm firstRest.right)
                                        chainRightRest.right.left))
      | inr firstRight =>
          cases firstRight with
          | intro r firstData =>
              cases firstData with
              | intro rightR firstRest =>
                  cases ih with
                  | inl chainLeft =>
                      cases chainLeft with
                      | intro lMid chainLeftRest =>
                          cases chainLeftRest with
                          | intro l' chainLeftData =>
                              cases chainLeftData with
                              | intro _leftMid chainLeftRest =>
                                  exact False.elim
                                    (not_hsame_e1_e0
                                      (hsame_trans (hsame_symm firstRest.right)
                                        chainLeftRest.right.left))
                  | inr chainRight =>
                      cases chainRight with
                      | intro rMid chainRightRest =>
                          cases chainRightRest with
                          | intro r' chainRightData =>
                              cases chainRightData with
                              | intro rightMid chainRightRest =>
                                  cases chainRightRest with
                                  | intro rightR' chainRightRest =>
                                      have samePayload : hsame r rMid :=
                                        hsame_e1_iff.mp
                                          (hsame_trans (hsame_symm firstRest.right)
                                            chainRightRest.left)
                                      exact Or.inr
                                        (Exists.intro r
                                          (Exists.intro r'
                                            (And.intro rightR
                                              (And.intro rightR'
                                                (And.intro firstRest.left
                                                  (And.intro chainRightRest.right.left
                                                    (hsame_trans samePayload
                                                      chainRightRest.right.right)))))))

theorem SumHistoryLedgerPolicy_visible_payload_readback {Left Right : BHist -> Prop}
    {raw visible l r : BHist} :
    SumHistoryLedgerPolicy Left Right raw visible ->
      (hsame visible (BHist.e0 l) -> ∃ a : BHist, Left a ∧ hsame l a) ∧
        (hsame visible (BHist.e1 r) -> ∃ b : BHist, Right b ∧ hsame r b) := by
  intro ledger
  have visibleCarrier : SumHistoryCarrier Left Right visible :=
    SumHistoryLedgerPolicy_visible_carrier ledger
  constructor
  · intro sameVisible
    have carrierAt : SumHistoryCarrier Left Right (BHist.e0 l) :=
      SumHistoryCarrier_hsame_transport sameVisible visibleCarrier
    cases SumHistoryCarrier_e0_inversion carrierAt with
    | intro a data =>
        exact Exists.intro a (And.intro data.right data.left)
  · intro sameVisible
    have carrierAt : SumHistoryCarrier Left Right (BHist.e1 r) :=
      SumHistoryCarrier_hsame_transport sameVisible visibleCarrier
    cases SumHistoryCarrier_e1_inversion carrierAt with
    | intro b data =>
        exact Exists.intro b (And.intro data.right data.left)

theorem SumHistoryLedgerChain_endpoint_exactness {Left Right : BHist → Prop}
    {rho z l l' r r' : BHist} :
    SumHistoryLedgerChain Left Right rho z →
      (((hsame rho (BHist.e0 l) ∧ hsame z (BHist.e1 r')) → False) ∧
        ((hsame rho (BHist.e1 r) ∧ hsame z (BHist.e0 l')) → False) ∧
        ((hsame rho (BHist.e0 l) ∧ hsame z (BHist.e0 l')) → hsame l l') ∧
        ((hsame rho (BHist.e1 r) ∧ hsame z (BHist.e1 r')) → hsame r r') ∧
        (hsame z (BHist.e0 l') → ∃ a : BHist, Left a ∧ hsame l' a) ∧
        (hsame z (BHist.e1 r') → ∃ b : BHist, Right b ∧ hsame r' b)) := by
  intro chain
  have carrierZ : SumHistoryCarrier Left Right z := by
    induction chain with
    | single ledger =>
        exact SumHistoryLedgerPolicy_visible_carrier ledger
    | cons _ _ ih =>
        exact ih
  have classifier : SumHistoryClassifier Left Right hsame hsame rho z := by
    clear carrierZ
    exact SumHistoryLedgerChain_classifier_composition chain
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
          · intro sameZ
            have carrierAt : SumHistoryCarrier Left Right (BHist.e0 l') :=
              SumHistoryCarrier_hsame_transport sameZ carrierZ
            cases SumHistoryCarrier_e0_inversion carrierAt with
            | intro a data =>
                exact Exists.intro a (And.intro data.right data.left)
          · intro sameZ
            have carrierAt : SumHistoryCarrier Left Right (BHist.e1 r') :=
              SumHistoryCarrier_hsame_transport sameZ carrierZ
            cases SumHistoryCarrier_e1_inversion carrierAt with
            | intro b data =>
                exact Exists.intro b (And.intro data.right data.left)

theorem SumHistoryLedgerChain_raw_branch_final_readback {Left Right : BHist → Prop}
    {rho z l r : BHist} :
    SumHistoryLedgerChain Left Right rho z →
      (Left l →
        hsame rho (BHist.e0 l) →
          ∃ l' : BHist,
            Left l' ∧ hsame z (BHist.e0 l') ∧ hsame l l' ∧
              ((∃ r' : BHist, Right r' ∧ hsame z (BHist.e1 r')) → False)) ∧
        (Right r →
          hsame rho (BHist.e1 r) →
            ∃ r' : BHist,
              Right r' ∧ hsame z (BHist.e1 r') ∧ hsame r r' ∧
                ((∃ l' : BHist, Left l' ∧ hsame z (BHist.e0 l')) → False)) := by
  intro chain
  constructor
  · intro _leftL sameRhoLeft
    have branches := SumHistoryLedgerChain_branch_exactness chain
    cases branches with
    | inl leftBranch =>
        cases leftBranch with
        | intro l0 leftBranch =>
            cases leftBranch with
            | intro l' data =>
                have sameLL0 : hsame l l0 :=
                  hsame_e0_iff.mp (hsame_trans (hsame_symm sameRhoLeft)
                    data.right.right.left)
                have noRight :
                    (∃ r' : BHist, Right r' ∧ hsame z (BHist.e1 r')) → False := by
                  intro rightVisible
                  cases rightVisible with
                  | intro r' rightData =>
                      exact (SumHistoryLedgerChain_endpoint_exactness
                        (Left := Left) (Right := Right) (rho := rho) (z := z)
                        (l := l) (l' := l) (r := r') (r' := r') chain).left
                        (And.intro sameRhoLeft rightData.right)
                exact Exists.intro l'
                  (And.intro data.right.left
                    (And.intro data.right.right.right.left
                      (And.intro (hsame_trans sameLL0 data.right.right.right.right)
                        noRight)))
    | inr rightBranch =>
        cases rightBranch with
        | intro _r0 rightBranch =>
            cases rightBranch with
            | intro r' data =>
                exact False.elim
                  ((SumHistoryLedgerChain_endpoint_exactness
                    (Left := Left) (Right := Right) (rho := rho) (z := z)
                    (l := l) (l' := l) (r := r') (r' := r') chain).left
                    (And.intro sameRhoLeft data.right.right.right.left))
  · intro _rightR sameRhoRight
    have branches := SumHistoryLedgerChain_branch_exactness chain
    cases branches with
    | inl leftBranch =>
        cases leftBranch with
        | intro _l0 leftBranch =>
            cases leftBranch with
            | intro l' data =>
                exact False.elim
                  ((SumHistoryLedgerChain_endpoint_exactness
                    (Left := Left) (Right := Right) (rho := rho) (z := z)
                    (l := l') (l' := l') (r := r) (r' := r) chain).right.left
                    (And.intro sameRhoRight data.right.right.right.left))
    | inr rightBranch =>
        cases rightBranch with
        | intro r0 rightBranch =>
            cases rightBranch with
            | intro r' data =>
                have sameRR0 : hsame r r0 :=
                  hsame_e1_iff.mp (hsame_trans (hsame_symm sameRhoRight)
                    data.right.right.left)
                have noLeft :
                    (∃ l' : BHist, Left l' ∧ hsame z (BHist.e0 l')) → False := by
                  intro leftVisible
                  cases leftVisible with
                  | intro l' leftData =>
                      exact (SumHistoryLedgerChain_endpoint_exactness
                        (Left := Left) (Right := Right) (rho := rho) (z := z)
                        (l := l') (l' := l') (r := r) (r' := r) chain).right.left
                        (And.intro sameRhoRight leftData.right)
                exact Exists.intro r'
                  (And.intro data.right.left
                    (And.intro data.right.right.right.left
                      (And.intro (hsame_trans sameRR0 data.right.right.right.right)
                        noLeft)))

end BEDC.Derived.SumUp
