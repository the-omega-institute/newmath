import BEDC.Derived.SumUp

namespace BEDC.Derived.SumUp

open BEDC.FKernel.Hist

theorem SumHistoryCarrier_visible_payload_determinism {Left Right : BHist → Prop}
    {h l l' r r' : BHist} :
    (hsame h (BHist.e0 l) → Left l → hsame h (BHist.e0 l') → Left l' → hsame l l') ∧
      (hsame h (BHist.e1 r) → Right r → hsame h (BHist.e1 r') → Right r' →
        hsame r r') := by
  constructor
  · intro sameLeft _ sameLeft' _
    exact hsame_e0_iff.mp (hsame_trans (hsame_symm sameLeft) sameLeft')
  · intro sameRight _ sameRight' _
    exact hsame_e1_iff.mp (hsame_trans (hsame_symm sameRight) sameRight')

theorem SumHistoryClassifier_carrier_aware_branch_partition {Left Right : BHist → Prop}
    {LeftEq RightEq : BHist → BHist → Prop} {h k : BHist} :
    SumHistoryCarrier Left Right h →
      SumHistoryCarrier Left Right k →
        SumHistoryClassifier Left Right LeftEq RightEq h k →
          (∃ a : BHist, ∃ b : BHist,
            Left a ∧ Left b ∧ hsame h (BHist.e0 a) ∧ hsame k (BHist.e0 b) ∧
              LeftEq a b) ∨
            (∃ a : BHist, ∃ b : BHist,
              Right a ∧ Right b ∧ hsame h (BHist.e1 a) ∧ hsame k (BHist.e1 b) ∧
                RightEq a b) := by
  intro carrierH carrierK classifier
  cases classifier with
  | inl leftBranch =>
      cases leftBranch with
      | intro a leftRest =>
          cases leftRest with
          | intro b data =>
              cases data with
              | intro sameH rest =>
                  cases rest with
                  | intro sameK sameLeft =>
                      have leftAtA :
                          ∃ a' : BHist, hsame a a' ∧ Left a' :=
                        SumHistoryCarrier_e0_inversion
                          (SumHistoryCarrier_hsame_transport sameH carrierH)
                      have leftAtB :
                          ∃ b' : BHist, hsame b b' ∧ Left b' :=
                        SumHistoryCarrier_e0_inversion
                          (SumHistoryCarrier_hsame_transport sameK carrierK)
                      cases leftAtA with
                      | intro a' leftDataA =>
                          cases leftDataA with
                          | intro sameA leftA' =>
                              cases sameA
                              cases leftAtB with
                              | intro b' leftDataB =>
                                  cases leftDataB with
                                  | intro sameB leftB' =>
                                      cases sameB
                                      exact Or.inl
                                        (Exists.intro a
                                          (Exists.intro b
                                            (And.intro leftA'
                                              (And.intro leftB'
                                                (And.intro sameH
                                                  (And.intro sameK sameLeft))))))
  | inr rightBranch =>
      cases rightBranch with
      | intro a rightRest =>
          cases rightRest with
          | intro b data =>
              cases data with
              | intro sameH rest =>
                  cases rest with
                  | intro sameK sameRight =>
                      have rightAtA :
                          ∃ a' : BHist, hsame a a' ∧ Right a' :=
                        SumHistoryCarrier_e1_inversion
                          (SumHistoryCarrier_hsame_transport sameH carrierH)
                      have rightAtB :
                          ∃ b' : BHist, hsame b b' ∧ Right b' :=
                        SumHistoryCarrier_e1_inversion
                          (SumHistoryCarrier_hsame_transport sameK carrierK)
                      cases rightAtA with
                      | intro a' rightDataA =>
                          cases rightDataA with
                          | intro sameA rightA' =>
                              cases sameA
                              cases rightAtB with
                              | intro b' rightDataB =>
                                  cases rightDataB with
                                  | intro sameB rightB' =>
                                      cases sameB
                                      exact Or.inr
                                        (Exists.intro a
                                          (Exists.intro b
                                            (And.intro rightA'
                                              (And.intro rightB'
                                                (And.intro sameH
                                                  (And.intro sameK sameRight))))))

theorem SumHistoryClassifier_carrier_aware_branch_exactness {Left Right : BHist → Prop}
    {LeftEq RightEq : BHist → BHist → Prop} {h k : BHist} :
    (SumHistoryCarrier Left Right h ∧ SumHistoryCarrier Left Right k ∧
        SumHistoryClassifier Left Right LeftEq RightEq h k) ↔
      ((∃ a : BHist, ∃ b : BHist,
          Left a ∧ Left b ∧ hsame h (BHist.e0 a) ∧ hsame k (BHist.e0 b) ∧
            LeftEq a b) ∨
        (∃ a : BHist, ∃ b : BHist,
          Right a ∧ Right b ∧ hsame h (BHist.e1 a) ∧ hsame k (BHist.e1 b) ∧
            RightEq a b)) := by
  constructor
  · intro packed
    cases packed with
    | intro carrierH rest =>
        cases rest with
        | intro carrierK classifier =>
            exact SumHistoryClassifier_carrier_aware_branch_partition carrierH carrierK classifier
  · intro branch
    cases branch with
    | inl leftBranch =>
        cases leftBranch with
        | intro a restA =>
            cases restA with
            | intro b data =>
                cases data with
                | intro leftA rest =>
                    cases rest with
                    | intro leftB rest =>
                        cases rest with
                        | intro sameH rest =>
                            cases rest with
                            | intro sameK leftEq =>
                                exact And.intro
                                  (Or.inl (Exists.intro a (And.intro sameH leftA)))
                                  (And.intro
                                    (Or.inl (Exists.intro b (And.intro sameK leftB)))
                                    (Or.inl
                                      (Exists.intro a
                                        (Exists.intro b
                                          (And.intro sameH (And.intro sameK leftEq))))))
    | inr rightBranch =>
        cases rightBranch with
        | intro a restA =>
            cases restA with
            | intro b data =>
                cases data with
                | intro rightA rest =>
                    cases rest with
                    | intro rightB rest =>
                        cases rest with
                        | intro sameH rest =>
                            cases rest with
                            | intro sameK rightEq =>
                                exact And.intro
                                  (Or.inr (Exists.intro a (And.intro sameH rightA)))
                                  (And.intro
                                    (Or.inr (Exists.intro b (And.intro sameK rightB)))
                                    (Or.inr
                                      (Exists.intro a
                                        (Exists.intro b
                                          (And.intro sameH (And.intro sameK rightEq))))))

theorem SumHistorySource_weakening {Left Right Left' Right' : BHist -> Prop}
    {LeftEq RightEq LeftEq' RightEq' : BHist -> BHist -> Prop} :
    ((forall h : BHist, Left h -> Left' h) /\
        (forall h : BHist, Right h -> Right' h)) ->
      ((forall a b : BHist, LeftEq a b -> LeftEq' a b) /\
        (forall a b : BHist, RightEq a b -> RightEq' a b)) ->
        (forall {h : BHist},
          SumHistoryCarrier Left Right h -> SumHistoryCarrier Left' Right' h) /\
          (forall {h k : BHist},
            SumHistoryClassifier Left Right LeftEq RightEq h k ->
              SumHistoryClassifier Left' Right' LeftEq' RightEq' h k) := by
  intro sourceWeakening relationWeakening
  cases sourceWeakening with
  | intro leftSource rightSource =>
      cases relationWeakening with
      | intro leftRelation rightRelation =>
          constructor
          · intro h carrier
            cases carrier with
            | inl leftBranch =>
                cases leftBranch with
                | intro l data =>
                    cases data with
                    | intro sameH leftCarrier =>
                        exact Or.inl
                          (Exists.intro l (And.intro sameH (leftSource l leftCarrier)))
            | inr rightBranch =>
                cases rightBranch with
                | intro r data =>
                    cases data with
                    | intro sameH rightCarrier =>
                        exact Or.inr
                          (Exists.intro r (And.intro sameH (rightSource r rightCarrier)))
          · intro h k classifier
            cases classifier with
            | inl leftBranch =>
                cases leftBranch with
                | intro a restA =>
                    cases restA with
                    | intro b data =>
                        cases data with
                        | intro sameH rest =>
                            cases rest with
                            | intro sameK sameLeft =>
                                exact Or.inl
                                  (Exists.intro a
                                    (Exists.intro b
                                      (And.intro sameH
                                        (And.intro sameK
                                          (leftRelation a b sameLeft)))))
            | inr rightBranch =>
                cases rightBranch with
                | intro a restA =>
                    cases restA with
                    | intro b data =>
                        cases data with
                        | intro sameH rest =>
                            cases rest with
                            | intro sameK sameRight =>
                                exact Or.inr
                                  (Exists.intro a
                                    (Exists.intro b
                                      (And.intro sameH
                                        (And.intro sameK
                                          (rightRelation a b sameRight)))))

end BEDC.Derived.SumUp
