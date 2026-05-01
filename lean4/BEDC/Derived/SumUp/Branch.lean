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

end BEDC.Derived.SumUp
