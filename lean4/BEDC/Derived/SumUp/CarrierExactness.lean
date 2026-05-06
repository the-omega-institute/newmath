import BEDC.Derived.SumUp.Classifier

namespace BEDC.Derived.SumUp

open BEDC.FKernel.Hist

theorem SumHistoryClassifier_hsame_same_tag_carrier_exactness {Left Right : BHist -> Prop}
    {l l' r r' : BHist} :
    (((SumHistoryCarrier Left Right (BHist.e0 l) ∧
        SumHistoryCarrier Left Right (BHist.e0 l') ∧
          SumHistoryClassifier Left Right hsame hsame (BHist.e0 l) (BHist.e0 l')) ↔
        ∃ a : BHist, ∃ a' : BHist,
          Left a ∧ Left a' ∧ hsame l a ∧ hsame l' a' ∧ hsame a a') ∧
      ((SumHistoryCarrier Left Right (BHist.e1 r) ∧
        SumHistoryCarrier Left Right (BHist.e1 r') ∧
          SumHistoryClassifier Left Right hsame hsame (BHist.e1 r) (BHist.e1 r')) ↔
        ∃ b : BHist, ∃ b' : BHist,
          Right b ∧ Right b' ∧ hsame r b ∧ hsame r' b' ∧ hsame b b')) := by
  constructor
  · constructor
    · intro packed
      have leftPayload := SumHistoryCarrier_e0_inversion packed.left
      have rightPayload := SumHistoryCarrier_e0_inversion packed.right.left
      cases leftPayload with
      | intro a leftData =>
          cases rightPayload with
          | intro a' rightData =>
              have sameEndpoints : hsame l l' :=
                SumHistoryClassifier_left_hsame_inversion packed.right.right
              have samePayloads : hsame a a' :=
                hsame_trans (hsame_symm leftData.left)
                  (hsame_trans sameEndpoints rightData.left)
              exact Exists.intro a
                (Exists.intro a'
                  (And.intro leftData.right
                    (And.intro rightData.right
                      (And.intro leftData.left
                        (And.intro rightData.left samePayloads)))))
    · intro payloads
      cases payloads with
      | intro a rest =>
          cases rest with
          | intro a' data =>
              exact And.intro
                (Or.inl (Exists.intro a
                  (And.intro (hsame_e0_iff.mpr data.right.right.left) data.left)))
                (And.intro
                  (Or.inl (Exists.intro a'
                    (And.intro (hsame_e0_iff.mpr data.right.right.right.left)
                      data.right.left)))
                  (Or.inl
                    (Exists.intro a
                      (Exists.intro a'
                        (And.intro (hsame_e0_iff.mpr data.right.right.left)
                          (And.intro (hsame_e0_iff.mpr data.right.right.right.left)
                            data.right.right.right.right))))))
  · constructor
    · intro packed
      have leftPayload := SumHistoryCarrier_e1_inversion packed.left
      have rightPayload := SumHistoryCarrier_e1_inversion packed.right.left
      cases leftPayload with
      | intro b leftData =>
          cases rightPayload with
          | intro b' rightData =>
              have sameEndpoints : hsame r r' :=
                SumHistoryClassifier_right_hsame_inversion packed.right.right
              have samePayloads : hsame b b' :=
                hsame_trans (hsame_symm leftData.left)
                  (hsame_trans sameEndpoints rightData.left)
              exact Exists.intro b
                (Exists.intro b'
                  (And.intro leftData.right
                    (And.intro rightData.right
                      (And.intro leftData.left
                        (And.intro rightData.left samePayloads)))))
    · intro payloads
      cases payloads with
      | intro b rest =>
          cases rest with
          | intro b' data =>
              exact And.intro
                (Or.inr (Exists.intro b
                  (And.intro (hsame_e1_iff.mpr data.right.right.left) data.left)))
                (And.intro
                  (Or.inr (Exists.intro b'
                    (And.intro (hsame_e1_iff.mpr data.right.right.right.left)
                      data.right.left)))
                  (Or.inr
                    (Exists.intro b
                      (Exists.intro b'
                        (And.intro (hsame_e1_iff.mpr data.right.right.left)
                          (And.intro (hsame_e1_iff.mpr data.right.right.right.left)
                            data.right.right.right.right))))))

end BEDC.Derived.SumUp
