import BEDC.Derived.SumUp.Classifier

namespace BEDC.Derived.SumUp

open BEDC.FKernel.Hist

theorem SumHistoryClassifier_carrier_aware_same_tag_exactness {Left Right : BHist -> Prop}
    {LeftEq RightEq : BHist -> BHist -> Prop}
    (leftTransport : forall {x y : BHist}, Left x -> hsame x y -> Left y)
    (rightTransport : forall {x y : BHist}, Right x -> hsame x y -> Right y)
    {l l' r r' : BHist} :
    ((SumHistoryCarrier Left Right (BHist.e0 l) ∧
      SumHistoryCarrier Left Right (BHist.e0 l') ∧
        SumHistoryClassifier Left Right LeftEq RightEq (BHist.e0 l) (BHist.e0 l')) ->
      exists a : BHist, exists a' : BHist,
        Left a ∧ Left a' ∧ hsame l a ∧ hsame l' a' ∧ LeftEq a a') ∧
      ((SumHistoryCarrier Left Right (BHist.e1 r) ∧
        SumHistoryCarrier Left Right (BHist.e1 r') ∧
          SumHistoryClassifier Left Right LeftEq RightEq (BHist.e1 r) (BHist.e1 r')) ->
        exists b : BHist, exists b' : BHist,
          Right b ∧ Right b' ∧ hsame r b ∧ hsame r' b' ∧ RightEq b b') := by
  constructor
  · intro packed
    have leftCarrier := SumHistoryCarrier_e0_inversion packed.left
    have rightCarrier := SumHistoryCarrier_e0_inversion packed.right.left
    have classified :=
      (SumHistoryClassifier_generic_same_tag_exactness
        (Left := Left) (Right := Right) (LeftEq := LeftEq) (RightEq := RightEq)).left.mp
        packed.right.right
    cases leftCarrier with
    | intro c leftData =>
        cases rightCarrier with
        | intro c' rightData =>
            cases classified with
            | intro a classifiedRest =>
                cases classifiedRest with
                | intro a' classifierData =>
                    have leftCA : hsame c a :=
                      hsame_trans (hsame_symm leftData.left) classifierData.left
                    have leftC'A' : hsame c' a' :=
                      hsame_trans (hsame_symm rightData.left) classifierData.right.left
                    exact Exists.intro a
                      (Exists.intro a'
                        (And.intro (leftTransport leftData.right leftCA)
                          (And.intro (leftTransport rightData.right leftC'A')
                            (And.intro classifierData.left
                              (And.intro classifierData.right.left
                                classifierData.right.right)))))
  · intro packed
    have leftCarrier := SumHistoryCarrier_e1_inversion packed.left
    have rightCarrier := SumHistoryCarrier_e1_inversion packed.right.left
    have classified :=
      (SumHistoryClassifier_generic_same_tag_exactness
        (Left := Left) (Right := Right) (LeftEq := LeftEq) (RightEq := RightEq)).right.mp
        packed.right.right
    cases leftCarrier with
    | intro c leftData =>
        cases rightCarrier with
        | intro c' rightData =>
            cases classified with
            | intro b classifiedRest =>
                cases classifiedRest with
                | intro b' classifierData =>
                    have rightCB : hsame c b :=
                      hsame_trans (hsame_symm leftData.left) classifierData.left
                    have rightC'B' : hsame c' b' :=
                      hsame_trans (hsame_symm rightData.left) classifierData.right.left
                    exact Exists.intro b
                      (Exists.intro b'
                        (And.intro (rightTransport leftData.right rightCB)
                          (And.intro (rightTransport rightData.right rightC'B')
                            (And.intro classifierData.left
                              (And.intro classifierData.right.left
                                classifierData.right.right)))))

end BEDC.Derived.SumUp
