import BEDC.Derived.OptionUp

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist

theorem TaggedOptionHistoryClassifier_visible_endpoint_pair_readback {S : BHist -> Prop}
    {Rel : BHist -> BHist -> Prop} {h k a b : BHist} :
    TaggedOptionHistoryClassifier S Rel h k -> hsame h (BHist.e1 a) ->
      hsame k (BHist.e1 b) ->
        exists a0 b0 : BHist,
          S a0 /\ S b0 /\ hsame a a0 /\ hsame b b0 /\ Rel a0 b0 := by
  intro classifier sameH sameK
  cases classifier with
  | inl absentPair =>
      exact False.elim
        (not_hsame_emp_e1 (hsame_trans (hsame_symm absentPair.left) sameH))
  | inr presentPair =>
      cases presentPair with
      | intro a0 restA =>
          cases restA with
          | intro b0 data =>
              cases data with
              | intro sourceA rest =>
                  cases rest with
                  | intro sourceB rest =>
                      cases rest with
                      | intro sameHPresent rest =>
                          cases rest with
                          | intro sameKPresent rel =>
                              exact
                                Exists.intro a0
                                  (Exists.intro b0
                                    (And.intro sourceA
                                      (And.intro sourceB
                                        (And.intro
                                          (hsame_e1_iff.mp
                                            (hsame_trans (hsame_symm sameH) sameHPresent))
                                          (And.intro
                                            (hsame_e1_iff.mp
                                              (hsame_trans (hsame_symm sameK) sameKPresent))
                                            rel)))))

end BEDC.Derived.OptionUp
