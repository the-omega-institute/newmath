import BEDC.Derived.OptionUp

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist

theorem TaggedOptionHistoryClassifier_visible_branch_inversion {S : BHist -> Prop}
    {Rel : BHist -> BHist -> Prop} {h k : BHist} :
    TaggedOptionHistoryClassifier S Rel h k ->
      (hsame h BHist.Empty -> hsame k BHist.Empty) /\
        (forall {a : BHist}, S a -> hsame h (BHist.e1 a) ->
          exists a' : BHist, exists b : BHist,
            S a' /\ S b /\ hsame a a' /\ Rel a' b /\ hsame k (BHist.e1 b)) := by
  intro classifier
  constructor
  · intro sameHEmpty
    cases classifier with
    | inl absentPair =>
        exact absentPair.right
    | inr presentPair =>
        cases presentPair with
        | intro a' restA =>
            cases restA with
            | intro b data =>
                cases data with
                | intro _sourceA' rest =>
                    cases rest with
                    | intro _sourceB rest =>
                        cases rest with
                        | intro sameHPresent _ =>
                            exact False.elim
                              (not_hsame_emp_e1
                                (hsame_trans (hsame_symm sameHEmpty) sameHPresent))
  · intro a sourceA sameHPresentA
    cases classifier with
    | inl absentPair =>
        exact False.elim
          (not_hsame_emp_e1
            (hsame_trans (hsame_symm absentPair.left) sameHPresentA))
    | inr presentPair =>
        cases presentPair with
        | intro a' restA =>
            cases restA with
            | intro b data =>
                cases data with
                | intro sourceA' rest =>
                    cases rest with
                    | intro sourceB rest =>
                        cases rest with
                        | intro sameHPresentA' rest =>
                            cases rest with
                            | intro sameKPresentB relA'B =>
                                have samePayload : hsame a a' :=
                                  hsame_e1_iff.mp
                                    (hsame_trans (hsame_symm sameHPresentA) sameHPresentA')
                                exact Exists.intro a'
                                  (Exists.intro b
                                    (And.intro sourceA'
                                      (And.intro sourceB
                                        (And.intro samePayload
                                          (And.intro relA'B sameKPresentB)))))

end BEDC.Derived.OptionUp
