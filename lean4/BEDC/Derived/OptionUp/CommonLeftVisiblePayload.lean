import BEDC.Derived.OptionUp

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist

theorem TaggedOptionHistoryClassifier_common_left_visible_payload_classification
    {S : BHist -> Prop} {Rel : BHist -> BHist -> Prop}
    (rel_symm : forall {x y : BHist}, Rel x y -> Rel y x)
    (rel_trans : forall {x y z : BHist}, Rel x y -> Rel y z -> Rel x z)
    (source_hsame : forall {x y : BHist}, S x -> S y -> hsame x y -> Rel x y)
    {h k r a b c : BHist} :
    TaggedOptionHistoryClassifier S Rel h k ->
      TaggedOptionHistoryClassifier S Rel h r ->
        S a -> S b -> S c ->
          hsame h (BHist.e1 a) ->
            hsame k (BHist.e1 b) -> hsame r (BHist.e1 c) -> Rel b c := by
  intro classifierHK classifierHR sourceA sourceB sourceC sameHA sameKB sameRC
  cases classifierHK with
  | inl absentHK =>
      exact False.elim
        (not_hsame_emp_e1 (hsame_trans (hsame_symm absentHK.left) sameHA))
  | inr presentHK =>
      cases presentHK with
      | intro a0 restA0 =>
          cases restA0 with
          | intro b0 dataHK =>
              cases dataHK with
              | intro sourceA0 restHK =>
                  cases restHK with
                  | intro sourceB0 restHK =>
                      cases restHK with
                      | intro sameHA0 restHK =>
                          cases restHK with
                          | intro sameKB0 relA0B0 =>
                              cases classifierHR with
                              | inl absentHR =>
                                  exact False.elim
                                    (not_hsame_emp_e1
                                      (hsame_trans (hsame_symm absentHR.left) sameHA))
                              | inr presentHR =>
                                  cases presentHR with
                                  | intro c0 restC0 =>
                                      cases restC0 with
                                      | intro d0 dataHR =>
                                          cases dataHR with
                                          | intro sourceC0 restHR =>
                                              cases restHR with
                                              | intro sourceD0 restHR =>
                                                  cases restHR with
                                                  | intro sameHC0 restHR =>
                                                      cases restHR with
                                                      | intro sameRD0 relC0D0 =>
                                                          have sameBB0 : hsame b b0 :=
                                                            hsame_e1_iff.mp
                                                              (hsame_trans
                                                                (hsame_symm sameKB) sameKB0)
                                                          have relBB0 : Rel b b0 :=
                                                            source_hsame sourceB sourceB0
                                                              sameBB0
                                                          have relB0A0 : Rel b0 a0 :=
                                                            rel_symm relA0B0
                                                          have relBA0 : Rel b a0 :=
                                                            rel_trans relBB0 relB0A0
                                                          have sameA0A : hsame a0 a :=
                                                            hsame_e1_iff.mp
                                                              (hsame_trans
                                                                (hsame_symm sameHA0) sameHA)
                                                          have relA0A : Rel a0 a :=
                                                            source_hsame sourceA0 sourceA
                                                              sameA0A
                                                          have relBA : Rel b a :=
                                                            rel_trans relBA0 relA0A
                                                          have sameAC0 : hsame a c0 :=
                                                            hsame_e1_iff.mp
                                                              (hsame_trans
                                                                (hsame_symm sameHA) sameHC0)
                                                          have relAC0 : Rel a c0 :=
                                                            source_hsame sourceA sourceC0
                                                              sameAC0
                                                          have relAD0 : Rel a d0 :=
                                                            rel_trans relAC0 relC0D0
                                                          have sameD0C : hsame d0 c :=
                                                            hsame_e1_iff.mp
                                                              (hsame_trans
                                                                (hsame_symm sameRD0) sameRC)
                                                          have relD0C : Rel d0 c :=
                                                            source_hsame sourceD0 sourceC
                                                              sameD0C
                                                          exact rel_trans relBA
                                                            (rel_trans relAD0 relD0C)

end BEDC.Derived.OptionUp
