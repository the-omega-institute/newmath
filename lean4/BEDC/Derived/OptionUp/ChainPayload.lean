import BEDC.Derived.OptionUp

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist

theorem TaggedOptionHistoryClassifier_present_chain_payload_witness {S : BHist -> Prop}
    {Rel : BHist -> BHist -> Prop} {h k r a c : BHist} :
    TaggedOptionHistoryClassifier S Rel h k ->
      TaggedOptionHistoryClassifier S Rel k r ->
        hsame h (BHist.e1 a) ->
          hsame r (BHist.e1 c) ->
            ∃ a0 b b' c0 : BHist,
              S a0 ∧ S b ∧ S b' ∧ S c0 ∧ hsame a a0 ∧ hsame b b' ∧
                hsame c0 c ∧ Rel a0 b ∧ Rel b' c0 := by
  intro classifierHK classifierKR sameHPresentA sameRPresentC
  cases classifierHK with
  | inl absentHK =>
      exact False.elim
        (not_hsame_emp_e1 (hsame_trans (hsame_symm absentHK.left) sameHPresentA))
  | inr presentHK =>
      cases presentHK with
      | intro a0 restA0 =>
          cases restA0 with
          | intro b dataHK =>
              cases dataHK with
              | intro sourceA0 restHK =>
                  cases restHK with
                  | intro sourceB restHK =>
                      cases restHK with
                      | intro sameHPresentA0 restHK =>
                          cases restHK with
                          | intro sameKPresentB relA0B =>
                              cases classifierKR with
                              | inl absentKR =>
                                  exact False.elim
                                    (not_hsame_e1_empty
                                      (hsame_trans (hsame_symm sameRPresentC)
                                        absentKR.right))
                              | inr presentKR =>
                                  cases presentKR with
                                  | intro b' restB' =>
                                      cases restB' with
                                      | intro c0 dataKR =>
                                          cases dataKR with
                                          | intro sourceB' restKR =>
                                              cases restKR with
                                              | intro sourceC0 restKR =>
                                                  cases restKR with
                                                  | intro sameKPresentB' restKR =>
                                                      cases restKR with
                                                      | intro sameRPresentC0 relB'C0 =>
                                                          have sameAA0 : hsame a a0 :=
                                                            hsame_e1_iff.mp
                                                              (hsame_trans
                                                                (hsame_symm sameHPresentA)
                                                                sameHPresentA0)
                                                          have sameBB' : hsame b b' :=
                                                            hsame_e1_iff.mp
                                                              (hsame_trans
                                                                (hsame_symm sameKPresentB)
                                                                sameKPresentB')
                                                          have sameC0C : hsame c0 c :=
                                                            hsame_e1_iff.mp
                                                              (hsame_trans
                                                                (hsame_symm sameRPresentC0)
                                                                sameRPresentC)
                                                          exact
                                                            Exists.intro a0
                                                              (Exists.intro b
                                                                (Exists.intro b'
                                                                  (Exists.intro c0
                                                                    (And.intro sourceA0
                                                                      (And.intro sourceB
                                                                        (And.intro sourceB'
                                                                          (And.intro sourceC0
                                                                            (And.intro sameAA0
                                                                              (And.intro sameBB'
                                                                                (And.intro sameC0C
                                                                                  (And.intro relA0B
                                                                                    relB'C0)))))))))))

end BEDC.Derived.OptionUp
