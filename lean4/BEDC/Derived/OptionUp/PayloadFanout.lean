import BEDC.Derived.OptionUp

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist

theorem TaggedOptionHistoryClassifier_left_present_payload_fanout {S : BHist -> Prop}
    {Rel : BHist -> BHist -> Prop} {h k r a : BHist} :
    TaggedOptionHistoryClassifier S Rel h k -> TaggedOptionHistoryClassifier S Rel h r ->
      hsame h (BHist.e1 a) ->
        (exists b a' : BHist, S b /\ S a' /\ hsame a a' /\ Rel a' b /\
          hsame k (BHist.e1 b)) /\
          (exists c a'' : BHist, S c /\ S a'' /\ hsame a a'' /\ Rel a'' c /\
            hsame r (BHist.e1 c)) := by
  intro left right sameHPresent
  constructor
  · cases left with
    | inl absent =>
        exact False.elim
          (not_hsame_emp_e1 (hsame_trans (hsame_symm absent.left) sameHPresent))
    | inr present =>
        cases present with
        | intro source restSource =>
            cases restSource with
            | intro target data =>
                have samePayload : hsame a source :=
                  hsame_e1_iff.mp
                    (hsame_trans (hsame_symm sameHPresent) data.right.right.left)
                exact Exists.intro target
                  (Exists.intro source
                    (And.intro data.right.left
                      (And.intro data.left
                        (And.intro samePayload
                          (And.intro data.right.right.right.right
                            data.right.right.right.left)))))
  · cases right with
    | inl absent =>
        exact False.elim
          (not_hsame_emp_e1 (hsame_trans (hsame_symm absent.left) sameHPresent))
    | inr present =>
        cases present with
        | intro source restSource =>
            cases restSource with
            | intro target data =>
                have samePayload : hsame a source :=
                  hsame_e1_iff.mp
                    (hsame_trans (hsame_symm sameHPresent) data.right.right.left)
                exact Exists.intro target
                  (Exists.intro source
                    (And.intro data.right.left
                      (And.intro data.left
                        (And.intro samePayload
                          (And.intro data.right.right.right.right
                            data.right.right.right.left)))))

theorem TaggedOptionHistoryClassifier_hsame_shared_left_visible_right_deterministic
    {S : BHist -> Prop} {h k r a b c : BHist} :
    TaggedOptionHistoryClassifier S hsame h k -> TaggedOptionHistoryClassifier S hsame h r ->
      hsame h (BHist.e1 a) -> hsame k (BHist.e1 b) -> hsame r (BHist.e1 c) ->
        hsame b c := by
  intro left right sameH sameK sameR
  cases left with
  | inl absentLeft =>
      exact False.elim
        (not_hsame_emp_e1 (hsame_trans (hsame_symm absentLeft.left) sameH))
  | inr presentLeft =>
      cases presentLeft with
      | intro leftSource restLeftSource =>
          cases restLeftSource with
          | intro leftTarget leftData =>
              cases leftData with
              | intro _sourceLeft restLeft =>
                  cases restLeft with
                  | intro _sourceTarget restLeft =>
                      cases restLeft with
                      | intro sameHLeft restLeft =>
                          cases restLeft with
                          | intro sameKLeft relLeft =>
                              cases right with
                              | inl absentRight =>
                                  exact False.elim
                                    (not_hsame_emp_e1
                                      (hsame_trans (hsame_symm absentRight.left) sameH))
                              | inr presentRight =>
                                  cases presentRight with
                                  | intro rightSource restRightSource =>
                                      cases restRightSource with
                                      | intro rightTarget rightData =>
                                          cases rightData with
                                          | intro _sourceRight restRight =>
                                              cases restRight with
                                              | intro _sourceRightTarget restRight =>
                                                  cases restRight with
                                                  | intro sameHRight restRight =>
                                                      cases restRight with
                                                      | intro sameRRight relRight =>
                                                          have sameALeftSource :
                                                              hsame a leftSource :=
                                                            hsame_e1_iff.mp
                                                              (hsame_trans
                                                                (hsame_symm sameH) sameHLeft)
                                                          have sameARightSource :
                                                              hsame a rightSource :=
                                                            hsame_e1_iff.mp
                                                              (hsame_trans
                                                                (hsame_symm sameH) sameHRight)
                                                          have sameBLeftTarget :
                                                              hsame b leftTarget :=
                                                            hsame_e1_iff.mp
                                                              (hsame_trans
                                                                (hsame_symm sameK) sameKLeft)
                                                          have sameCRightTarget :
                                                              hsame c rightTarget :=
                                                            hsame_e1_iff.mp
                                                              (hsame_trans
                                                                (hsame_symm sameR) sameRRight)
                                                          exact hsame_trans sameBLeftTarget
                                                            (hsame_trans (hsame_symm relLeft)
                                                              (hsame_trans
                                                                (hsame_symm sameALeftSource)
                                                                (hsame_trans sameARightSource
                                                                  (hsame_trans relRight
                                                                    (hsame_symm
                                                                      sameCRightTarget)))))

end BEDC.Derived.OptionUp
