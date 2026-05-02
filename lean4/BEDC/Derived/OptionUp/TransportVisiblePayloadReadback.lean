import BEDC.Derived.OptionUp

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist

theorem TaggedOptionHistoryClassifier_transport_visible_payload_readback {S : BHist → Prop}
    {Rel : BHist → BHist → Prop} {h k u v x y : BHist} :
    TaggedOptionHistoryClassifier S Rel h k → hsame h u → hsame k v →
      hsame u (BHist.e1 x) → hsame v (BHist.e1 y) →
        ∃ a : BHist, ∃ b : BHist,
          S a ∧ S b ∧ hsame x a ∧ hsame y b ∧ Rel a b := by
  intro classifier sameHU sameKV sameUVisible sameVVisible
  cases classifier with
  | inl absent =>
      have sameUEmpty : hsame u BHist.Empty := hsame_trans (hsame_symm sameHU) absent.left
      exact False.elim
        (not_hsame_emp_e1 (hsame_trans (hsame_symm sameUEmpty) sameUVisible))
  | inr present =>
      cases present with
      | intro a restA =>
          cases restA with
          | intro b data =>
              cases data with
              | intro sourceA rest =>
                  cases rest with
                  | intro sourceB rest =>
                      cases rest with
                      | intro sameHPresent rest =>
                          cases rest with
                          | intro sameKPresent relAB =>
                              have sameUPresent : hsame u (BHist.e1 a) :=
                                hsame_trans (hsame_symm sameHU) sameHPresent
                              have sameVPresent : hsame v (BHist.e1 b) :=
                                hsame_trans (hsame_symm sameKV) sameKPresent
                              have sameXA : hsame x a :=
                                hsame_e1_iff.mp
                                  (hsame_trans (hsame_symm sameUVisible) sameUPresent)
                              have sameYB : hsame y b :=
                                hsame_e1_iff.mp
                                  (hsame_trans (hsame_symm sameVVisible) sameVPresent)
                              exact Exists.intro a
                                (Exists.intro b
                                  (And.intro sourceA
                                    (And.intro sourceB
                                      (And.intro sameXA
                                        (And.intro sameYB relAB)))))

end BEDC.Derived.OptionUp
