import BEDC.Derived.OptionUp

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist

theorem TaggedOptionHistoryClassifier_composite_right_visible_readback {S : BHist → Prop}
    {Rel : BHist → BHist → Prop}
    (rel_trans : ∀ {a b c : BHist}, Rel a b → Rel b c → Rel a c)
    {h k r : BHist} :
    TaggedOptionHistoryClassifier S Rel h k → TaggedOptionHistoryClassifier S Rel k r →
      (hsame r BHist.Empty → hsame h BHist.Empty) ∧
        (∀ {a : BHist}, S a → hsame r (BHist.e1 a) →
          ∃ b : BHist, ∃ a' : BHist,
            S b ∧ S a' ∧ hsame a a' ∧ Rel b a' ∧ hsame h (BHist.e1 b)) := by
  intro classifierHK classifierKR
  exact TaggedOptionHistoryClassifier_right_visible_branch_inversion
    (TaggedOptionHistoryClassifier_trans (S := S) (Rel := Rel) rel_trans classifierHK
      classifierKR)

end BEDC.Derived.OptionUp
