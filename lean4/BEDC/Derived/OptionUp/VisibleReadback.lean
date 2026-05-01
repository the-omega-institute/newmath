import BEDC.Derived.OptionUp

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist

theorem TaggedOptionHistoryCarrier_single_valued_visible_readback {S : BHist → Prop}
    {h : BHist} :
    TaggedOptionHistoryCarrier S h →
      (hsame h BHist.Empty ∧ ((∃ a : BHist, S a ∧ hsame h (BHist.e1 a)) → False)) ∨
        (∃ a : BHist,
          S a ∧ hsame h (BHist.e1 a) ∧ (hsame h BHist.Empty → False) ∧
            (∀ a' : BHist, S a' → hsame h (BHist.e1 a') → hsame a a')) := by
  intro carrier
  have partition := TaggedOptionHistoryCarrier_exclusive_branch_partition carrier
  cases partition with
  | inl absent =>
      exact Or.inl absent
  | inr present =>
      cases present with
      | intro a data =>
          cases data with
          | intro sourceA rest =>
              cases rest with
              | intro visibleA notEmpty =>
                  exact Or.inr
                    (Exists.intro a
                      (And.intro sourceA
                        (And.intro visibleA
                          (And.intro notEmpty
                            (by
                              intro a' _sourceA' visibleA'
                              exact hsame_e1_iff.mp
                                (hsame_trans (hsame_symm visibleA) visibleA'))))))

end BEDC.Derived.OptionUp
