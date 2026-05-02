import BEDC.Derived.OptionUp

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist

theorem TaggedOptionHistoryCarrier_present_hsame_readback {S : BHist → Prop} {h p : BHist} :
    TaggedOptionHistoryCarrier S h →
      hsame h (BHist.e1 p) → ∃ a : BHist, S a ∧ hsame p a := by
  intro carrier samePresent
  cases carrier with
  | inl emptyCase =>
      exact False.elim
        (not_hsame_emp_e1 (hsame_trans (hsame_symm emptyCase) samePresent))
  | inr presentCase =>
      cases presentCase with
      | intro a data =>
          cases data with
          | intro sourceA sameEndpoint =>
              exact Exists.intro a
                (And.intro sourceA
                  (hsame_e1_iff.mp (hsame_trans (hsame_symm samePresent) sameEndpoint)))

theorem TaggedOptionHistoryCarrier_present_source_transport {S : BHist → Prop}
    (source_transport : ∀ {x y : BHist}, hsame x y -> S x -> S y) {h : BHist} :
    TaggedOptionHistoryCarrier S (BHist.e1 h) -> S h := by
  intro carrier
  have present := TaggedOptionHistoryCarrier_present_exactness.mp carrier
  cases present with
  | intro a data =>
      cases data with
      | intro sourceA samePayload =>
          exact source_transport (hsame_symm samePayload) sourceA

theorem TaggedOptionHistoryCarrier_e1_source_iff {S : BHist → Prop}
    (source_transport : ∀ {x y : BHist}, hsame x y → S x → S y) {h : BHist} :
    TaggedOptionHistoryCarrier S (BHist.e1 h) ↔ S h := by
  constructor
  · intro carrier
    exact TaggedOptionHistoryCarrier_present_source_transport source_transport carrier
  · intro sourceH
    exact Or.inr (Exists.intro h (And.intro sourceH (hsame_refl (BHist.e1 h))))

end BEDC.Derived.OptionUp
