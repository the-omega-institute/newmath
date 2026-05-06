import BEDC.Derived.OptionUp

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist

def TaggedOptionHistoryLedger (S : BHist -> Prop) (h : BHist) : Prop :=
  hsame h BHist.Empty ∨ ∃ a : BHist, S a ∧ hsame h (BHist.e1 a)

theorem TaggedOptionHistoryLedger_present_payload_readback {S : BHist -> Prop} {h p : BHist} :
    TaggedOptionHistoryLedger S h -> hsame h (BHist.e1 p) ->
      ∃ a : BHist, S a ∧ hsame p a := by
  intro ledger samePresent
  cases ledger with
  | inl sameEmpty =>
      have emptyPresent : hsame BHist.Empty (BHist.e1 p) :=
        hsame_trans (hsame_symm sameEmpty) samePresent
      exact False.elim (not_hsame_emp_e1 emptyPresent)
  | inr payload =>
      cases payload with
      | intro a data =>
          have samePayload : hsame p a :=
            hsame_e1_iff.mp (hsame_trans (hsame_symm samePresent) data.right)
          exact Exists.intro a (And.intro data.left samePayload)

end BEDC.Derived.OptionUp
