import BEDC.Derived.SumUp.Ledger

namespace BEDC.Derived.SumUp

open BEDC.FKernel.Hist

theorem SumHistoryLedgerChain_branch_exactness_iff {Left Right : BHist -> Prop}
    {rho z : BHist} :
    SumHistoryLedgerChain Left Right rho z ↔
      ((exists l : BHist, exists l' : BHist,
          Left l ∧ Left l' ∧ hsame rho (BHist.e0 l) ∧ hsame z (BHist.e0 l') ∧
            hsame l l') ∨
        (exists r : BHist, exists r' : BHist,
          Right r ∧ Right r' ∧ hsame rho (BHist.e1 r) ∧ hsame z (BHist.e1 r') ∧
            hsame r r')) := by
  constructor
  · intro chain
    exact SumHistoryLedgerChain_branch_exactness chain
  · intro branch
    cases branch with
    | inl leftBranch =>
        cases leftBranch with
        | intro l leftRest =>
            cases leftRest with
            | intro l' data =>
                have sameVisible : hsame z (BHist.e0 l) :=
                  hsame_trans data.right.right.right.left
                    (hsame_e0_iff.mpr (hsame_symm data.right.right.right.right))
                have ledger : SumHistoryLedgerPolicy Left Right rho z :=
                  SumHistoryLedgerPolicy_raw_visible_branch_exactness.mpr
                    (Or.inl
                      (Exists.intro l
                        (And.intro data.left
                          (And.intro data.right.right.left sameVisible))))
                exact SumHistoryLedgerChain.single ledger
    | inr rightBranch =>
        cases rightBranch with
        | intro r rightRest =>
            cases rightRest with
            | intro r' data =>
                have sameVisible : hsame z (BHist.e1 r) :=
                  hsame_trans data.right.right.right.left
                    (hsame_e1_iff.mpr (hsame_symm data.right.right.right.right))
                have ledger : SumHistoryLedgerPolicy Left Right rho z :=
                  SumHistoryLedgerPolicy_raw_visible_branch_exactness.mpr
                    (Or.inr
                      (Exists.intro r
                        (And.intro data.left
                          (And.intro data.right.right.left sameVisible))))
                exact SumHistoryLedgerChain.single ledger

end BEDC.Derived.SumUp
