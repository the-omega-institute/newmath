import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem SheafBHistCoverNerveLedger_exactness_rows {ambient member overlap route germ : BHist} :
    SheafBHistCoverNerveLedger ambient member overlap route germ ->
      UnaryHistory ambient ∧ UnaryHistory member ∧ UnaryHistory overlap ∧ hsame overlap member ∧
        Cont overlap route germ ∧ hsame germ (append overlap route) := by
  intro ledger
  exact And.intro ledger.left
    (And.intro ledger.right.left
      (And.intro ledger.right.right.left
        (And.intro ledger.right.right.right.left
          (And.intro ledger.right.right.right.right ledger.right.right.right.right))))

end BEDC.Derived.SheafUp
