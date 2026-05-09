import BEDC.FKernel.Cont
import BEDC.FKernel.Hist

namespace BEDC.Derived.RingOfIntegersUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

def RingOfIntegersDedekindSourceCarrier
    (N Z eta E kappa tau rho : BHist) : Prop :=
  Cont N Z eta ∧
    hsame (append eta E) kappa ∧
      hsame (append kappa tau) rho

theorem RingOfIntegersDedekindSourceCarrier_equation_ledger_unique
    {N Z eta E E' kappa tau rho : BHist} :
    RingOfIntegersDedekindSourceCarrier N Z eta E kappa tau rho ->
      RingOfIntegersDedekindSourceCarrier N Z eta E' kappa tau rho ->
        hsame (append eta E) (append eta E') ∧ hsame E E' := by
  intro left right
  have sameLedgerRows : hsame (append eta E) (append eta E') :=
    hsame_trans left.right.left (hsame_symm right.right.left)
  exact And.intro sameLedgerRows (append_left_cancel (h := eta) sameLedgerRows)

end BEDC.Derived.RingOfIntegersUp
