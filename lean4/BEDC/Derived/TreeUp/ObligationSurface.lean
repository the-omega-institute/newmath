import BEDC.Derived.TreeUp

namespace BEDC.Derived.TreeUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem TreeBHistObligationCarrier_stability_ledger_obligation
    {root source target edge connected acyclic repr package acyclic' package' : BHist} :
    TreeBHistObligationCarrier root source target edge connected acyclic repr package ->
      hsame acyclic acyclic' ->
        hsame package package' ->
          TreeBHistObligationCarrier root source target edge connected acyclic' repr package' ∧
            hsame acyclic' BHist.Empty ∧ hsame package' (append source target) := by
  intro carrier sameAcyclic samePackage
  have acyclicEmpty : hsame acyclic' BHist.Empty :=
    hsame_trans (hsame_symm sameAcyclic) carrier.right.right.right.left
  have packageTarget : hsame package' (append source target) :=
    hsame_trans (hsame_symm samePackage) carrier.right.right.right.right.right
  exact And.intro
    (And.intro carrier.left
      (And.intro carrier.right.left
        (And.intro carrier.right.right.left
          (And.intro acyclicEmpty
            (And.intro carrier.right.right.right.right.left packageTarget)))))
    (And.intro acyclicEmpty packageTarget)

end BEDC.Derived.TreeUp
