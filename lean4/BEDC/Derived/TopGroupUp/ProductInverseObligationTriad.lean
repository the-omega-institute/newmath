import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.GroupUp
open BEDC.Derived.TopologyUp

theorem TopGroupRootThresholdPackage_product_inverse_obligation_triad
    {group topology product inverse neighborhood ledger provenance productLedger inverseLedger :
      BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      Cont product neighborhood productLedger ->
        Cont inverse neighborhood inverseLedger ->
          TopologySingletonCarrier topology ∧ GroupSingletonCarrier group ∧
            Cont product neighborhood productLedger ∧ Cont inverse neighborhood inverseLedger ∧
              UnaryHistory productLedger ∧ UnaryHistory inverseLedger ∧
                hsame ledger (append product inverse) ∧ hsame provenance ledger := by
  intro package productCont inverseCont
  have boundary :=
    TopGroupRootThresholdPackage_source_coupled_continuity_boundary package
  have productLedgerUnary : UnaryHistory productLedger :=
    unary_cont_closed boundary.right.right.left boundary.right.right.right.right.left productCont
  have inverseLedgerUnary : UnaryHistory inverseLedger :=
    unary_cont_closed boundary.right.right.right.left boundary.right.right.right.right.left
      inverseCont
  exact
    And.intro boundary.right.left
      (And.intro boundary.left
        (And.intro productCont
          (And.intro inverseCont
            (And.intro productLedgerUnary
              (And.intro inverseLedgerUnary
                (And.intro boundary.right.right.right.right.right.right.left
                  boundary.right.right.right.right.right.right.right))))))

end BEDC.Derived.TopGroupUp
