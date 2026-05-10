import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.GroupUp
open BEDC.Derived.TopologyUp

theorem TopGroupRootThresholdPackage_continuity_consumer_exhaustion
    {group topology product inverse neighborhood ledger provenance productLedger inverseLedger :
      BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      Cont product neighborhood productLedger ->
        Cont inverse neighborhood inverseLedger ->
          GroupSingletonCarrier group ∧ TopologySingletonCarrier topology ∧
            UnaryHistory productLedger ∧ UnaryHistory inverseLedger ∧
              Cont product neighborhood productLedger ∧ Cont inverse neighborhood inverseLedger ∧
                Cont product inverse ledger ∧ hsame provenance ledger := by
  intro package productLedgerCont inverseLedgerCont
  have boundary := TopGroupRootThresholdPackage_source_coupled_continuity_boundary package
  have productLedgerUnary : UnaryHistory productLedger :=
    unary_cont_closed boundary.right.right.left boundary.right.right.right.right.left
      productLedgerCont
  have inverseLedgerUnary : UnaryHistory inverseLedger :=
    unary_cont_closed boundary.right.right.right.left boundary.right.right.right.right.left
      inverseLedgerCont
  exact And.intro boundary.left
    (And.intro boundary.right.left
      (And.intro productLedgerUnary
        (And.intro inverseLedgerUnary
          (And.intro productLedgerCont
            (And.intro inverseLedgerCont
              (And.intro package.right.right.right.right.right.left
                boundary.right.right.right.right.right.right.right))))))

end BEDC.Derived.TopGroupUp
