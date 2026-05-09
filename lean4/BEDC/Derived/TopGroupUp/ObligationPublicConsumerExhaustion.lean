import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.Derived.GroupUp
open BEDC.Derived.TopologyUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem TopGroupRootThresholdPackage_obligation_public_consumer_exhaustion
    {group topology product inverse neighborhood ledger provenance productLedger inverseLedger
      consumerLedger exportLedger : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      Cont product neighborhood productLedger ->
        Cont inverse neighborhood inverseLedger ->
          Cont productLedger inverseLedger consumerLedger ->
            Cont consumerLedger provenance exportLedger ->
              GroupSingletonCarrier group ∧ TopologySingletonCarrier topology ∧
                UnaryHistory consumerLedger ∧ UnaryHistory exportLedger ∧
                  hsame consumerLedger
                    (append (append product neighborhood) (append inverse neighborhood)) ∧
                    hsame exportLedger (append consumerLedger provenance) ∧
                      hsame ledger (append product inverse) ∧ hsame provenance ledger := by
  intro package productLedgerCont inverseLedgerCont consumerLedgerCont exportLedgerCont
  have rows :=
    TopGroupRootThresholdPackage_operation_ledger_obligation package productLedgerCont
      inverseLedgerCont consumerLedgerCont
  have boundary :=
    TopGroupRootThresholdPackage_source_coupled_continuity_boundary package
  have provenanceUnary : UnaryHistory provenance :=
    unary_transport boundary.right.right.right.right.right.left
      (hsame_symm rows.right.right.right.right.right)
  have exportLedgerUnary : UnaryHistory exportLedger :=
    unary_cont_closed rows.right.right.left provenanceUnary exportLedgerCont
  exact And.intro boundary.left
    (And.intro boundary.right.left
      (And.intro rows.right.right.left
        (And.intro exportLedgerUnary
          (And.intro rows.right.right.right.left
            (And.intro exportLedgerCont
              (And.intro rows.right.right.right.right.left rows.right.right.right.right.right))))))

end BEDC.Derived.TopGroupUp
