import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.GroupUp
open BEDC.Derived.TopologyUp

theorem TopGroupRootSourceFiber_export_exactness
    {group topology product inverse neighborhood ledger provenance productLedger inverseLedger
      exportLedger consumerLedger : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      Cont product neighborhood productLedger ->
        Cont inverse neighborhood inverseLedger ->
          Cont productLedger inverseLedger exportLedger ->
            Cont exportLedger provenance consumerLedger ->
              GroupSingletonCarrier group ∧ TopologySingletonCarrier topology ∧
                UnaryHistory exportLedger ∧ UnaryHistory consumerLedger ∧
                  hsame exportLedger (append productLedger inverseLedger) ∧
                    hsame consumerLedger (append exportLedger provenance) ∧
                      hsame ledger (append product inverse) ∧ hsame provenance ledger := by
  intro package productLedgerCont inverseLedgerCont exportLedgerCont consumerLedgerCont
  have exportRows :=
    TopGroupRootSourceFiber_export_continuity package productLedgerCont inverseLedgerCont
      exportLedgerCont
  have sourceRows := TopGroupRootThresholdPackage_shared_source_rows package
  have consumerLedgerUnary : UnaryHistory consumerLedger :=
    unary_cont_closed exportRows.right.right.left sourceRows.right.right.right.right
      consumerLedgerCont
  exact And.intro package.left
    (And.intro package.right.left
      (And.intro exportRows.right.right.left
        (And.intro consumerLedgerUnary
          (And.intro exportRows.right.right.right.left
            (And.intro consumerLedgerCont
              (And.intro exportRows.right.right.right.right.left
                exportRows.right.right.right.right.right))))))

end BEDC.Derived.TopGroupUp
