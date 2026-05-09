import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.Derived.GroupUp
open BEDC.Derived.TopologyUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem TopGroupRootThresholdPackage_public_obligation_inventory
    {group topology product inverse neighborhood ledger provenance productLedger inverseLedger
      consumerLedger : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      Cont product neighborhood productLedger ->
        Cont inverse neighborhood inverseLedger ->
          Cont productLedger inverseLedger consumerLedger ->
            GroupSingletonCarrier group ∧ TopologySingletonCarrier topology ∧
              Cont group topology product ∧ Cont product inverse ledger ∧
                Cont ledger BHist.Empty provenance ∧ UnaryHistory productLedger ∧
                  UnaryHistory inverseLedger ∧ UnaryHistory consumerLedger ∧
                    hsame consumerLedger
                      (append (append product neighborhood) (append inverse neighborhood)) ∧
                      hsame provenance ledger := by
  intro package productRow inverseRow consumerRow
  have rows := TopGroupRootThresholdPackage_shared_source_rows package
  have obligation :=
    TopGroupRootThresholdPackage_operation_ledger_obligation package productRow inverseRow
      consumerRow
  exact And.intro package.left
    (And.intro package.right.left
      (And.intro rows.left
        (And.intro rows.right.left
          (And.intro rows.right.right.left
            (And.intro obligation.left
              (And.intro obligation.right.left
                (And.intro obligation.right.right.left
                  (And.intro obligation.right.right.right.left
                    obligation.right.right.right.right.right))))))))

end BEDC.Derived.TopGroupUp
