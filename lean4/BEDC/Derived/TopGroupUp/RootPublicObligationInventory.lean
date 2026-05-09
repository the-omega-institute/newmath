import BEDC.Derived.TopGroupUp.RootCarrierObligations

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.GroupUp
open BEDC.Derived.TopologyUp

theorem TopGroupRootThresholdPackage_root_public_obligation_inventory
    {group topology product inverse neighborhood ledger provenance productLedger inverseLedger
      operationLedger sourceFiber : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      Cont product neighborhood productLedger ->
        Cont inverse neighborhood inverseLedger ->
          Cont productLedger inverseLedger operationLedger ->
            Cont (append group topology) ledger sourceFiber ->
              GroupSingletonCarrier group ∧ TopologySingletonCarrier topology ∧
                Cont group topology product ∧ Cont product inverse ledger ∧
                  UnaryHistory productLedger ∧ UnaryHistory inverseLedger ∧
                    UnaryHistory operationLedger ∧ UnaryHistory sourceFiber ∧
                      hsame operationLedger (append productLedger inverseLedger) ∧
                        hsame sourceFiber (append (append group topology) ledger) ∧
                          hsame provenance ledger := by
  intro package productRow inverseRow operationRow sourceFiberRow
  have operationInventory :=
    TopGroupRootThresholdPackage_operation_ledger_obligation package productRow inverseRow
      operationRow
  have sourceFiberInventory :=
    TopGroupRootThresholdPackage_root_source_fiber_carrier_obligation package sourceFiberRow
  exact And.intro sourceFiberInventory.left
    (And.intro sourceFiberInventory.right.left
      (And.intro sourceFiberInventory.right.right.left
        (And.intro sourceFiberInventory.right.right.right.left
          (And.intro operationInventory.left
            (And.intro operationInventory.right.left
              (And.intro operationInventory.right.right.left
                (And.intro sourceFiberInventory.right.right.right.right.left
                  (And.intro operationRow
                    (And.intro sourceFiberInventory.right.right.right.right.right.left
                      sourceFiberInventory.right.right.right.right.right.right)))))))))

end BEDC.Derived.TopGroupUp
