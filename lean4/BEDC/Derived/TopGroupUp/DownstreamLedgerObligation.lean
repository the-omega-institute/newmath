import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem TopGroupRootThresholdPackage_downstream_ledger_obligation
    {group topology product inverse neighborhood ledger provenance productLedger inverseLedger
      consumerLedger : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      Cont product neighborhood productLedger ->
        Cont inverse neighborhood inverseLedger ->
          Cont productLedger inverseLedger consumerLedger ->
            Cont product inverse ledger ∧ Cont ledger BHist.Empty provenance ∧
              UnaryHistory ledger ∧ UnaryHistory provenance ∧ UnaryHistory consumerLedger ∧
                hsame consumerLedger (append productLedger inverseLedger) := by
  intro package productLedgerCont inverseLedgerCont consumerLedgerCont
  have sourceRows := TopGroupRootThresholdPackage_shared_source_rows package
  have operationRows :=
    TopGroupRootThresholdPackage_operation_ledger_obligation package productLedgerCont
      inverseLedgerCont consumerLedgerCont
  exact And.intro sourceRows.right.left
    (And.intro sourceRows.right.right.left
      (And.intro sourceRows.right.right.right.left
        (And.intro sourceRows.right.right.right.right
          (And.intro operationRows.right.right.left consumerLedgerCont))))

theorem TopGroupRootSourceFiber_continuity_obligation
    {group topology product inverse neighborhood ledger provenance productLedger productLedger'
      inverseLedger inverseLedger' product' inverse' neighborhood' : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      hsame product product' ->
        hsame inverse inverse' ->
          hsame neighborhood neighborhood' ->
            Cont product neighborhood productLedger ->
              Cont product' neighborhood' productLedger' ->
                Cont inverse neighborhood inverseLedger ->
                  Cont inverse' neighborhood' inverseLedger' ->
                    hsame productLedger productLedger' ∧ hsame inverseLedger inverseLedger' ∧
                      UnaryHistory productLedger' ∧ UnaryHistory inverseLedger' ∧
                        hsame provenance ledger := by
  intro package sameProduct sameInverse sameNeighborhood productLedgerCont productLedgerCont'
    inverseLedgerCont inverseLedgerCont'
  have productTransport :=
    TopGroupRootThresholdPackage_product_neighborhood_transport package sameProduct sameNeighborhood
      productLedgerCont productLedgerCont'
  have inverseTransport :=
    TopGroupRootThresholdPackage_inverse_neighborhood_transport package sameInverse sameNeighborhood
      inverseLedgerCont inverseLedgerCont'
  exact And.intro productTransport.left
    (And.intro inverseTransport.left
      (And.intro productTransport.right.right.right
        (And.intro inverseTransport.right.right.right.left
          inverseTransport.right.right.right.right)))

end BEDC.Derived.TopGroupUp
