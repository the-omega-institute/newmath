import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem TopGroupRootOperationSourcePacket_continuity_coupling
    {group topology product inverse neighborhood ledger provenance productLedger inverseLedger
      product' inverse' ledger' : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      Cont product neighborhood productLedger ->
        Cont inverse neighborhood inverseLedger ->
          hsame product product' ->
            hsame inverse inverse' ->
              Cont product' inverse' ledger' ->
                UnaryHistory productLedger ∧ UnaryHistory inverseLedger ∧
                  hsame ledger ledger' ∧ UnaryHistory ledger' ∧ hsame provenance ledger := by
  intro package productLedgerCont inverseLedgerCont sameProduct sameInverse ledgerCont'
  have consumers :=
    TopGroupRootThresholdPackage_consumer_exhaustion package productLedgerCont inverseLedgerCont
  have stability :=
    TopGroupRootThresholdPackage_continuity_classifier_stability package sameProduct sameInverse
      ledgerCont'
  exact And.intro consumers.right.right.left
    (And.intro consumers.right.right.right.left
      (And.intro stability.left
        (And.intro stability.right.right.right consumers.right.right.right.right.right)))

theorem TopGroupRootOperationSourcePacket_operation_continuity_exhaustion
    {group topology product inverse neighborhood ledger provenance : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      exists productLedger inverseLedger operationLedger : BHist,
        Cont product neighborhood productLedger ∧ Cont inverse neighborhood inverseLedger ∧
          Cont productLedger inverseLedger operationLedger ∧ UnaryHistory productLedger ∧
            UnaryHistory inverseLedger ∧ UnaryHistory operationLedger ∧
              hsame operationLedger
                (append (append product neighborhood) (append inverse neighborhood)) ∧
                hsame ledger (append product inverse) ∧ hsame provenance ledger := by
  intro package
  let productLedger := append product neighborhood
  let inverseLedger := append inverse neighborhood
  let operationLedger := append productLedger inverseLedger
  have productRow : Cont product neighborhood productLedger := by
    rfl
  have inverseRow : Cont inverse neighborhood inverseLedger := by
    rfl
  have operationRow : Cont productLedger inverseLedger operationLedger := by
    rfl
  have operation :=
    TopGroupRootThresholdPackage_operation_ledger_obligation package productRow inverseRow
      operationRow
  exact Exists.intro productLedger
    (Exists.intro inverseLedger
      (Exists.intro operationLedger
        (And.intro productRow
          (And.intro inverseRow
            (And.intro operationRow operation)))))

end BEDC.Derived.TopGroupUp
