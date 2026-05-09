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

end BEDC.Derived.TopGroupUp
