import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.GroupUp
open BEDC.Derived.TopologyUp

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

theorem TopGroupRootThresholdPackage_root_source_pair_exactness
    {group topology product inverse neighborhood ledger provenance sourceLedger : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      Cont group topology product ->
        Cont ledger BHist.Empty sourceLedger ->
          GroupSingletonCarrier group ∧ TopologySingletonCarrier topology ∧
            UnaryHistory product ∧ UnaryHistory sourceLedger ∧
              hsame product (append group topology) ∧ hsame sourceLedger ledger ∧
                hsame provenance ledger := by
  intro package productCont sourceLedgerCont
  have groupUnary : UnaryHistory group :=
    unary_transport unary_empty (hsame_symm package.left)
  have topologyUnary : UnaryHistory topology :=
    unary_transport unary_empty (hsame_symm package.right.left)
  have productUnary : UnaryHistory product :=
    unary_cont_closed groupUnary topologyUnary productCont
  have rows := TopGroupRootThresholdPackage_shared_source_rows package
  have sourceLedgerUnary : UnaryHistory sourceLedger :=
    unary_cont_closed rows.right.right.right.left unary_empty sourceLedgerCont
  exact
    And.intro package.left
      (And.intro package.right.left
        (And.intro productUnary
          (And.intro sourceLedgerUnary
            (And.intro productCont
              (And.intro (cont_right_unit_result sourceLedgerCont)
                package.right.right.right.right.right.right)))))

end BEDC.Derived.TopGroupUp
