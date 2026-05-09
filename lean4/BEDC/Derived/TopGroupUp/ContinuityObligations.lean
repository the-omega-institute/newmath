import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.GroupUp
open BEDC.Derived.TopologyUp

theorem TopGroupRootThresholdPackage_inversion_continuity_carrier
    {group topology product inverse neighborhood ledger provenance inverseLedger : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      Cont inverse neighborhood inverseLedger ->
        GroupSingletonCarrier group ∧ TopologySingletonCarrier topology ∧ UnaryHistory inverse ∧
          UnaryHistory neighborhood ∧ UnaryHistory inverseLedger ∧
            Cont inverse neighborhood inverseLedger ∧
              hsame inverseLedger (append inverse neighborhood) ∧ hsame provenance ledger := by
  intro package inverseLedgerCont
  have boundary :=
    TopGroupRootThresholdPackage_source_coupled_continuity_boundary package
  have inverseLedgerUnary : UnaryHistory inverseLedger :=
    unary_cont_closed boundary.right.right.right.left boundary.right.right.right.right.left
      inverseLedgerCont
  exact
    And.intro boundary.left
      (And.intro boundary.right.left
        (And.intro boundary.right.right.right.left
          (And.intro boundary.right.right.right.right.left
            (And.intro inverseLedgerUnary
              (And.intro inverseLedgerCont
                (And.intro inverseLedgerCont boundary.right.right.right.right.right.right.right))))))

theorem TopGroupRootThresholdPackage_operation_continuity_witness_obligation
    {group topology product inverse neighborhood ledger provenance productLedger inverseLedger :
      BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      Cont product neighborhood productLedger ->
        Cont inverse neighborhood inverseLedger ->
          UnaryHistory productLedger ∧ UnaryHistory inverseLedger ∧
            hsame productLedger (append product neighborhood) ∧
              hsame inverseLedger (append inverse neighborhood) ∧ Cont product inverse ledger ∧
                hsame provenance ledger := by
  intro package productLedgerCont inverseLedgerCont
  have boundary :=
    TopGroupRootThresholdPackage_source_coupled_continuity_boundary package
  have productLedgerUnary : UnaryHistory productLedger :=
    unary_cont_closed boundary.right.right.left boundary.right.right.right.right.left
      productLedgerCont
  have inverseLedgerUnary : UnaryHistory inverseLedger :=
    unary_cont_closed boundary.right.right.right.left boundary.right.right.right.right.left
      inverseLedgerCont
  exact
    And.intro productLedgerUnary
      (And.intro inverseLedgerUnary
        (And.intro productLedgerCont
          (And.intro inverseLedgerCont
            (And.intro package.right.right.right.right.right.left
              package.right.right.right.right.right.right))))

theorem TopGroupRootThresholdPackage_product_cont_ledger_soundness
    {group topology product inverse neighborhood ledger provenance productLedger
      productContinuityLedger : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      Cont product neighborhood productLedger ->
        Cont productLedger ledger productContinuityLedger ->
          UnaryHistory productLedger ∧ UnaryHistory productContinuityLedger ∧
            hsame productLedger (append product neighborhood) ∧
              hsame productContinuityLedger (append productLedger ledger) ∧
                hsame ledger (append product inverse) ∧ hsame provenance ledger := by
  intro package productCont productContinuityCont
  have boundary :=
    TopGroupRootThresholdPackage_source_coupled_continuity_boundary package
  have productLedgerUnary : UnaryHistory productLedger :=
    unary_cont_closed boundary.right.right.left boundary.right.right.right.right.left productCont
  have productContinuityLedgerUnary : UnaryHistory productContinuityLedger :=
    unary_cont_closed productLedgerUnary boundary.right.right.right.right.right.left
      productContinuityCont
  exact And.intro productLedgerUnary
    (And.intro productContinuityLedgerUnary
      (And.intro productCont
        (And.intro productContinuityCont
          (And.intro boundary.right.right.right.right.right.right.left
            boundary.right.right.right.right.right.right.right))))

theorem TopGroupRootThresholdPackage_product_continuity_obligation
    {group topology product inverse neighborhood ledger provenance productLedger transportedProduct
      transportedNeighborhood transportedLedger : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      hsame product transportedProduct ->
        hsame neighborhood transportedNeighborhood ->
          Cont product neighborhood productLedger ->
            Cont transportedProduct transportedNeighborhood transportedLedger ->
              hsame productLedger transportedLedger ∧ UnaryHistory transportedProduct ∧
                UnaryHistory transportedNeighborhood ∧ UnaryHistory transportedLedger ∧
                  hsame ledger (append product inverse) ∧ hsame provenance ledger := by
  intro package sameProduct sameNeighborhood productCont transportedCont
  have transported :=
    TopGroupRootThresholdPackage_product_neighborhood_transport package sameProduct
      sameNeighborhood productCont transportedCont
  have boundary :=
    TopGroupRootThresholdPackage_source_coupled_continuity_boundary package
  exact And.intro transported.left
    (And.intro transported.right.left
      (And.intro transported.right.right.left
        (And.intro transported.right.right.right
          (And.intro boundary.right.right.right.right.right.right.left
            boundary.right.right.right.right.right.right.right))))

end BEDC.Derived.TopGroupUp
