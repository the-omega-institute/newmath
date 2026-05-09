import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.GroupUp
open BEDC.Derived.TopologyUp

def TopGroupSourceCoupledContinuityPacket
    (group topology product inverse neighborhood productLedger inverseLedger provenance :
      BHist) : Prop :=
  TopGroupRootThresholdPackage group topology product inverse neighborhood (append product inverse)
      provenance ∧
    Cont product neighborhood productLedger ∧ Cont inverse neighborhood inverseLedger ∧
      hsame provenance (append product inverse)

theorem TopGroupSourceCoupledContinuityPacket_ledger_closure
    {group topology product inverse neighborhood productLedger inverseLedger provenance :
      BHist} :
    TopGroupSourceCoupledContinuityPacket group topology product inverse neighborhood
        productLedger inverseLedger provenance ->
      GroupSingletonCarrier group ∧ TopologySingletonCarrier topology ∧ UnaryHistory product ∧
        UnaryHistory inverse ∧ UnaryHistory productLedger ∧ UnaryHistory inverseLedger ∧
          Cont product neighborhood productLedger ∧ Cont inverse neighborhood inverseLedger ∧
            hsame provenance (append product inverse) := by
  intro packet
  have package :=
    packet.left
  have boundary :=
    TopGroupRootThresholdPackage_source_coupled_continuity_boundary package
  have productLedgerUnary : UnaryHistory productLedger :=
    unary_cont_closed boundary.right.right.left boundary.right.right.right.right.left
      packet.right.left
  have inverseLedgerUnary : UnaryHistory inverseLedger :=
    unary_cont_closed boundary.right.right.right.left boundary.right.right.right.right.left
      packet.right.right.left
  exact And.intro package.left
    (And.intro package.right.left
      (And.intro boundary.right.right.left
        (And.intro boundary.right.right.right.left
          (And.intro productLedgerUnary
            (And.intro inverseLedgerUnary
              (And.intro packet.right.left
                (And.intro packet.right.right.left packet.right.right.right)))))))

theorem TopGroupRootThresholdPackage_source_coupled_carrier_scope
    {group topology product inverse neighborhood ledger provenance carrierLedger : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      Cont group neighborhood carrierLedger ->
        GroupSingletonCarrier group ∧ TopologySingletonCarrier topology ∧ UnaryHistory group ∧
          UnaryHistory topology ∧ UnaryHistory neighborhood ∧ UnaryHistory product ∧
            UnaryHistory inverse ∧ UnaryHistory ledger ∧ UnaryHistory carrierLedger ∧
              Cont group topology product ∧ Cont product inverse ledger ∧
                hsame carrierLedger (append group neighborhood) ∧ hsame provenance ledger := by
  intro package carrierCont
  have scope := TopGroupRootThreshold_carrier_scope package
  have boundary := TopGroupRootThresholdPackage_source_coupled_continuity_boundary package
  have rows := TopGroupRootThresholdPackage_shared_source_rows package
  have carrierLedgerUnary : UnaryHistory carrierLedger :=
    unary_cont_closed scope.right.right.left scope.right.right.right.right.left carrierCont
  exact
    ⟨scope.left, scope.right.left, scope.right.right.left, scope.right.right.right.left,
      scope.right.right.right.right.left, boundary.right.right.left,
      boundary.right.right.right.left, boundary.right.right.right.right.right.left,
      carrierLedgerUnary, rows.left, rows.right.left, carrierCont,
      scope.right.right.right.right.right.right⟩

end BEDC.Derived.TopGroupUp
