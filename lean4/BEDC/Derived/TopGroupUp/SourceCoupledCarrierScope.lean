import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.GroupUp
open BEDC.Derived.TopologyUp

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
