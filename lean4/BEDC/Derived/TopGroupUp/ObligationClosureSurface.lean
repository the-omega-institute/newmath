import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.GroupUp
open BEDC.Derived.TopologyUp

theorem TopGroupRootThresholdPackage_obligation_carrier_classifier_surface
    {group topology product inverse neighborhood ledger provenance : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      GroupSingletonCarrier group ∧ TopologySingletonCarrier topology ∧ UnaryHistory group ∧
        UnaryHistory topology ∧ UnaryHistory neighborhood ∧ Cont group topology product ∧
          Cont product inverse ledger ∧ Cont ledger BHist.Empty provenance ∧
            hsame provenance ledger := by
  intro package
  have scope := TopGroupRootThreshold_carrier_scope package
  have rows := TopGroupRootThresholdPackage_shared_source_rows package
  exact
    ⟨scope.left, scope.right.left, scope.right.right.left, scope.right.right.right.left,
      scope.right.right.right.right.left, rows.left, rows.right.left, rows.right.right.left,
      scope.right.right.right.right.right.right⟩

end BEDC.Derived.TopGroupUp
