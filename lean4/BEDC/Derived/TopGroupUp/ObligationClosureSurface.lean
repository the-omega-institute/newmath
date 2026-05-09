import BEDC.Derived.TopGroupUp
import BEDC.Derived.TopGroupUp.RootPublicObligationInventory
import BEDC.Derived.TopGroupUp.RootLedgerSemanticExactness

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem TopGroupObligation_public_consumer_surface_certificate
    {group topology product inverse neighborhood ledger provenance productLedger inverseLedger
      consumerLedger sourceFiber classifierLedger : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
    Cont product neighborhood productLedger ->
    Cont inverse neighborhood inverseLedger ->
    Cont productLedger inverseLedger consumerLedger ->
    Cont (append group topology) ledger sourceFiber ->
    Cont provenance ledger classifierLedger ->
      GroupSingletonCarrier group ∧ TopologySingletonCarrier topology ∧
        Cont group topology product ∧ Cont product inverse ledger ∧
          Cont ledger BHist.Empty provenance ∧ UnaryHistory consumerLedger ∧
            UnaryHistory sourceFiber ∧ UnaryHistory classifierLedger ∧
              hsame consumerLedger (append productLedger inverseLedger) ∧
                hsame sourceFiber (append (append group topology) ledger) ∧
                  hsame classifierLedger (append provenance ledger) ∧
                    SemanticNameCert (fun row : BHist => hsame row provenance)
                      (fun row : BHist => hsame row provenance)
                      (fun row : BHist => hsame row provenance) hsame := by
  intro package productRow inverseRow consumerRow sourceFiberRow classifierRow
  have inventory :=
    TopGroupRootThresholdPackage_root_public_obligation_inventory package productRow inverseRow
      consumerRow sourceFiberRow
  have sourceRows := TopGroupRootThresholdPackage_shared_source_rows package
  have classifierUnary : UnaryHistory classifierLedger :=
    unary_cont_closed sourceRows.right.right.right.right sourceRows.right.right.right.left
      classifierRow
  have certificate :=
    (TopGroupRootThresholdPackage_export_boundary_certificate package).left
  exact
    ⟨inventory.left,
      inventory.right.left,
      inventory.right.right.left,
      inventory.right.right.right.left,
      sourceRows.right.right.left,
      inventory.right.right.right.right.right.right.left,
      inventory.right.right.right.right.right.right.right.left,
      classifierUnary,
      inventory.right.right.right.right.right.right.right.right.left,
      inventory.right.right.right.right.right.right.right.right.right.left,
      classifierRow,
      certificate⟩

end BEDC.Derived.TopGroupUp
