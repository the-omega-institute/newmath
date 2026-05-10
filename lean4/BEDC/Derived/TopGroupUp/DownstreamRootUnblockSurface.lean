import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.GroupUp
open BEDC.Derived.TopologyUp

theorem TopGroupRootThresholdPackage_downstream_root_unblock_surface
    {group topology product inverse neighborhood ledger provenance productLedger inverseLedger
      consumerLedger : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      Cont product neighborhood productLedger ->
        Cont inverse neighborhood inverseLedger ->
          Cont productLedger inverseLedger consumerLedger ->
            SemanticNameCert (fun row : BHist => hsame row provenance)
                (fun row : BHist => hsame row provenance)
                (fun row : BHist => hsame row provenance) hsame ∧
              GroupSingletonCarrier group ∧ TopologySingletonCarrier topology ∧
                UnaryHistory consumerLedger ∧
                  hsame consumerLedger
                    (append (append product neighborhood) (append inverse neighborhood)) ∧
                    Cont product inverse ledger ∧ hsame provenance ledger := by
  intro package productCont inverseCont consumerCont
  have cert := (TopGroupRootThresholdPackage_export_boundary_certificate package).left
  have rows :=
    TopGroupRootThresholdPackage_operation_ledger_obligation package productCont inverseCont
      consumerCont
  exact And.intro cert
    (And.intro package.left
      (And.intro package.right.left
        (And.intro rows.right.right.left
          (And.intro rows.right.right.right.left
            (And.intro package.right.right.right.right.right.left
              package.right.right.right.right.right.right)))))

def TopGroupRootSharedSourcePacket
    (group topology product inverse neighborhood ledger provenance : BHist) : Prop :=
  TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ∧
    Cont group topology product ∧ Cont product inverse ledger ∧
      Cont ledger BHist.Empty provenance

theorem TopGroupRootSharedSourcePacket_export_rows
    {group topology product inverse neighborhood ledger provenance : BHist} :
    TopGroupRootSharedSourcePacket group topology product inverse neighborhood ledger provenance ->
      GroupSingletonCarrier group ∧ TopologySingletonCarrier topology ∧ Cont group topology product ∧
        Cont product inverse ledger ∧ Cont ledger BHist.Empty provenance ∧
          UnaryHistory provenance := by
  intro packet
  have package :
      TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance :=
    packet.left
  have rows := TopGroupRootThresholdPackage_shared_source_rows package
  exact And.intro package.left
    (And.intro package.right.left
      (And.intro packet.right.left
        (And.intro packet.right.right.left
          (And.intro packet.right.right.right rows.right.right.right.right))))

theorem TopGroupRootSharedSourcePacket_public_inventory_exhaustion
    {group topology product inverse neighborhood ledger provenance productLedger inverseLedger
      consumerLedger carrierLedger classifierLedger : BHist} :
    TopGroupRootSharedSourcePacket group topology product inverse neighborhood ledger provenance ->
      Cont product neighborhood productLedger ->
        Cont inverse neighborhood inverseLedger ->
          Cont productLedger inverseLedger consumerLedger ->
            Cont group neighborhood carrierLedger ->
              Cont provenance ledger classifierLedger ->
                GroupSingletonCarrier group ∧ TopologySingletonCarrier topology ∧
                  Cont group topology product ∧ Cont product inverse ledger ∧
                    Cont ledger BHist.Empty provenance ∧ UnaryHistory provenance ∧
                      UnaryHistory productLedger ∧ UnaryHistory inverseLedger ∧
                        UnaryHistory consumerLedger ∧ UnaryHistory carrierLedger ∧
                          UnaryHistory classifierLedger ∧
                            hsame consumerLedger (append productLedger inverseLedger) ∧
                              hsame provenance ledger ∧
                                SemanticNameCert (fun row : BHist => hsame row provenance)
                                  (fun row : BHist => hsame row provenance)
                                  (fun row : BHist => hsame row provenance) hsame := by
  intro packet productRow inverseRow consumerRow carrierRow classifierRow
  have package :
      TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance :=
    packet.left
  have rows := TopGroupRootSharedSourcePacket_export_rows packet
  have sharedRows := TopGroupRootThresholdPackage_shared_source_rows package
  have operationRows :=
    TopGroupRootThresholdPackage_operation_ledger_obligation package productRow inverseRow
      consumerRow
  have groupUnary : UnaryHistory group :=
    unary_transport unary_empty (hsame_symm rows.left)
  have carrierLedgerUnary : UnaryHistory carrierLedger :=
    unary_cont_closed groupUnary package.right.right.left carrierRow
  have classifierLedgerUnary : UnaryHistory classifierLedger :=
    unary_cont_closed rows.right.right.right.right.right sharedRows.right.right.right.left
      classifierRow
  have cert :=
    (TopGroupRootThresholdPackage_export_boundary_certificate package).left
  exact
    ⟨rows.left, rows.right.left, rows.right.right.left, rows.right.right.right.left,
      rows.right.right.right.right.left, rows.right.right.right.right.right,
      operationRows.left, operationRows.right.left, operationRows.right.right.left,
      carrierLedgerUnary, classifierLedgerUnary, consumerRow,
      operationRows.right.right.right.right.right, cert⟩

end BEDC.Derived.TopGroupUp
