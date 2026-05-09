import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.GroupUp
open BEDC.Derived.TopologyUp

theorem TopGroupRootThresholdPackage_namecert_obligation_surface
    {group topology product inverse neighborhood ledger provenance : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      SemanticNameCert (fun row : BHist => hsame row provenance)
        (fun row : BHist => hsame row provenance)
        (fun row : BHist => hsame row provenance) hsame ∧
        GroupSingletonCarrier group ∧ TopologySingletonCarrier topology ∧ UnaryHistory neighborhood ∧
          Cont group topology product ∧ Cont product inverse ledger ∧
            Cont ledger BHist.Empty provenance ∧ hsame provenance ledger ∧
              exists productLedger inverseLedger : BHist,
                Cont product neighborhood productLedger ∧ Cont inverse neighborhood inverseLedger ∧
                  UnaryHistory productLedger ∧ UnaryHistory inverseLedger := by
  intro package
  have cert :=
    (TopGroupRootThresholdPackage_export_boundary_certificate package).left
  have rows :=
    TopGroupRootThresholdPackage_shared_source_rows package
  have operation :=
    TopGroupRootThresholdPackage_operation_scope package
  cases operation with
  | intro productLedger rest =>
      cases rest with
      | intro inverseLedger data =>
        exact
          ⟨cert, package.left, package.right.left, package.right.right.left, rows.left,
            rows.right.left, rows.right.right.left,
            package.right.right.right.right.right.right, productLedger, inverseLedger,
            data.left, data.right.left, data.right.right.left, data.right.right.right.left⟩

end BEDC.Derived.TopGroupUp
