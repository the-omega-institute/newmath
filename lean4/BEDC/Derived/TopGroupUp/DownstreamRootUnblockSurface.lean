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

end BEDC.Derived.TopGroupUp
