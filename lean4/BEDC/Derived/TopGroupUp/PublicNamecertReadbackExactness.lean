import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.GroupUp
open BEDC.Derived.TopologyUp

theorem TopGroupRootThresholdPackage_public_namecert_readback_exactness
    {group topology product inverse neighborhood ledger provenance productLedger inverseLedger :
      BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      Cont product neighborhood productLedger ->
        Cont inverse neighborhood inverseLedger ->
          SemanticNameCert (fun row : BHist => hsame row provenance)
            (fun row : BHist => hsame row provenance)
            (fun row : BHist => hsame row provenance) hsame ∧
            GroupSingletonCarrier group ∧ TopologySingletonCarrier topology ∧
              UnaryHistory productLedger ∧ UnaryHistory inverseLedger ∧
                Cont product neighborhood productLedger ∧
                  Cont inverse neighborhood inverseLedger ∧ hsame ledger (append product inverse) ∧
                    hsame provenance ledger := by
  intro package productRow inverseRow
  have certificate :=
    TopGroupRootThresholdPackage_public_certificate_boundary package
  have consumer :=
    TopGroupRootThresholdPackage_consumer_exhaustion package productRow inverseRow
  exact
    ⟨certificate.left, consumer.left, consumer.right.left, consumer.right.right.left,
      consumer.right.right.right.left, productRow, inverseRow,
      certificate.right.right.right.right.right.right.left,
      consumer.right.right.right.right.right⟩

end BEDC.Derived.TopGroupUp
