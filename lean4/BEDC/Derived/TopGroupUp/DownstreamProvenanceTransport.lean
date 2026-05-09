import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem TopGroupRootDownstreamPackage_provenance_transport
    {group topology product inverse neighborhood ledger provenance ledger' provenance'
      productLedger inverseLedger : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      hsame ledger' ledger ->
        hsame provenance' provenance ->
          Cont product neighborhood productLedger ->
            Cont inverse neighborhood inverseLedger ->
              TopGroupRootThresholdPackage group topology product inverse neighborhood ledger'
                  provenance' ∧
                UnaryHistory productLedger ∧ UnaryHistory inverseLedger ∧
                  hsame provenance' ledger' := by
  intro package sameLedger sameProvenance productLedgerCont inverseLedgerCont
  have transported :=
    TopGroupRootThreshold_classifier_ledger_transport_packet package sameLedger sameProvenance
  have consumers :=
    TopGroupRootThresholdPackage_consumer_exhaustion package productLedgerCont inverseLedgerCont
  exact And.intro transported.right.right
    (And.intro consumers.right.right.left
      (And.intro consumers.right.right.right.left transported.right.left))

end BEDC.Derived.TopGroupUp
