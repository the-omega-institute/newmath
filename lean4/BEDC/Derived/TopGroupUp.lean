import BEDC.Derived.GroupUp
import BEDC.Derived.TopologyUp.Singleton
import BEDC.FKernel.Unary

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.GroupUp
open BEDC.Derived.TopologyUp

def TopGroupRootThresholdPackage
    (group topology product inverse neighborhood ledger provenance : BHist) : Prop :=
  GroupSingletonCarrier group ∧ TopologySingletonCarrier topology ∧ UnaryHistory neighborhood ∧
    hsame product (append group topology) ∧ hsame inverse BHist.Empty ∧
      hsame ledger (append product inverse) ∧ hsame provenance ledger

theorem TopGroupRootThreshold_carrier_scope
    {group topology product inverse neighborhood ledger provenance : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      GroupSingletonCarrier group ∧ TopologySingletonCarrier topology ∧ UnaryHistory group ∧
        UnaryHistory topology ∧ UnaryHistory neighborhood ∧ hsame ledger (append product inverse) ∧
          hsame provenance ledger := by
  intro package
  have groupUnary : UnaryHistory group :=
    unary_transport unary_empty (hsame_symm package.left)
  have topologyUnary : UnaryHistory topology :=
    unary_transport unary_empty (hsame_symm package.right.left)
  exact And.intro package.left
    (And.intro package.right.left
      (And.intro groupUnary
        (And.intro topologyUnary
          (And.intro package.right.right.left
            (And.intro package.right.right.right.right.right.left
              package.right.right.right.right.right.right)))))

theorem TopGroupRootThreshold_product_inverse_empty_scope
    {group topology product inverse neighborhood ledger provenance : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      hsame product BHist.Empty ∧ hsame inverse BHist.Empty ∧ hsame ledger BHist.Empty ∧
        hsame provenance BHist.Empty := by
  intro package
  have productEmpty : hsame product BHist.Empty :=
    hsame_trans package.right.right.right.left
      (append_eq_empty_iff.mpr (And.intro package.left package.right.left))
  have ledgerEmpty : hsame ledger BHist.Empty :=
    hsame_trans package.right.right.right.right.right.left
      (append_eq_empty_iff.mpr (And.intro productEmpty package.right.right.right.right.left))
  exact And.intro productEmpty
    (And.intro package.right.right.right.right.left
      (And.intro ledgerEmpty
        (hsame_trans package.right.right.right.right.right.right ledgerEmpty)))

theorem TopGroupRootThreshold_classifier_ledger_transport_packet
    {group topology product inverse neighborhood ledger provenance ledger' provenance' : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      hsame ledger' ledger ->
        hsame provenance' provenance ->
          hsame ledger' (append product inverse) ∧ hsame provenance' ledger' ∧
            TopGroupRootThresholdPackage group topology product inverse neighborhood ledger'
              provenance' := by
  intro package sameLedger sameProvenance
  have ledgerEndpoint : hsame ledger' (append product inverse) :=
    hsame_trans sameLedger package.right.right.right.right.right.left
  have provenanceEndpoint : hsame provenance' ledger' :=
    hsame_trans sameProvenance
      (hsame_trans package.right.right.right.right.right.right (hsame_symm sameLedger))
  exact And.intro ledgerEndpoint
    (And.intro provenanceEndpoint
      (And.intro package.left
        (And.intro package.right.left
          (And.intro package.right.right.left
            (And.intro package.right.right.right.left
              (And.intro package.right.right.right.right.left
                (And.intro ledgerEndpoint provenanceEndpoint)))))))

end BEDC.Derived.TopGroupUp
