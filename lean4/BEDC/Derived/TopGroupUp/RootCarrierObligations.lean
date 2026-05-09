import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.GroupUp
open BEDC.Derived.TopologyUp

theorem TopGroupRootThresholdPackage_root_downstream_carrier_obligation
    {group topology product inverse neighborhood ledger provenance carrierLedger : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      Cont group neighborhood carrierLedger ->
        GroupSingletonCarrier group ∧ TopologySingletonCarrier topology ∧ UnaryHistory group ∧
          UnaryHistory topology ∧ UnaryHistory neighborhood ∧ UnaryHistory carrierLedger ∧
            hsame carrierLedger (append group neighborhood) ∧ hsame provenance ledger := by
  intro package carrierCont
  have rows := TopGroupRootThreshold_carrier_scope package
  have carrierUnary : UnaryHistory carrierLedger :=
    unary_cont_closed rows.right.right.left rows.right.right.right.right.left carrierCont
  exact And.intro rows.left
    (And.intro rows.right.left
      (And.intro rows.right.right.left
        (And.intro rows.right.right.right.left
          (And.intro rows.right.right.right.right.left
            (And.intro carrierUnary
              (And.intro carrierCont rows.right.right.right.right.right.right))))))

theorem TopGroupRootThresholdPackage_root_source_fiber_carrier_obligation
    {group topology product inverse neighborhood ledger provenance sourceFiber : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      Cont (append group topology) ledger sourceFiber ->
        GroupSingletonCarrier group ∧ TopologySingletonCarrier topology ∧
          Cont group topology product ∧ Cont product inverse ledger ∧ UnaryHistory sourceFiber ∧
            hsame sourceFiber (append (append group topology) ledger) ∧
              hsame provenance ledger := by
  intro package sourceFiberCont
  have rows := TopGroupRootThresholdPackage_shared_source_rows package
  have groupUnary : UnaryHistory group :=
    unary_transport unary_empty (hsame_symm package.left)
  have topologyUnary : UnaryHistory topology :=
    unary_transport unary_empty (hsame_symm package.right.left)
  have sourceUnary : UnaryHistory (append group topology) :=
    unary_append_closed groupUnary topologyUnary
  have sourceFiberUnary : UnaryHistory sourceFiber :=
    unary_cont_closed sourceUnary rows.right.right.right.left sourceFiberCont
  exact And.intro package.left
    (And.intro package.right.left
      (And.intro rows.left
        (And.intro rows.right.left
          (And.intro sourceFiberUnary
            (And.intro sourceFiberCont package.right.right.right.right.right.right)))))

end BEDC.Derived.TopGroupUp
