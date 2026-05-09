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

theorem TopGroupRootThresholdPackage_continuity_ledger_scope
    {group topology product inverse neighborhood ledger provenance : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      Cont product inverse ledger ∧ UnaryHistory ledger ∧ UnaryHistory provenance ∧
        hsame provenance ledger := by
  intro package
  have rows := TopGroupRootThreshold_carrier_scope package
  have productUnary : UnaryHistory product :=
    unary_transport (unary_append_closed rows.right.right.left rows.right.right.right.left)
      (hsame_symm package.right.right.right.left)
  have inverseUnary : UnaryHistory inverse :=
    unary_transport unary_empty (hsame_symm package.right.right.right.right.left)
  have ledgerCont : Cont product inverse ledger :=
    package.right.right.right.right.right.left
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed productUnary inverseUnary ledgerCont
  have provenanceUnary : UnaryHistory provenance :=
    unary_transport ledgerUnary (hsame_symm rows.right.right.right.right.right.right)
  exact And.intro ledgerCont
    (And.intro ledgerUnary
      (And.intro provenanceUnary rows.right.right.right.right.right.right))

end BEDC.Derived.TopGroupUp
