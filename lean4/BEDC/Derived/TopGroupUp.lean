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

theorem TopGroupRootThresholdPackage_source_coupled_continuity_boundary
    {group topology product inverse neighborhood ledger provenance : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      GroupSingletonCarrier group ∧ TopologySingletonCarrier topology ∧ UnaryHistory product ∧
        UnaryHistory inverse ∧ UnaryHistory neighborhood ∧ UnaryHistory ledger ∧
          hsame ledger (append product inverse) ∧ hsame provenance ledger := by
  intro package
  have scope := TopGroupRootThreshold_carrier_scope package
  have productUnaryRaw : UnaryHistory (append group topology) :=
    unary_append_closed scope.right.right.left scope.right.right.right.left
  have productUnary : UnaryHistory product :=
    unary_transport productUnaryRaw (hsame_symm package.right.right.right.left)
  have inverseUnary : UnaryHistory inverse :=
    unary_transport unary_empty (hsame_symm package.right.right.right.right.left)
  have ledgerUnaryRaw : UnaryHistory (append product inverse) :=
    unary_append_closed productUnary inverseUnary
  have ledgerUnary : UnaryHistory ledger :=
    unary_transport ledgerUnaryRaw (hsame_symm package.right.right.right.right.right.left)
  exact And.intro scope.left
    (And.intro scope.right.left
      (And.intro productUnary
        (And.intro inverseUnary
          (And.intro scope.right.right.right.right.left
            (And.intro ledgerUnary
              (And.intro scope.right.right.right.right.right.left
                scope.right.right.right.right.right.right))))))

end BEDC.Derived.TopGroupUp
