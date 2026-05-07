import BEDC.Derived.GraphUp

namespace BEDC.Derived.TreeUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.GraphUp

def TreeRootBranch (endpoint root connected : BHist) : Prop :=
  GraphContEdge endpoint root connected ∧ UnaryHistory root ∧ Cont endpoint root connected

def TreeBHistCarrier (graph edge connected acyclic root endpoint : BHist) : Prop :=
  GraphContEdge graph edge connected ∧ UnaryHistory acyclic ∧
    TreeRootBranch endpoint root connected

theorem TreeBHistCarrier_root_branch_transport
    {graph edge connected acyclic root endpoint endpoint' root' connected' : BHist} :
    TreeBHistCarrier graph edge connected acyclic root endpoint ->
      hsame endpoint endpoint' -> hsame root root' -> hsame connected connected' ->
        TreeRootBranch endpoint' root' connected' ∧ UnaryHistory root' ∧
          Cont endpoint' root' connected' := by
  intro carrier sameEndpoint sameRoot sameConnected
  have branch : TreeRootBranch endpoint root connected := carrier.right.right
  have rootUnary : UnaryHistory root' :=
    unary_transport branch.right.left sameRoot
  have transportedEdge : GraphContEdge endpoint' root' connected' :=
    (GraphContEdge_classifier_transport branch.left sameEndpoint sameRoot sameConnected).left
  have transportedCont : Cont endpoint' root' connected' :=
    cont_hsame_transport sameEndpoint sameRoot sameConnected branch.right.right
  exact And.intro
    (And.intro transportedEdge (And.intro rootUnary transportedCont))
    (And.intro rootUnary transportedCont)

theorem TreeBHistCarrier_hsame_transport
    {graph edge connected acyclic root endpoint graph' edge' connected' acyclic' root'
      endpoint' : BHist} :
    TreeBHistCarrier graph edge connected acyclic root endpoint -> hsame graph graph' ->
      hsame edge edge' -> hsame connected connected' -> hsame acyclic acyclic' ->
        hsame root root' -> hsame endpoint endpoint' ->
          TreeBHistCarrier graph' edge' connected' acyclic' root' endpoint' ∧
            GraphContEdge graph' edge' connected' ∧ UnaryHistory acyclic' ∧
              TreeRootBranch endpoint' root' connected' := by
  intro carrier sameGraph sameEdge sameConnected sameAcyclic sameRoot sameEndpoint
  have graphRow : GraphContEdge graph' edge' connected' :=
    (GraphContEdge_classifier_transport carrier.left sameGraph sameEdge sameConnected).left
  have acyclicUnary : UnaryHistory acyclic' :=
    unary_transport carrier.right.left sameAcyclic
  have branch :
      TreeRootBranch endpoint' root' connected' ∧ UnaryHistory root' ∧
        Cont endpoint' root' connected' :=
    TreeBHistCarrier_root_branch_transport carrier sameEndpoint sameRoot sameConnected
  have carrier' : TreeBHistCarrier graph' edge' connected' acyclic' root' endpoint' :=
    And.intro graphRow (And.intro acyclicUnary branch.left)
  exact And.intro carrier'
    (And.intro graphRow (And.intro acyclicUnary branch.left))

theorem TreeVisibleCarrier_root_witness_obligation {root vertex edge : BHist} :
    GraphContEdge root vertex edge ->
      (hsame root BHist.Empty -> GraphContEdge BHist.Empty vertex vertex ∧ hsame edge vertex) ∧
        ((hsame root BHist.Empty -> False) -> UnaryHistory root ∧
          GraphContEdge root vertex edge) := by
  intro edgeRow
  constructor
  · intro rootEmpty
    cases rootEmpty
    have emptyEdge : GraphContEdge BHist.Empty vertex vertex :=
      And.intro unary_empty (And.intro edgeRow.right.left (cont_left_unit vertex))
    have sameEdgeVertex : hsame edge vertex :=
      cont_left_unit_result edgeRow.right.right
    exact And.intro emptyEdge sameEdgeVertex
  · intro _rootNonempty
    exact And.intro edgeRow.left edgeRow

end BEDC.Derived.TreeUp
