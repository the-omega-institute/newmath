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

theorem TreeBHistCarrier_visible_spine_extension_ledger
    {graph edge connected acyclic root endpoint spine extendedRoot extendedConnected k : BHist} :
    TreeBHistCarrier graph edge connected acyclic root endpoint -> UnaryHistory spine ->
      Cont root spine extendedRoot -> Cont connected spine extendedConnected ->
        hsame extendedConnected k ->
          GraphContEdge endpoint extendedRoot k ∧ UnaryHistory extendedRoot ∧
            Cont endpoint extendedRoot k ∧ hsame extendedConnected k := by
  intro carrier spineUnary rootSpine connectedSpine sameExtended
  have branch : TreeRootBranch endpoint root connected := carrier.right.right
  have endpointUnary : UnaryHistory endpoint := branch.left.left
  have extendedRootUnary : UnaryHistory extendedRoot :=
    unary_cont_closed branch.right.left spineUnary rootSpine
  cases cont_assoc_exists branch.right.right rootSpine with
  | intro assocResult assocRows =>
      have sameAssocExtended : hsame assocResult extendedConnected :=
        cont_deterministic assocRows.left connectedSpine
      have sameAssocK : hsame assocResult k :=
        hsame_trans sameAssocExtended sameExtended
      have endpointExtendedK : Cont endpoint extendedRoot k :=
        cont_result_hsame_transport assocRows.right sameAssocK
      exact And.intro
        (And.intro endpointUnary (And.intro extendedRootUnary endpointExtendedK))
        (And.intro extendedRootUnary (And.intro endpointExtendedK sameExtended))

end BEDC.Derived.TreeUp
