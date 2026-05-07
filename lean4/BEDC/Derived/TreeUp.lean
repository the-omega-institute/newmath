import BEDC.Derived.GraphUp

namespace BEDC.Derived.TreeUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.GraphUp

def TreeBHistObligationCarrier
    (root source target edge connected acyclic repr package : BHist) : Prop :=
  GraphContEdge source target edge ∧ UnaryHistory root ∧ Cont root connected source ∧
    hsame acyclic BHist.Empty ∧ Cont edge repr target ∧ hsame package (append source target)

theorem TreeBHistCarrier_obligation_rows
    {root source target edge connected acyclic repr package : BHist} :
    TreeBHistObligationCarrier root source target edge connected acyclic repr package ->
      GraphContEdge source target edge ∧ UnaryHistory root ∧ Cont root connected source ∧
        hsame acyclic BHist.Empty ∧ Cont edge repr target ∧
          hsame package (append source target) ∧
            SemanticNameCert UnaryHistory UnaryHistory UnaryHistory hsame := by
  intro carrier
  have cert : SemanticNameCert UnaryHistory UnaryHistory UnaryHistory hsame :=
    GraphCont_namecert_surface.left
  exact And.intro carrier.left
    (And.intro carrier.right.left
          (And.intro carrier.right.right.left
            (And.intro carrier.right.right.right.left
              (And.intro carrier.right.right.right.right.left
            (And.intro carrier.right.right.right.right.right cert)))))

theorem TreeGraphSource_connected_root_path_readback
    {root endpoint step pathOut rootOut : BHist} :
    UnaryHistory root -> GraphContEdge endpoint step pathOut ->
      Cont pathOut BHist.Empty rootOut -> hsame rootOut root ->
        UnaryHistory endpoint ∧ UnaryHistory step ∧ Cont endpoint step pathOut ∧
          hsame pathOut root := by
  intro _rootUnary edge rootPath sameRoot
  have sameRootOutPath : hsame rootOut pathOut :=
    Iff.mp cont_right_unit_iff rootPath
  have samePathRoot : hsame pathOut root :=
    hsame_trans (hsame_symm sameRootOutPath) sameRoot
  exact And.intro edge.left
    (And.intro edge.right.left
      (And.intro edge.right.right samePathRoot))

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

theorem TreeBHistCarrier_classifier_transport_surface
    {graph edge connected acyclic root endpoint graph' edge' connected' acyclic' root'
      endpoint' : BHist} :
    TreeBHistCarrier graph edge connected acyclic root endpoint ->
      hsame graph graph' -> hsame edge edge' -> hsame connected connected' ->
        hsame acyclic acyclic' -> hsame endpoint endpoint' -> hsame root root' ->
          TreeBHistCarrier graph' edge' connected' acyclic' root' endpoint' ∧
            GraphContEdge graph' edge' connected' ∧
              TreeRootBranch endpoint' root' connected' := by
  intro carrier sameGraph sameEdge sameConnected sameAcyclic sameEndpoint sameRoot
  have transportedGraph :
      GraphContEdge graph' edge' connected' :=
    (GraphContEdge_classifier_transport carrier.left sameGraph sameEdge sameConnected).left
  have transportedAcyclic : UnaryHistory acyclic' :=
    unary_transport carrier.right.left sameAcyclic
  have transportedBranch :
      TreeRootBranch endpoint' root' connected' :=
    (TreeBHistCarrier_root_branch_transport carrier sameEndpoint sameRoot sameConnected).left
  exact And.intro
    (And.intro transportedGraph (And.intro transportedAcyclic transportedBranch))
    (And.intro transportedGraph transportedBranch)

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
