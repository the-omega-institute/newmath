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

theorem TreeBHistObligationCarrier_classifier_transport
    {root source target edge connected acyclic repr package root' source' target' edge'
      connected' acyclic' repr' package' : BHist} :
    TreeBHistObligationCarrier root source target edge connected acyclic repr package ->
      hsame root root' -> hsame source source' -> hsame target target' -> hsame edge edge' ->
        hsame connected connected' -> hsame acyclic acyclic' -> hsame repr repr' ->
          hsame package package' ->
            TreeBHistObligationCarrier root' source' target' edge' connected' acyclic' repr'
                package' ∧
              GraphContEdge source' target' edge' ∧ Cont root' connected' source' ∧
                Cont edge' repr' target' ∧ hsame package' (append source' target') := by
  intro carrier sameRoot sameSource sameTarget sameEdge sameConnected sameAcyclic sameRepr
    samePackage
  have edgeTransport :
      GraphContEdge source' target' edge' ∧ Cont source' target' edge' ∧
        (hsame source source' ∧ hsame target target' ∧ hsame edge edge') :=
    GraphContEdge_classifier_transport carrier.left sameSource sameTarget sameEdge
  have rootUnary : UnaryHistory root' :=
    unary_transport carrier.right.left sameRoot
  have connectedRoute : Cont root' connected' source' :=
    cont_hsame_transport sameRoot sameConnected sameSource carrier.right.right.left
  have acyclicEmpty : hsame acyclic' BHist.Empty :=
    hsame_trans (hsame_symm sameAcyclic) carrier.right.right.right.left
  have reprRoute : Cont edge' repr' target' :=
    cont_hsame_transport sameEdge sameRepr sameTarget carrier.right.right.right.right.left
  have packageSame : hsame package' (append source' target') := by
    cases samePackage
    cases sameSource
    cases sameTarget
    exact carrier.right.right.right.right.right
  have transportedCarrier :
      TreeBHistObligationCarrier root' source' target' edge' connected' acyclic' repr'
        package' :=
    And.intro edgeTransport.left
      (And.intro rootUnary
        (And.intro connectedRoute
          (And.intro acyclicEmpty
            (And.intro reprRoute packageSame))))
  exact And.intro transportedCarrier
    (And.intro edgeTransport.left
      (And.intro connectedRoute
        (And.intro reprRoute packageSame)))

end BEDC.Derived.TreeUp
