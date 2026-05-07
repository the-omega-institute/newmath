import BEDC.Derived.GraphUp

namespace BEDC.Derived.TreeUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.GraphUp

theorem TreeVisibleDerivationSpine_extension_transport
    {root node edge spine extended transported : BHist} :
    GraphContEdge root node edge -> UnaryHistory spine -> Cont edge spine extended ->
      hsame extended transported ->
        exists edge' : BHist,
          GraphContEdge root node edge' ∧ Cont edge' spine transported ∧
            hsame edge edge' ∧ UnaryHistory transported := by
  intro edgeRow spineUnary extension sameEndpoint
  have edgeUnary : UnaryHistory edge :=
    unary_cont_closed edgeRow.left edgeRow.right.left edgeRow.right.right
  have transportedCont : Cont edge spine transported :=
    cont_result_hsame_transport extension sameEndpoint
  have transportedUnary : UnaryHistory transported :=
    unary_cont_closed edgeUnary spineUnary transportedCont
  exact Exists.intro edge
    (And.intro edgeRow
      (And.intro transportedCont (And.intro (hsame_refl edge) transportedUnary)))

theorem TreeVisibleSpine_extension_ledger {source mid target tail path extended : BHist} :
    GraphContEdge source path mid -> UnaryHistory tail -> Cont mid tail target ->
      Cont path tail extended ->
        GraphContEdge source extended target ∧ GraphContEdge mid tail target ∧
          hsame (append source extended) target := by
  intro edge tailUnary targetRow extendedRow
  have midUnary : UnaryHistory mid :=
    unary_cont_closed edge.left edge.right.left edge.right.right
  have extendedUnary : UnaryHistory extended :=
    unary_cont_closed edge.right.left tailUnary extendedRow
  have sourceExtendedRow : Cont source extended target := by
    cases edge.right.right
    cases targetRow
    cases extendedRow
    exact append_assoc source path tail
  have sameLedger : hsame (append source extended) target := by
    cases edge.right.right
    cases targetRow
    cases extendedRow
    exact (append_assoc source path tail).symm
  exact And.intro
    (And.intro edge.left (And.intro extendedUnary sourceExtendedRow))
    (And.intro
      (And.intro midUnary (And.intro tailUnary targetRow))
      sameLedger)

theorem TreeGraphContEdge_visible_spine_extension_transport
    {root spine endpoint extension out out' : BHist} :
    GraphContEdge root spine endpoint -> UnaryHistory extension -> Cont endpoint extension out ->
      hsame out out' -> GraphContEdge endpoint extension out' ∧ UnaryHistory out' ∧ hsame out out' := by
  intro edge extensionUnary extensionRoute sameOut
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed edge.left edge.right.left edge.right.right
  have outUnary : UnaryHistory out :=
    unary_cont_closed endpointUnary extensionUnary extensionRoute
  have outUnary' : UnaryHistory out' :=
    unary_transport outUnary sameOut
  have extensionRoute' : Cont endpoint extension out' :=
    cont_result_hsame_transport extensionRoute sameOut
  exact And.intro
    (And.intro endpointUnary (And.intro extensionUnary extensionRoute'))
    (And.intro outUnary' sameOut)

theorem TreeGraphContEdge_closed_walk_unit_collapse {start tail closed : BHist} :
    GraphContEdge start tail closed -> hsame closed start ->
      hsame tail BHist.Empty ∧ GraphContEdge start BHist.Empty start := by
  intro edge sameClosed
  have unitLoop : Cont start tail start :=
    cont_result_hsame_transport edge.right.right sameClosed
  have tailEmpty : hsame tail BHist.Empty :=
    cont_right_unit_unique unitLoop
  exact And.intro tailEmpty
    (And.intro edge.left (And.intro unary_empty (cont_right_unit start)))


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

theorem TreeBHistObligationCarrier_acyclic_empty_transport
    {root source target edge connected acyclic repr package acyclic' : BHist} :
    TreeBHistObligationCarrier root source target edge connected acyclic repr package ->
      hsame acyclic acyclic' ->
        hsame acyclic' BHist.Empty ∧
          TreeBHistObligationCarrier root source target edge connected acyclic' repr package := by
  intro carrier sameAcyclic
  have acyclicEmpty : hsame acyclic' BHist.Empty :=
    hsame_trans (hsame_symm sameAcyclic) carrier.right.right.right.left
  exact And.intro acyclicEmpty
    (And.intro carrier.left
      (And.intro carrier.right.left
        (And.intro carrier.right.right.left
          (And.intro acyclicEmpty
            (And.intro carrier.right.right.right.right.left
              carrier.right.right.right.right.right)))))

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

theorem TreeBHistCarrier_stability_ledger_transport
    {graph edge connected acyclic root endpoint endpoint' root' connected' acyclic' : BHist} :
    TreeBHistCarrier graph edge connected acyclic root endpoint ->
      hsame endpoint endpoint' -> hsame root root' -> hsame connected connected' ->
        hsame acyclic acyclic' ->
          TreeBHistCarrier graph edge connected' acyclic' root' endpoint' ∧
            GraphContEdge endpoint' root' connected' ∧ UnaryHistory acyclic' ∧
              Cont endpoint' root' connected' := by
  intro carrier sameEndpoint sameRoot sameConnected sameAcyclic
  have graphSource : GraphContEdge graph edge connected' :=
    (GraphContEdge_classifier_transport carrier.left (hsame_refl graph) (hsame_refl edge)
      sameConnected).left
  have branch :
      TreeRootBranch endpoint' root' connected' ∧ UnaryHistory root' ∧
        Cont endpoint' root' connected' :=
    TreeBHistCarrier_root_branch_transport carrier sameEndpoint sameRoot sameConnected
  have acyclicUnary : UnaryHistory acyclic' :=
    unary_transport carrier.right.left sameAcyclic
  exact And.intro
    (And.intro graphSource (And.intro acyclicUnary branch.left))
    (And.intro branch.left.left
      (And.intro acyclicUnary branch.right.right))

theorem TreeBHistCarrier_classifier_transport
    {graph edge connected acyclic root endpoint graphNext edgeNext connectedNext acyclicNext
      rootNext endpointNext : BHist} :
    TreeBHistCarrier graph edge connected acyclic root endpoint ->
      hsame graph graphNext -> hsame edge edgeNext -> hsame connected connectedNext ->
        hsame acyclic acyclicNext -> hsame root rootNext -> hsame endpoint endpointNext ->
          TreeBHistCarrier graphNext edgeNext connectedNext acyclicNext rootNext endpointNext ∧
            GraphContEdge graphNext edgeNext connectedNext ∧ UnaryHistory acyclicNext ∧
              Cont endpointNext rootNext connectedNext := by
  intro carrier sameGraph sameEdge sameConnected sameAcyclic sameRoot sameEndpoint
  have graphRow :
      GraphContEdge graphNext edgeNext connectedNext ∧ Cont graphNext edgeNext connectedNext ∧
        (hsame graph graphNext ∧ hsame edge edgeNext ∧ hsame connected connectedNext) :=
    GraphContEdge_classifier_transport carrier.left sameGraph sameEdge sameConnected
  have acyclicUnary : UnaryHistory acyclicNext :=
    unary_transport carrier.right.left sameAcyclic
  have rootBranch :
      TreeRootBranch endpointNext rootNext connectedNext ∧ UnaryHistory rootNext ∧
        Cont endpointNext rootNext connectedNext :=
    TreeBHistCarrier_root_branch_transport carrier sameEndpoint sameRoot sameConnected
  exact And.intro
    (And.intro graphRow.left (And.intro acyclicUnary rootBranch.left))
    (And.intro graphRow.left (And.intro acyclicUnary rootBranch.right.right))

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

theorem TreeBHistCarrier_closed_walk_tail_empty
    {graph edge connected acyclic root endpoint tail closed : BHist} :
    TreeBHistCarrier graph edge connected acyclic root endpoint ->
      Cont endpoint tail closed -> hsame closed endpoint ->
        hsame tail BHist.Empty ∧ UnaryHistory endpoint ∧
          TreeRootBranch endpoint root connected := by
  intro carrier closedWalk sameClosed
  have branch : TreeRootBranch endpoint root connected := carrier.right.right
  have endpointUnary : UnaryHistory endpoint := branch.left.left
  have closedEndpoint : Cont endpoint tail endpoint :=
    cont_result_hsame_transport closedWalk sameClosed
  have tailEmpty : hsame tail BHist.Empty :=
    cont_right_unit_unique closedEndpoint
  exact And.intro tailEmpty (And.intro endpointUnary branch)

theorem TreeRootWitness_spine_extension_exactness
    {graph edge connected acyclic root endpoint spine extendedRoot extendedConnected : BHist} :
    TreeBHistCarrier graph edge connected acyclic root endpoint -> UnaryHistory spine ->
      Cont root spine extendedRoot -> Cont connected spine extendedConnected ->
        TreeRootBranch endpoint extendedRoot extendedConnected ∧ UnaryHistory extendedRoot ∧
          Cont endpoint extendedRoot extendedConnected := by
  intro carrier spineUnary rootSpine connectedSpine
  have branch : TreeRootBranch endpoint root connected := carrier.right.right
  have endpointUnary : UnaryHistory endpoint := branch.left.left
  have extendedRootUnary : UnaryHistory extendedRoot :=
    unary_cont_closed branch.right.left spineUnary rootSpine
  cases cont_assoc_exists branch.right.right rootSpine with
  | intro assocResult assocRows =>
      have sameAssocExtended : hsame assocResult extendedConnected :=
        cont_deterministic assocRows.left connectedSpine
      have endpointExtendedConnected : Cont endpoint extendedRoot extendedConnected :=
        cont_result_hsame_transport assocRows.right sameAssocExtended
      exact And.intro
        (And.intro
          (And.intro endpointUnary (And.intro extendedRootUnary endpointExtendedConnected))
          (And.intro extendedRootUnary endpointExtendedConnected))
        (And.intro extendedRootUnary endpointExtendedConnected)

theorem TreeSyntacticRepresentation_carrier_readback
    {graph edge connected acyclic root endpoint spine extendedRoot extendedConnected : BHist} :
    TreeBHistCarrier graph edge connected acyclic root endpoint -> UnaryHistory spine ->
      Cont root spine extendedRoot -> Cont connected spine extendedConnected ->
        TreeRootBranch endpoint root connected ∧ UnaryHistory endpoint ∧
          UnaryHistory extendedRoot ∧ UnaryHistory extendedConnected ∧
            Cont endpoint root connected ∧ Cont root spine extendedRoot ∧
              Cont connected spine extendedConnected := by
  intro carrier spineUnary rootSpine connectedSpine
  have branch : TreeRootBranch endpoint root connected := carrier.right.right
  have endpointUnary : UnaryHistory endpoint := branch.left.left
  have connectedUnary : UnaryHistory connected :=
    unary_cont_closed endpointUnary branch.right.left branch.right.right
  have extendedRootUnary : UnaryHistory extendedRoot :=
    unary_cont_closed branch.right.left spineUnary rootSpine
  have extendedConnectedUnary : UnaryHistory extendedConnected :=
    unary_cont_closed connectedUnary spineUnary connectedSpine
  exact And.intro branch
    (And.intro endpointUnary
      (And.intro extendedRootUnary
        (And.intro extendedConnectedUnary
          (And.intro branch.right.right
            (And.intro rootSpine connectedSpine)))))

theorem TreeBHistCarrier_closed_path_unit_loop
    {graph edge connected acyclic root endpoint loop closed : BHist} :
    TreeBHistCarrier graph edge connected acyclic root endpoint ->
      GraphContEdge endpoint loop closed -> hsame closed endpoint ->
        GraphContEdge endpoint BHist.Empty endpoint ∧ hsame loop BHist.Empty := by
  intro carrier closedPath sameClosed
  have endpointUnary : UnaryHistory endpoint := carrier.right.right.left.left
  have unitLoop : GraphContEdge endpoint BHist.Empty endpoint :=
    (GraphContEdge_unit_loop (h := endpoint) (gL := endpoint) (gR := endpoint)
      endpointUnary).right.left
  have closedEndpoint : Cont endpoint loop endpoint :=
    cont_result_hsame_transport closedPath.right.right sameClosed
  have loopEmpty : hsame loop BHist.Empty :=
    cont_right_unit_unique closedEndpoint
  exact And.intro unitLoop loopEmpty

theorem TreeBHistCarrier_syntactic_representation
    {graph edge connected acyclic root endpoint «syntax» syntaxTarget : BHist} :
    TreeBHistCarrier graph edge connected acyclic root endpoint ->
      UnaryHistory «syntax» -> Cont endpoint «syntax» syntaxTarget ->
        TreeRootBranch endpoint root connected ∧ GraphContEdge endpoint «syntax» syntaxTarget ∧
          UnaryHistory syntaxTarget := by
  intro carrier syntaxUnary syntaxRow
  have branch : TreeRootBranch endpoint root connected := carrier.right.right
  have endpointUnary : UnaryHistory endpoint := branch.left.left
  have targetUnary : UnaryHistory syntaxTarget :=
    unary_cont_closed endpointUnary syntaxUnary syntaxRow
  exact And.intro branch
    (And.intro
      (And.intro endpointUnary (And.intro syntaxUnary syntaxRow))
      targetUnary)

theorem TreeBHistObligationCarrier_acyclic_unit_loop_exactness
    {root source target edge connected acyclic repr package loop : BHist} :
    TreeBHistObligationCarrier root source target edge connected acyclic repr package ->
      GraphContEdge target BHist.Empty loop ->
        GraphContEdge target BHist.Empty target ∧ hsame loop target ∧
          hsame acyclic BHist.Empty ∧ Cont edge repr target := by
  intro carrier loopEdge
  have loopExact :
      GraphContEdge target BHist.Empty target ∧ hsame loop target :=
    GraphContEdge_empty_tail_identity carrier.left.right.left loopEdge
  exact And.intro loopExact.left
    (And.intro loopExact.right
      (And.intro carrier.right.right.right.left carrier.right.right.right.right.left))

theorem TreePublicDerivationSyntaxBridge_visible_spine_package
    {graph edge connected acyclic root endpoint spine extendedRoot extendedConnected syntaxTarget :
      BHist} :
    TreeBHistCarrier graph edge connected acyclic root endpoint -> UnaryHistory spine ->
      Cont root spine extendedRoot -> Cont connected spine extendedConnected ->
        hsame extendedConnected syntaxTarget ->
          TreeRootBranch endpoint extendedRoot extendedConnected ∧
            GraphContEdge endpoint extendedRoot syntaxTarget ∧ UnaryHistory syntaxTarget ∧
              Cont endpoint extendedRoot syntaxTarget := by
  intro carrier spineUnary rootSpine connectedSpine sameSyntax
  have rootExtension :
      TreeRootBranch endpoint extendedRoot extendedConnected ∧ UnaryHistory extendedRoot ∧
        Cont endpoint extendedRoot extendedConnected :=
    TreeRootWitness_spine_extension_exactness carrier spineUnary rootSpine connectedSpine
  have syntaxUnary : UnaryHistory syntaxTarget :=
    unary_transport
      (unary_cont_closed rootExtension.left.left.left rootExtension.right.left
        rootExtension.right.right)
      sameSyntax
  have syntaxCont : Cont endpoint extendedRoot syntaxTarget :=
    cont_result_hsame_transport rootExtension.right.right sameSyntax
  have syntaxEdge : GraphContEdge endpoint extendedRoot syntaxTarget :=
    (GraphContEdge_classifier_transport rootExtension.left.left (hsame_refl endpoint)
      (hsame_refl extendedRoot) sameSyntax).left
  exact And.intro rootExtension.left
    (And.intro syntaxEdge (And.intro syntaxUnary syntaxCont))

end BEDC.Derived.TreeUp
