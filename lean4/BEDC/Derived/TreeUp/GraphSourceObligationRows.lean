import BEDC.Derived.TreeUp

namespace BEDC.Derived.TreeUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.GraphUp

theorem TreeGraphSource_obligation_rows
    {graph edge connected acyclic root endpoint «syntax» syntaxTarget graphNext edgeNext
      connectedNext : BHist} :
    TreeObligationSurface graph edge connected acyclic root endpoint «syntax» syntaxTarget ->
      hsame graph graphNext -> hsame edge edgeNext -> hsame connected connectedNext ->
        GraphContEdge graphNext edgeNext connectedNext ∧
          TreeObligationSurface graphNext edgeNext connectedNext acyclic root endpoint «syntax»
            syntaxTarget ∧
          hsame connectedNext connected ∧ Cont endpoint «syntax» syntaxTarget := by
  intro surface sameGraph sameEdge sameConnected
  have rows := TreeObligationSurface_rows surface
  have graphRow : GraphContEdge graphNext edgeNext connectedNext :=
    (GraphContEdge_classifier_transport rows.left.left sameGraph sameEdge sameConnected).left
  have branch :
      TreeRootBranch endpoint root connectedNext ∧ UnaryHistory root ∧
        Cont endpoint root connectedNext :=
    TreeBHistCarrier_root_branch_transport rows.left (hsame_refl endpoint) (hsame_refl root)
      sameConnected
  have transportedCarrier :
      TreeBHistCarrier graphNext edgeNext connectedNext acyclic root endpoint :=
    And.intro graphRow (And.intro rows.left.right.left branch.left)
  exact And.intro graphRow
    (And.intro
      (And.intro transportedCarrier
        (And.intro rows.right.left rows.right.right.left))
      (And.intro (hsame_symm sameConnected) rows.right.right.left))

theorem TreeGraphSource_carrier_obligation {graph edge connected root endpoint : BHist} :
    GraphContEdge graph edge connected -> GraphContEdge endpoint root connected ->
      UnaryHistory root ->
        TreeBHistCarrier graph edge connected BHist.Empty root endpoint ∧ UnaryHistory graph ∧
          UnaryHistory edge ∧ UnaryHistory connected := by
  intro graphRow rootRow rootCarrier
  have rootBranch : TreeRootBranch endpoint root connected :=
    And.intro rootRow (And.intro rootCarrier rootRow.right.right)
  have carrier : TreeBHistCarrier graph edge connected BHist.Empty root endpoint :=
    And.intro graphRow (And.intro unary_empty rootBranch)
  have connectedCarrier : UnaryHistory connected :=
    unary_cont_closed graphRow.left graphRow.right.left graphRow.right.right
  exact And.intro carrier
    (And.intro graphRow.left (And.intro graphRow.right.left connectedCarrier))

theorem TreeObligationSurface_classifier_transport
    {graph edge connected acyclic root endpoint syntaxHist syntaxTarget graphNext edgeNext
      connectedNext acyclicNext rootNext endpointNext syntaxNext syntaxTargetNext : BHist} :
    TreeObligationSurface graph edge connected acyclic root endpoint syntaxHist syntaxTarget ->
      hsame graph graphNext -> hsame edge edgeNext -> hsame connected connectedNext ->
        hsame acyclic acyclicNext -> hsame root rootNext -> hsame endpoint endpointNext ->
          hsame syntaxHist syntaxNext -> hsame syntaxTarget syntaxTargetNext ->
            Cont endpointNext syntaxNext syntaxTargetNext ->
              TreeObligationSurface graphNext edgeNext connectedNext acyclicNext rootNext
                  endpointNext syntaxNext syntaxTargetNext ∧
                GraphContEdge graphNext edgeNext connectedNext ∧
                  TreeRootBranch endpointNext rootNext connectedNext ∧
                    Cont endpointNext syntaxNext syntaxTargetNext := by
  intro surface sameGraph sameEdge sameConnected sameAcyclic sameRoot sameEndpoint sameSyntax
    _sameSyntaxTarget syntaxRow
  have carrierRows :=
    TreeBHistCarrier_classifier_transport surface.left sameGraph sameEdge sameConnected
      sameAcyclic sameRoot sameEndpoint
  have syntaxUnary : UnaryHistory syntaxNext :=
    unary_transport surface.right.left sameSyntax
  have nextSurface :
      TreeObligationSurface graphNext edgeNext connectedNext acyclicNext rootNext endpointNext
        syntaxNext syntaxTargetNext :=
    And.intro carrierRows.left (And.intro syntaxUnary syntaxRow)
  exact And.intro nextSurface
    (And.intro carrierRows.right.left
      (And.intro carrierRows.left.right.right syntaxRow))

end BEDC.Derived.TreeUp
