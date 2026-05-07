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

end BEDC.Derived.TreeUp
