import BEDC.Derived.TreeUp

namespace BEDC.Derived.TreeUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.GraphUp

theorem TreeBHistCarrier_classifier_transport_obligation
    {graph edge connected acyclic root endpoint graphNext edgeNext connectedNext acyclicNext
      rootNext endpointNext syntaxHist syntaxTarget : BHist} :
    TreeObligationSurface graph edge connected acyclic root endpoint syntaxHist syntaxTarget ->
      hsame graph graphNext -> hsame edge edgeNext -> hsame connected connectedNext ->
        hsame acyclic acyclicNext -> hsame root rootNext -> hsame endpoint endpointNext ->
          TreeObligationSurface graphNext edgeNext connectedNext acyclicNext rootNext
              endpointNext syntaxHist syntaxTarget ∧
            GraphContEdge graphNext edgeNext connectedNext ∧
              TreeRootBranch endpointNext rootNext connectedNext ∧ UnaryHistory acyclicNext ∧
                Cont endpointNext rootNext connectedNext ∧ hsame connected connectedNext := by
  intro surface sameGraph sameEdge sameConnected sameAcyclic sameRoot sameEndpoint
  have transported :
      TreeBHistCarrier graphNext edgeNext connectedNext acyclicNext rootNext endpointNext ∧
        GraphContEdge graphNext edgeNext connectedNext ∧ UnaryHistory acyclicNext ∧
          Cont endpointNext rootNext connectedNext :=
    TreeBHistCarrier_classifier_transport surface.left sameGraph sameEdge sameConnected
      sameAcyclic sameRoot sameEndpoint
  have transportedSyntax : Cont endpointNext syntaxHist syntaxTarget :=
    cont_hsame_transport sameEndpoint (hsame_refl syntaxHist) (hsame_refl syntaxTarget)
      surface.right.right
  have transportedBranch : TreeRootBranch endpointNext rootNext connectedNext :=
    transported.left.right.right
  exact And.intro
    (And.intro transported.left (And.intro surface.right.left transportedSyntax))
    (And.intro transported.right.left
      (And.intro transportedBranch
        (And.intro transported.right.right.left
          (And.intro transported.right.right.right sameConnected))))

end BEDC.Derived.TreeUp
