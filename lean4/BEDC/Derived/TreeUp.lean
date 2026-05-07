import BEDC.Derived.GraphUp

namespace BEDC.Derived.TreeUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
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

end BEDC.Derived.TreeUp
