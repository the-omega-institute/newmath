import BEDC.Derived.GraphUp

namespace BEDC.Derived.TreeUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.GraphUp

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

end BEDC.Derived.TreeUp
