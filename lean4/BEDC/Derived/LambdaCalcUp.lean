import BEDC.Derived.TreeUp

namespace BEDC.Derived.LambdaCalcUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.TreeUp

def LambdaCalcBHistTermCarrier
    (graph edge connected acyclic tag payload endpoint : BHist) : Prop :=
  TreeBHistCarrier graph edge connected acyclic tag endpoint ∧ UnaryHistory payload ∧
    UnaryHistory endpoint ∧ Cont tag payload endpoint

theorem LambdaCalcBHistTermCarrier_abstraction_application_closure
    {graph edge connected acyclic bodyTag bodyPayload bodyEndpoint binder absPayload absTag
      absEndpoint funTag funPayload funEndpoint argTag argPayload argEndpoint appPayload appTag
      appEndpoint : BHist} :
    LambdaCalcBHistTermCarrier graph edge connected acyclic bodyTag bodyPayload bodyEndpoint ->
      LambdaCalcBHistTermCarrier graph edge connected acyclic funTag funPayload funEndpoint ->
        LambdaCalcBHistTermCarrier graph edge connected acyclic argTag argPayload argEndpoint ->
          UnaryHistory binder ->
            Cont binder bodyEndpoint absPayload ->
              TreeBHistCarrier graph edge connected acyclic absTag absEndpoint ->
                Cont absTag absPayload absEndpoint ->
                  Cont funEndpoint argEndpoint appPayload ->
                    TreeBHistCarrier graph edge connected acyclic appTag appEndpoint ->
                      Cont appTag appPayload appEndpoint ->
                        LambdaCalcBHistTermCarrier graph edge connected acyclic absTag absPayload
                            absEndpoint ∧
                          LambdaCalcBHistTermCarrier graph edge connected acyclic appTag appPayload
                              appEndpoint ∧
                            UnaryHistory absPayload ∧ UnaryHistory appPayload := by
  intro bodyCarrier funCarrier argCarrier binderUnary absPayloadRow absTree absEndpointRow
    appPayloadRow appTree appEndpointRow
  have absPayloadUnary : UnaryHistory absPayload :=
    unary_cont_closed binderUnary bodyCarrier.right.right.left absPayloadRow
  have absEndpointUnary : UnaryHistory absEndpoint :=
    absTree.right.right.left.left
  have appPayloadUnary : UnaryHistory appPayload :=
    unary_cont_closed funCarrier.right.right.left argCarrier.right.right.left appPayloadRow
  have appEndpointUnary : UnaryHistory appEndpoint :=
    appTree.right.right.left.left
  have absCarrier :
      LambdaCalcBHistTermCarrier graph edge connected acyclic absTag absPayload absEndpoint :=
    And.intro absTree
      (And.intro absPayloadUnary
        (And.intro absEndpointUnary absEndpointRow))
  have appCarrier :
      LambdaCalcBHistTermCarrier graph edge connected acyclic appTag appPayload appEndpoint :=
    And.intro appTree
      (And.intro appPayloadUnary
        (And.intro appEndpointUnary appEndpointRow))
  exact And.intro absCarrier
    (And.intro appCarrier
      (And.intro absPayloadUnary appPayloadUnary))

end BEDC.Derived.LambdaCalcUp
