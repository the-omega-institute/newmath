import BEDC.Derived.LambdaCalcUp

namespace BEDC.Derived.LambdaCalcUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.TreeUp

theorem LambdaCalcBHistTermPacketCarrier_capture_avoidance_cont_closure
    {graph edge connected acyclic tag payload endpoint substTag substPayload substEndpoint varIndex
      ledger result resultTag resultEndpoint : BHist} :
    LambdaCalcBHistTermPacketCarrier graph edge connected acyclic tag payload endpoint ->
      LambdaCalcBHistTermPacketCarrier graph edge connected acyclic substTag substPayload
          substEndpoint ->
        UnaryHistory varIndex ->
          TreeBHistCarrier graph edge connected acyclic resultTag resultEndpoint ->
            Cont endpoint substEndpoint ledger ->
              Cont ledger varIndex result ->
                Cont resultTag result resultEndpoint ->
                  LambdaCalcBHistTermPacketCarrier graph edge connected acyclic resultTag result
                      resultEndpoint ∧
                    UnaryHistory ledger ∧ UnaryHistory result := by
  intro packet substPacket varUnary resultTree ledgerRow resultRow resultEndpointRow
  have scope :=
    LambdaCalcBHistTermPacketCarrier_substitution_ledger_scope packet substPacket varUnary
      ledgerRow resultRow
  have resultEndpointUnary : UnaryHistory resultEndpoint :=
    (TreeBHistCarrier_exactness_rows resultTree).right.right.right.right.right.right.right.left
  have resultPacket :
      LambdaCalcBHistTermPacketCarrier graph edge connected acyclic resultTag result
        resultEndpoint :=
    And.intro resultTree
      (And.intro scope.right.left
        (And.intro resultEndpointUnary resultEndpointRow))
  exact And.intro resultPacket (And.intro scope.left scope.right.left)

end BEDC.Derived.LambdaCalcUp
