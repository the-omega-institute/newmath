import BEDC.Derived.LambdaCalcUp

namespace BEDC.Derived.LambdaCalcUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.TreeUp

theorem LambdaCalcBHistTermPacketCarrier_root_constructor_scope
    {graph edge connected acyclic tag payload endpoint constructorLedger : BHist} :
    LambdaCalcBHistTermPacketCarrier graph edge connected acyclic tag payload endpoint ->
      Cont endpoint payload constructorLedger ->
        UnaryHistory tag ∧ UnaryHistory payload ∧ UnaryHistory endpoint ∧
          UnaryHistory constructorLedger ∧ hsame constructorLedger (append endpoint payload) ∧
            TreeBHistCarrier graph edge connected acyclic tag endpoint := by
  intro packet constructorRow
  have rows := TreeBHistCarrier_exactness_rows packet.left
  have constructorUnary : UnaryHistory constructorLedger :=
    unary_cont_closed packet.right.right.left packet.right.left constructorRow
  exact And.intro rows.right.right.right.right.right.right.left
    (And.intro packet.right.left
      (And.intro packet.right.right.left
        (And.intro constructorUnary
          (And.intro constructorRow packet.left))))

end BEDC.Derived.LambdaCalcUp
