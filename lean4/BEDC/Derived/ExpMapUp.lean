import BEDC.Derived.LieAlgebraUp
import BEDC.Derived.LieGroupUp
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Units
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.ExpMapUp

open BEDC.Derived.LieAlgebraUp
open BEDC.Derived.LieGroupUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def ExpMapGraphCarrier (tangent endpoint flow : BHist) : Prop :=
  LieAlgebraSingletonCarrier tangent ∧ LieGroupSingletonCarrier endpoint ∧
    Cont tangent BHist.Empty flow ∧ hsame flow endpoint

theorem ExpMapCarrier_source_obligations {tangent endpoint flow : BHist} :
    ExpMapGraphCarrier tangent endpoint flow ->
      LieAlgebraSingletonCarrier tangent ∧ LieGroupSingletonCarrier endpoint ∧
        hsame flow endpoint ∧ UnaryHistory tangent ∧ UnaryHistory endpoint ∧
          UnaryHistory flow := by
  intro graph
  have tangentUnary : UnaryHistory tangent :=
    unary_transport unary_empty (hsame_symm graph.left)
  have endpointUnary : UnaryHistory endpoint :=
    unary_transport unary_empty (hsame_symm graph.right.left)
  have flowTangent : hsame flow tangent :=
    cont_right_unit_result graph.right.right.left
  have flowUnary : UnaryHistory flow :=
    unary_transport tangentUnary (hsame_symm flowTangent)
  exact And.intro graph.left
    (And.intro graph.right.left
      (And.intro graph.right.right.right
        (And.intro tangentUnary (And.intro endpointUnary flowUnary))))

end BEDC.Derived.ExpMapUp
