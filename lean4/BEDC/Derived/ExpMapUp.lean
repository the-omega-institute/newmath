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

def ExpMapFlowLedger (tangent endpoint flow : BHist) : Prop :=
  LieAlgebraSingletonCarrier tangent ∧ LieGroupSingletonCarrier endpoint ∧
    Cont tangent BHist.Empty endpoint ∧ Cont endpoint BHist.Empty flow

theorem ExpMapFlowLedger_carrier_obligation_surface {tangent endpoint flow : BHist} :
    ExpMapFlowLedger tangent endpoint flow ->
      LieAlgebraSingletonCarrier tangent ∧ LieGroupSingletonCarrier endpoint ∧
        hsame endpoint tangent ∧ hsame flow endpoint ∧ UnaryHistory tangent ∧
          UnaryHistory endpoint ∧ UnaryHistory flow := by
  intro ledger
  have tangentCarrier : LieAlgebraSingletonCarrier tangent := ledger.left
  have endpointCarrier : LieGroupSingletonCarrier endpoint := ledger.right.left
  have sameEndpointTangent : hsame endpoint tangent :=
    cont_right_unit_result ledger.right.right.left
  have sameFlowEndpoint : hsame flow endpoint :=
    cont_right_unit_result ledger.right.right.right
  have tangentUnary : UnaryHistory tangent :=
    unary_transport unary_empty (hsame_symm tangentCarrier)
  have endpointUnary : UnaryHistory endpoint :=
    unary_transport tangentUnary (hsame_symm sameEndpointTangent)
  have flowUnary : UnaryHistory flow :=
    unary_transport endpointUnary (hsame_symm sameFlowEndpoint)
  exact And.intro tangentCarrier
    (And.intro endpointCarrier
      (And.intro sameEndpointTangent
        (And.intro sameFlowEndpoint
          (And.intro tangentUnary (And.intro endpointUnary flowUnary)))))

end BEDC.Derived.ExpMapUp
