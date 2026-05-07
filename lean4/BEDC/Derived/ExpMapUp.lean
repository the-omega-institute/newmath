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

theorem ExpMapCarrier_obligation_surface {tangent endpoint flow : BHist} :
    LieAlgebraSingletonCarrier tangent ->
      LieGroupSingletonCarrier endpoint ->
        Cont tangent endpoint flow ->
          LieAlgebraSingletonCarrier tangent ∧ LieGroupSingletonCarrier endpoint ∧
            LieGroupSingletonCarrier flow ∧ hsame flow BHist.Empty ∧ UnaryHistory flow := by
  intro tangentCarrier endpointCarrier flowRow
  have flowEmpty : hsame flow BHist.Empty :=
    cont_respects_hsame tangentCarrier endpointCarrier flowRow (cont_left_unit BHist.Empty)
  have flowUnary : UnaryHistory flow :=
    unary_transport unary_empty (hsame_symm flowEmpty)
  exact And.intro tangentCarrier
    (And.intro endpointCarrier (And.intro flowEmpty (And.intro flowEmpty flowUnary)))

end BEDC.Derived.ExpMapUp
