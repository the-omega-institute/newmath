import BEDC.Derived.LieAlgebraUp
import BEDC.Derived.LieGroupUp

namespace BEDC.Derived.AdjointRepUp

open BEDC.Derived.LieAlgebraUp
open BEDC.Derived.LieGroupUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem AdjointRepDifferentialAction_obligation {acting endpoint result chart : BHist} :
    LieGroupSingletonCarrier acting -> LieAlgebraSingletonCarrier endpoint ->
      LieAlgebraAdjointAction acting endpoint result -> Cont BHist.Empty result chart ->
        LieAlgebraSingletonCarrier result ∧ LieAlgebraSingletonCarrier chart ∧
          hsame chart result ∧ hsame chart BHist.Empty ∧
            UnaryHistory result ∧ UnaryHistory chart := by
  intro actingCarrier endpointCarrier action chartRow
  have resultEmpty : hsame result BHist.Empty :=
    cont_respects_hsame actingCarrier endpointCarrier action.right.right.left
      (cont_left_unit BHist.Empty)
  have chartResult : hsame chart result :=
    cont_left_unit_result chartRow
  have chartEmpty : hsame chart BHist.Empty :=
    hsame_trans chartResult resultEmpty
  have chartUnary : UnaryHistory chart :=
    unary_transport action.right.right.right (hsame_symm chartResult)
  exact And.intro resultEmpty
    (And.intro chartEmpty
      (And.intro chartResult
        (And.intro chartEmpty (And.intro action.right.right.right chartUnary))))

end BEDC.Derived.AdjointRepUp
