import BEDC.Derived.LieAlgebraUp
import BEDC.Derived.LieGroupUp
import BEDC.FKernel.Cont.Units

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

theorem AdjointRepSingleton_action_differential_endpoint
    {g x action differential bracket : BHist} :
    LieGroupSingletonCarrier g ->
      LieAlgebraSingletonCarrier x ->
        Cont g x action ->
          Cont BHist.Empty x differential ->
            Cont x x bracket ->
              hsame action BHist.Empty ∧ hsame differential x ∧
                hsame bracket BHist.Empty ∧ UnaryHistory action ∧
                  UnaryHistory differential := by
  intro groupCarrier algebraCarrier actionRow differentialRow bracketRow
  have actionEmpty : hsame action BHist.Empty :=
    cont_respects_hsame groupCarrier algebraCarrier actionRow (cont_left_unit BHist.Empty)
  have differentialSame : hsame differential x :=
    cont_left_unit_result differentialRow
  have bracketEmpty : hsame bracket BHist.Empty :=
    cont_respects_hsame algebraCarrier algebraCarrier bracketRow (cont_left_unit BHist.Empty)
  have actionUnary : UnaryHistory action :=
    unary_transport unary_empty (hsame_symm actionEmpty)
  have differentialUnary : UnaryHistory differential :=
    unary_transport unary_empty (hsame_symm (hsame_trans differentialSame algebraCarrier))
  exact And.intro actionEmpty
    (And.intro differentialSame
      (And.intro bracketEmpty (And.intro actionUnary differentialUnary)))

theorem AdjointRepClassifier_stability_obligation
    {acting acting' endpoint endpoint' action action' differential differential' chart chart' :
      BHist} :
    LieGroupSingletonClassifier acting acting' ->
      hsame endpoint endpoint' ->
        LieAlgebraAdjointAction acting endpoint action ->
          LieAlgebraAdjointAction acting' endpoint' action' ->
            Cont BHist.Empty endpoint differential ->
              Cont BHist.Empty endpoint' differential' ->
                Cont BHist.Empty action chart ->
                  Cont BHist.Empty action' chart' ->
                    hsame action action' ∧ hsame differential differential' ∧
                      hsame chart chart' ∧ UnaryHistory action' ∧ UnaryHistory chart' := by
  intro actingClassified sameEndpoint actionRow actionRow' differentialRow differentialRow'
    chartRow chartRow'
  have sameAction : hsame action action' :=
    cont_respects_hsame actingClassified.right.right sameEndpoint actionRow.right.right.left
      actionRow'.right.right.left
  have sameDifferential : hsame differential differential' :=
    cont_respects_hsame (hsame_refl BHist.Empty) sameEndpoint differentialRow differentialRow'
  have sameChart : hsame chart chart' :=
    cont_respects_hsame (hsame_refl BHist.Empty) sameAction chartRow chartRow'
  have chartUnary : UnaryHistory chart' :=
    unary_transport actionRow'.right.right.right (hsame_symm (cont_left_unit_result chartRow'))
  exact And.intro sameAction
    (And.intro sameDifferential
      (And.intro sameChart (And.intro actionRow'.right.right.right chartUnary)))

end BEDC.Derived.AdjointRepUp
