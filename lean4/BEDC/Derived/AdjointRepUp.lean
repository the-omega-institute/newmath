import BEDC.Derived.LieAlgebraUp
import BEDC.Derived.LieGroupUp
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Units
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.AdjointRepUp

open BEDC.Derived.LieAlgebraUp
open BEDC.Derived.LieGroupUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem AdjointRepSingleton_classifier_stability_obligation
    {s s' tangent tangent' sx sx' conj conj' adj adj' : BHist} :
    LieGroupSingletonCarrier s ->
      LieGroupSingletonCarrier s' ->
        LieAlgebraSingletonCarrier tangent ->
          LieAlgebraSingletonCarrier tangent' ->
            hsame s s' ->
              hsame tangent tangent' ->
                Cont s tangent sx ->
                  Cont s' tangent' sx' ->
                    Cont sx (LieGroupSingletonInv s) conj ->
                      Cont sx' (LieGroupSingletonInv s') conj' ->
                        Cont BHist.Empty tangent adj ->
                          Cont BHist.Empty tangent' adj' ->
                            hsame sx sx' ∧ hsame conj conj' ∧ hsame adj adj' ∧
                              LieGroupSingletonClassifier conj conj' ∧
                                LieAlgebraSingletonCarrier adj ∧
                                  LieAlgebraSingletonCarrier adj' ∧
                                    UnaryHistory conj ∧ UnaryHistory conj' ∧
                                      UnaryHistory adj ∧ UnaryHistory adj' := by
  intro carrierS carrierS' carrierTangent carrierTangent' sameS sameTangent sxRow sxRow'
  intro conjRow conjRow' adjRow adjRow'
  have sxSame : hsame sx sx' :=
    cont_respects_hsame sameS sameTangent sxRow sxRow'
  have sxCarrier : LieGroupSingletonCarrier sx :=
    cont_respects_hsame carrierS carrierTangent sxRow (cont_left_unit BHist.Empty)
  have sxCarrier' : LieGroupSingletonCarrier sx' :=
    cont_respects_hsame carrierS' carrierTangent' sxRow' (cont_left_unit BHist.Empty)
  have invCarrier : LieGroupSingletonCarrier (LieGroupSingletonInv s) := by
    rfl
  have invCarrier' : LieGroupSingletonCarrier (LieGroupSingletonInv s') := by
    rfl
  have invSame : hsame (LieGroupSingletonInv s) (LieGroupSingletonInv s') := by
    rfl
  have conjSame : hsame conj conj' :=
    cont_respects_hsame sxSame invSame conjRow conjRow'
  have conjCarrier : LieGroupSingletonCarrier conj :=
    cont_respects_hsame sxCarrier invCarrier conjRow (cont_left_unit BHist.Empty)
  have conjCarrier' : LieGroupSingletonCarrier conj' :=
    cont_respects_hsame sxCarrier' invCarrier' conjRow' (cont_left_unit BHist.Empty)
  have adjCarrier : LieAlgebraSingletonCarrier adj :=
    cont_respects_hsame (hsame_refl BHist.Empty) carrierTangent adjRow
      (cont_left_unit BHist.Empty)
  have adjCarrier' : LieAlgebraSingletonCarrier adj' :=
    cont_respects_hsame (hsame_refl BHist.Empty) carrierTangent' adjRow'
      (cont_left_unit BHist.Empty)
  have adjSame : hsame adj adj' :=
    cont_respects_hsame (hsame_refl BHist.Empty) sameTangent adjRow adjRow'
  have conjClassified : LieGroupSingletonClassifier conj conj' :=
    And.intro conjCarrier (And.intro conjCarrier' conjSame)
  have conjUnary : UnaryHistory conj :=
    unary_transport unary_empty (hsame_symm conjCarrier)
  have conjUnary' : UnaryHistory conj' :=
    unary_transport unary_empty (hsame_symm conjCarrier')
  have adjUnary : UnaryHistory adj :=
    unary_transport unary_empty (hsame_symm adjCarrier)
  have adjUnary' : UnaryHistory adj' :=
    unary_transport unary_empty (hsame_symm adjCarrier')
  exact And.intro sxSame
    (And.intro conjSame
      (And.intro adjSame
        (And.intro conjClassified
          (And.intro adjCarrier
            (And.intro adjCarrier'
              (And.intro conjUnary
                (And.intro conjUnary' (And.intro adjUnary adjUnary'))))))))

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

end BEDC.Derived.AdjointRepUp
