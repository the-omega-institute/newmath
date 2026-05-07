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

theorem AdjointRepClassifier_stability_obligation
    {s s' x x' tangent tangent' sx sx' conj conj' ad ad' : BHist} :
    LieGroupSingletonCarrier s -> LieGroupSingletonCarrier s' ->
      LieGroupSingletonClassifier s s' -> LieAlgebraSingletonCarrier x ->
        LieAlgebraSingletonCarrier x' -> hsame x x' ->
          LieAlgebraSingletonCarrier tangent -> LieAlgebraSingletonCarrier tangent' ->
            hsame tangent tangent' -> Cont s x sx ->
              Cont sx (LieGroupSingletonInv s) conj -> Cont s' x' sx' ->
                Cont sx' (LieGroupSingletonInv s') conj' -> Cont s tangent ad ->
                  Cont s' tangent' ad' ->
                    LieGroupSingletonClassifier conj conj' ∧ LieAlgebraSingletonCarrier ad ∧
                      LieAlgebraSingletonCarrier ad' ∧ hsame ad ad' := by
  intro carrierS carrierS' classifiedS carrierX carrierX' sameX carrierTangent
    carrierTangent' sameTangent sxRow conjRow sxRow' conjRow' adRow adRow'
  have sameSX : hsame sx sx' :=
    cont_respects_hsame classifiedS.right.right sameX sxRow sxRow'
  have invSame : hsame (LieGroupSingletonInv s) (LieGroupSingletonInv s') := by
    rfl
  have conjSame : hsame conj conj' :=
    cont_respects_hsame sameSX invSame conjRow conjRow'
  have sxCarrier : LieGroupSingletonCarrier sx :=
    cont_respects_hsame carrierS carrierX sxRow (cont_left_unit BHist.Empty)
  have invCarrier : LieGroupSingletonCarrier (LieGroupSingletonInv s) := by
    rfl
  have conjCarrier : LieGroupSingletonCarrier conj :=
    cont_respects_hsame sxCarrier invCarrier conjRow (cont_left_unit BHist.Empty)
  have conjCarrier' : LieGroupSingletonCarrier conj' :=
    hsame_trans (hsame_symm conjSame) conjCarrier
  have conjClassified : LieGroupSingletonClassifier conj conj' :=
    And.intro conjCarrier (And.intro conjCarrier' conjSame)
  have adCarrier : LieAlgebraSingletonCarrier ad :=
    cont_respects_hsame carrierS carrierTangent adRow (cont_left_unit BHist.Empty)
  have adCarrier' : LieAlgebraSingletonCarrier ad' :=
    cont_respects_hsame carrierS' carrierTangent' adRow' (cont_left_unit BHist.Empty)
  have adSame : hsame ad ad' :=
    cont_respects_hsame classifiedS.right.right sameTangent adRow adRow'
  exact And.intro conjClassified (And.intro adCarrier (And.intro adCarrier' adSame))

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

theorem AdjointRepConjugation_carrier_obligation {g x gx conj : BHist} :
    LieGroupSingletonCarrier g -> LieAlgebraSingletonCarrier x -> Cont g x gx ->
      Cont gx (LieGroupSingletonInv g) conj ->
        LieGroupSingletonCarrier conj ∧ hsame conj BHist.Empty ∧ UnaryHistory conj := by
  intro groupCarrier algebraCarrier gxRow conjRow
  have gxCarrier : LieGroupSingletonCarrier gx :=
    cont_respects_hsame groupCarrier algebraCarrier gxRow (cont_left_unit BHist.Empty)
  have inverseCarrier : LieGroupSingletonCarrier (LieGroupSingletonInv g) := by
    rfl
  have conjCarrier : LieGroupSingletonCarrier conj :=
    cont_respects_hsame gxCarrier inverseCarrier conjRow (cont_left_unit BHist.Empty)
  have conjUnary : UnaryHistory conj :=
    unary_transport unary_empty (hsame_symm conjCarrier)
  exact And.intro conjCarrier (And.intro conjCarrier conjUnary)

def AdjointRepActionEndpoint (group algebra endpoint : BHist) : Prop :=
  LieGroupSingletonCarrier group ∧ LieAlgebraSingletonCarrier algebra ∧
    ∃ action : BHist, Cont group algebra action ∧ hsame action endpoint

theorem AdjointRepConjugationCarrier_obligation
    {group algebra action endpoint : BHist} :
    LieGroupSingletonCarrier group -> LieAlgebraSingletonCarrier algebra ->
      Cont group algebra action -> hsame action endpoint ->
        AdjointRepActionEndpoint group algebra endpoint ∧ UnaryHistory endpoint := by
  intro groupCarrier algebraCarrier actionRow actionEndpoint
  have actionEmpty : hsame action BHist.Empty :=
    cont_respects_hsame groupCarrier algebraCarrier actionRow (cont_left_unit BHist.Empty)
  have endpointEmpty : hsame endpoint BHist.Empty :=
    hsame_trans (hsame_symm actionEndpoint) actionEmpty
  have endpointUnary : UnaryHistory endpoint :=
    unary_transport unary_empty (hsame_symm endpointEmpty)
  exact And.intro
    (And.intro groupCarrier
        (And.intro algebraCarrier
          (Exists.intro action (And.intro actionRow actionEndpoint))))
    endpointUnary

theorem AdjointRepDependencySource_obligation {group algebra action differential : BHist} :
    LieGroupSingletonCarrier group -> LieAlgebraSingletonCarrier algebra ->
      Cont group algebra action -> Cont BHist.Empty algebra differential ->
        LieGroupSingletonCarrier group ∧ LieAlgebraSingletonCarrier algebra ∧
          AdjointRepActionEndpoint group algebra action ∧ LieAlgebraSingletonCarrier differential ∧
            UnaryHistory group ∧ UnaryHistory algebra ∧ UnaryHistory action ∧
              UnaryHistory differential := by
  intro groupCarrier algebraCarrier actionRow differentialRow
  have actionEndpoint : AdjointRepActionEndpoint group algebra action :=
    And.intro groupCarrier
      (And.intro algebraCarrier
        (Exists.intro action (And.intro actionRow (hsame_refl action))))
  have actionEmpty : hsame action BHist.Empty :=
    cont_respects_hsame groupCarrier algebraCarrier actionRow (cont_left_unit BHist.Empty)
  have differentialAlgebra : hsame differential algebra :=
    cont_left_unit_result differentialRow
  have differentialCarrier : LieAlgebraSingletonCarrier differential :=
    hsame_trans differentialAlgebra algebraCarrier
  have groupUnary : UnaryHistory group :=
    unary_transport unary_empty (hsame_symm groupCarrier)
  have algebraUnary : UnaryHistory algebra :=
    unary_transport unary_empty (hsame_symm algebraCarrier)
  have actionUnary : UnaryHistory action :=
    unary_transport unary_empty (hsame_symm actionEmpty)
  have differentialUnary : UnaryHistory differential :=
    unary_transport unary_empty (hsame_symm differentialCarrier)
  exact And.intro groupCarrier
    (And.intro algebraCarrier
      (And.intro actionEndpoint
        (And.intro differentialCarrier
          (And.intro groupUnary
            (And.intro algebraUnary (And.intro actionUnary differentialUnary))))))

theorem AdjointRepAutomorphism_target_obligation {g x gx conj invAction composite : BHist} :
    LieGroupSingletonCarrier g -> LieAlgebraSingletonCarrier x -> Cont g x gx ->
      Cont gx (LieGroupSingletonInv g) conj -> Cont (LieGroupSingletonInv g) x invAction ->
        Cont conj invAction composite ->
          LieGroupSingletonCarrier conj ∧ LieGroupSingletonCarrier invAction ∧
            LieAlgebraSingletonCarrier composite ∧ hsame composite BHist.Empty ∧
              UnaryHistory conj ∧ UnaryHistory invAction ∧ UnaryHistory composite := by
  intro groupCarrier algebraCarrier gxRow conjRow invActionRow compositeRow
  have gxCarrier : LieGroupSingletonCarrier gx :=
    cont_respects_hsame groupCarrier algebraCarrier gxRow (cont_left_unit BHist.Empty)
  have inverseCarrier : LieGroupSingletonCarrier (LieGroupSingletonInv g) := by
    rfl
  have conjCarrier : LieGroupSingletonCarrier conj :=
    cont_respects_hsame gxCarrier inverseCarrier conjRow (cont_left_unit BHist.Empty)
  have invActionCarrier : LieGroupSingletonCarrier invAction :=
    cont_respects_hsame inverseCarrier algebraCarrier invActionRow (cont_left_unit BHist.Empty)
  have compositeCarrier : LieAlgebraSingletonCarrier composite :=
    cont_respects_hsame conjCarrier invActionCarrier compositeRow (cont_left_unit BHist.Empty)
  have conjUnary : UnaryHistory conj :=
    unary_transport unary_empty (hsame_symm conjCarrier)
  have invActionUnary : UnaryHistory invAction :=
    unary_transport unary_empty (hsame_symm invActionCarrier)
  have compositeUnary : UnaryHistory composite :=
    unary_transport unary_empty (hsame_symm compositeCarrier)
  exact And.intro conjCarrier
    (And.intro invActionCarrier
      (And.intro compositeCarrier
        (And.intro compositeCarrier
          (And.intro conjUnary (And.intro invActionUnary compositeUnary)))))

theorem AdjointRepAutomorphismTarget_obligation
    {group algebra endpoint inverse composite : BHist} :
    AdjointRepActionEndpoint group algebra endpoint -> Cont endpoint inverse BHist.Empty ->
      Cont endpoint endpoint composite ->
        AdjointRepActionEndpoint group algebra endpoint ∧ LieGroupSingletonCarrier inverse ∧
          LieAlgebraSingletonCarrier composite ∧ hsame (append endpoint inverse) BHist.Empty ∧
            hsame (append endpoint endpoint) composite ∧ UnaryHistory composite := by
  intro endpointWitness inverseRow compositeRow
  cases endpointWitness.right.right with
  | intro action actionData =>
      have actionEmpty : hsame action BHist.Empty :=
        cont_respects_hsame endpointWitness.left endpointWitness.right.left actionData.left
          (cont_left_unit BHist.Empty)
      have endpointEmpty : hsame endpoint BHist.Empty :=
        hsame_trans (hsame_symm actionData.right) actionEmpty
      have inverseEmpty : hsame inverse BHist.Empty :=
        (cont_empty_result_iff.mp inverseRow).right
      have compositeEmpty : hsame composite BHist.Empty :=
        cont_respects_hsame endpointEmpty endpointEmpty compositeRow (cont_left_unit BHist.Empty)
      have appendInverseEmpty : hsame (append endpoint inverse) BHist.Empty :=
        inverseRow.symm
      have appendCompositeSame : hsame (append endpoint endpoint) composite :=
        compositeRow.symm
      have compositeUnary : UnaryHistory composite :=
        unary_transport unary_empty (hsame_symm compositeEmpty)
      exact And.intro
        (And.intro endpointWitness.left
          (And.intro endpointWitness.right.left
            (Exists.intro action actionData)))
        (And.intro inverseEmpty
          (And.intro compositeEmpty
            (And.intro appendInverseEmpty
              (And.intro appendCompositeSame compositeUnary))))

end BEDC.Derived.AdjointRepUp
