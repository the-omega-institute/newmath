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

end BEDC.Derived.AdjointRepUp
