import BEDC.Derived.LieGroupUp

namespace BEDC.Derived.AdjointRepUp

open BEDC.Derived.LieAlgebraUp
open BEDC.Derived.LieGroupUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

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

end BEDC.Derived.AdjointRepUp
