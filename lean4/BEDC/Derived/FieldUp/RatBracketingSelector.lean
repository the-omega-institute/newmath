import BEDC.Derived.FieldUp.RatDenomUnit

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Mark
open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

def FieldRatBracketingEndpointSelector (s : BMark) (h k l : BHist) : BHist :=
  match s with
  | BMark.b0 => append (append h k) l
  | BMark.b1 => append h (append k l)

theorem FieldRatBracketingEndpointSelector_denominator_classifier {h k l : BHist} :
    RatDenomUnitCarrier h -> RatDenomUnitCarrier k -> RatDenomUnitCarrier l ->
      forall s t : BMark,
        RatDenomUnitClassifier (FieldRatBracketingEndpointSelector s h k l)
          (FieldRatBracketingEndpointSelector t h k l) := by
  intro carrierH carrierK carrierL s t
  have carrierHK : RatDenomUnitCarrier (append h k) :=
    field_rat_denominator_empty_unit_continuation_monoid_laws.right.left carrierH carrierK
  have carrierKL : RatDenomUnitCarrier (append k l) :=
    field_rat_denominator_empty_unit_continuation_monoid_laws.right.left carrierK carrierL
  have carrierLeft : RatDenomUnitCarrier (append (append h k) l) :=
    field_rat_denominator_empty_unit_continuation_monoid_laws.right.left carrierHK carrierL
  have carrierRight : RatDenomUnitCarrier (append h (append k l)) :=
    field_rat_denominator_empty_unit_continuation_monoid_laws.right.left carrierH carrierKL
  have classifiedLeftRight :
      RatDenomUnitClassifier (append (append h k) l) (append h (append k l)) :=
    field_rat_denominator_empty_unit_continuation_monoid_laws.right.right.right.left
      carrierH carrierK carrierL
  cases s with
  | b0 =>
      cases t with
      | b0 =>
          exact And.intro carrierLeft (And.intro carrierLeft (hsame_refl _))
      | b1 =>
          exact classifiedLeftRight
  | b1 =>
      cases t with
      | b0 =>
          exact And.intro carrierRight
            (And.intro carrierLeft (hsame_symm classifiedLeftRight.right.right))
      | b1 =>
          exact And.intro carrierRight (And.intro carrierRight (hsame_refl _))

end BEDC.Derived.FieldUp
