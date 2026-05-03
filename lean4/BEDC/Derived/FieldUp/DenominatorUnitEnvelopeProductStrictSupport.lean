import BEDC.Derived.FieldUp.DenominatorUnitEnvelope

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem field_rat_denominator_unit_envelope_product_strict_support_congruence {h h' k k' : BHist} :
    FieldRatDenominatorUnitEnvelopeCarrier h -> FieldRatDenominatorUnitEnvelopeCarrier h' ->
      FieldRatDenominatorUnitEnvelopeCarrier k -> FieldRatDenominatorUnitEnvelopeCarrier k' ->
        FieldRatDenominatorUnitEnvelopeClassifier h h' ->
          FieldRatDenominatorUnitEnvelopeClassifier k k' ->
            (RatHistoryCarrier (append h k) <-> RatHistoryCarrier (append h' k')) := by
  intro carrierH carrierH' carrierK carrierK' classifiedH classifiedK
  have productCarrier : FieldRatDenominatorUnitEnvelopeCarrier (append h k) :=
    field_rat_denominator_unit_envelope_monoid_laws.right.left carrierH carrierK
  have productCarrier' : FieldRatDenominatorUnitEnvelopeCarrier (append h' k') :=
    field_rat_denominator_unit_envelope_monoid_laws.right.left carrierH' carrierK'
  have productClassified :
      FieldRatDenominatorUnitEnvelopeClassifier (append h k) (append h' k') :=
    field_rat_denominator_unit_envelope_classifier_append_closed classifiedH classifiedK
  exact (field_rat_denominator_unit_envelope_strict_support_laws productCarrier
    productCarrier').left productClassified

end BEDC.Derived.FieldUp
