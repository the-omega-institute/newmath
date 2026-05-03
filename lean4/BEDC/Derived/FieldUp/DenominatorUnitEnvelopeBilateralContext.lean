import BEDC.Derived.FieldUp.DenominatorUnitEnvelope

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

theorem field_rat_denominator_envelope_bilateral_context_cancellation
    {h k l r p q p' q' : BHist} :
    hsame p BHist.Empty -> hsame q BHist.Empty -> hsame p' BHist.Empty ->
      hsame q' BHist.Empty -> FieldRatDenominatorUnitEnvelopeCarrier h ->
        FieldRatDenominatorUnitEnvelopeCarrier k -> RatHistoryCarrier l -> RatHistoryCarrier r ->
          (FieldRatDenominatorUnitEnvelopeClassifier
              (append p (append (append l (append h r)) q))
              (append p' (append (append l (append k r)) q')) ↔
            FieldRatDenominatorUnitEnvelopeClassifier h k) := by
  intro sameP sameQ sameP' sameQ' carrierH carrierK ratL ratR
  have stripEmptyContext :
      FieldRatDenominatorUnitEnvelopeClassifier
          (append p (append (append l (append h r)) q))
          (append p' (append (append l (append k r)) q')) ↔
        FieldRatDenominatorUnitEnvelopeClassifier (append l (append h r))
          (append l (append k r)) :=
    FieldRatDenominatorUnitEnvelopeClassifier_empty_context_iff sameP sameQ sameP' sameQ'
  have cancelBilateral :
      FieldRatDenominatorUnitEnvelopeClassifier (append l (append h r))
          (append l (append k r)) ↔
        FieldRatDenominatorUnitEnvelopeClassifier h k :=
    field_rat_denominator_bilateral_strict_factor_cancellation carrierH carrierK ratL ratR
  constructor
  · intro classified
    exact Iff.mp cancelBilateral (Iff.mp stripEmptyContext classified)
  · intro classified
    exact Iff.mpr stripEmptyContext (Iff.mpr cancelBilateral classified)

end BEDC.Derived.FieldUp
