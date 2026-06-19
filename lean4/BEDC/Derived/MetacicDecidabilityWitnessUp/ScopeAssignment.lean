import BEDC.Derived.MetacicDecidabilityWitnessUp.TasteGate

namespace BEDC.Derived.MetacicDecidabilityWitnessUp

open BEDC.FKernel.Hist

private theorem MetacicDecidabilityWitnessCarrier_scope_assignment_decode_encode :
    ∀ h : BHist,
      metacicDecidabilityWitnessDecodeBHist
        (metacicDecidabilityWitnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

theorem MetacicDecidabilityWitnessCarrier_scope_assignment
    {T S B F R H C P N : BHist} :
    metacicDecidabilityWitnessFields
        (MetacicDecidabilityWitnessUp.mk T S B F R H C P N) =
      [T, S, B, F, R, H, C, P, N] ∧
      metacicDecidabilityWitnessFromEventFlow
          (metacicDecidabilityWitnessToEventFlow
            (MetacicDecidabilityWitnessUp.mk T S B F R H C P N)) =
        some (MetacicDecidabilityWitnessUp.mk T S B F R H C P N) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · rfl
  · change
      some
        (MetacicDecidabilityWitnessUp.mk
          (metacicDecidabilityWitnessDecodeBHist
            (metacicDecidabilityWitnessEncodeBHist T))
          (metacicDecidabilityWitnessDecodeBHist
            (metacicDecidabilityWitnessEncodeBHist S))
          (metacicDecidabilityWitnessDecodeBHist
            (metacicDecidabilityWitnessEncodeBHist B))
          (metacicDecidabilityWitnessDecodeBHist
            (metacicDecidabilityWitnessEncodeBHist F))
          (metacicDecidabilityWitnessDecodeBHist
            (metacicDecidabilityWitnessEncodeBHist R))
          (metacicDecidabilityWitnessDecodeBHist
            (metacicDecidabilityWitnessEncodeBHist H))
          (metacicDecidabilityWitnessDecodeBHist
            (metacicDecidabilityWitnessEncodeBHist C))
          (metacicDecidabilityWitnessDecodeBHist
            (metacicDecidabilityWitnessEncodeBHist P))
          (metacicDecidabilityWitnessDecodeBHist
            (metacicDecidabilityWitnessEncodeBHist N))) =
        some (MetacicDecidabilityWitnessUp.mk T S B F R H C P N)
    rw [MetacicDecidabilityWitnessCarrier_scope_assignment_decode_encode T,
      MetacicDecidabilityWitnessCarrier_scope_assignment_decode_encode S,
      MetacicDecidabilityWitnessCarrier_scope_assignment_decode_encode B,
      MetacicDecidabilityWitnessCarrier_scope_assignment_decode_encode F,
      MetacicDecidabilityWitnessCarrier_scope_assignment_decode_encode R,
      MetacicDecidabilityWitnessCarrier_scope_assignment_decode_encode H,
      MetacicDecidabilityWitnessCarrier_scope_assignment_decode_encode C,
      MetacicDecidabilityWitnessCarrier_scope_assignment_decode_encode P,
      MetacicDecidabilityWitnessCarrier_scope_assignment_decode_encode N]

end BEDC.Derived.MetacicDecidabilityWitnessUp
