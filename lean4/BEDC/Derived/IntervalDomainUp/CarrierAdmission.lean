import BEDC.Derived.IntervalDomainUp.TasteGate

namespace BEDC.Derived.IntervalDomainUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark

private theorem IntervalDomainCarrierAdmission_decode_encode :
    ∀ h : BHist,
      IntervalDomainTasteGate_single_carrier_alignment_decodeBHist
          (IntervalDomainTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

theorem IntervalDomainCarrierAdmission (D : IntervalDomainUp) :
    ∃ L R N W Q E H C P A : BHist,
      D = IntervalDomainUp.mk L R N W Q E H C P A ∧
        IntervalDomainTasteGate_single_carrier_alignment_fields D =
          [L, R, N, W, Q, E, H, C, P, A] ∧
          IntervalDomainTasteGate_single_carrier_alignment_fromEventFlow
              (IntervalDomainTasteGate_single_carrier_alignment_toEventFlow D) =
            some D ∧
            IntervalDomainTasteGate_single_carrier_alignment_encodeBHist BHist.Empty =
              ([] : List BMark) ∧
              IntervalDomainTasteGate_single_carrier_alignment_encodeBHist
                  (BHist.e0 BHist.Empty) =
                [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark
  cases D with
  | mk L R N W Q E H C P A =>
      refine ⟨L, R, N, W, Q, E, H, C, P, A, rfl, rfl, ?_, rfl, rfl⟩
      change
        some
          (IntervalDomainUp.mk
            (IntervalDomainTasteGate_single_carrier_alignment_decodeBHist
              (IntervalDomainTasteGate_single_carrier_alignment_encodeBHist L))
            (IntervalDomainTasteGate_single_carrier_alignment_decodeBHist
              (IntervalDomainTasteGate_single_carrier_alignment_encodeBHist R))
            (IntervalDomainTasteGate_single_carrier_alignment_decodeBHist
              (IntervalDomainTasteGate_single_carrier_alignment_encodeBHist N))
            (IntervalDomainTasteGate_single_carrier_alignment_decodeBHist
              (IntervalDomainTasteGate_single_carrier_alignment_encodeBHist W))
            (IntervalDomainTasteGate_single_carrier_alignment_decodeBHist
              (IntervalDomainTasteGate_single_carrier_alignment_encodeBHist Q))
            (IntervalDomainTasteGate_single_carrier_alignment_decodeBHist
              (IntervalDomainTasteGate_single_carrier_alignment_encodeBHist E))
            (IntervalDomainTasteGate_single_carrier_alignment_decodeBHist
              (IntervalDomainTasteGate_single_carrier_alignment_encodeBHist H))
            (IntervalDomainTasteGate_single_carrier_alignment_decodeBHist
              (IntervalDomainTasteGate_single_carrier_alignment_encodeBHist C))
            (IntervalDomainTasteGate_single_carrier_alignment_decodeBHist
              (IntervalDomainTasteGate_single_carrier_alignment_encodeBHist P))
            (IntervalDomainTasteGate_single_carrier_alignment_decodeBHist
              (IntervalDomainTasteGate_single_carrier_alignment_encodeBHist A))) =
          some (IntervalDomainUp.mk L R N W Q E H C P A)
      rw [IntervalDomainCarrierAdmission_decode_encode L,
        IntervalDomainCarrierAdmission_decode_encode R,
        IntervalDomainCarrierAdmission_decode_encode N,
        IntervalDomainCarrierAdmission_decode_encode W,
        IntervalDomainCarrierAdmission_decode_encode Q,
        IntervalDomainCarrierAdmission_decode_encode E,
        IntervalDomainCarrierAdmission_decode_encode H,
        IntervalDomainCarrierAdmission_decode_encode C,
        IntervalDomainCarrierAdmission_decode_encode P,
        IntervalDomainCarrierAdmission_decode_encode A]

end BEDC.Derived.IntervalDomainUp
