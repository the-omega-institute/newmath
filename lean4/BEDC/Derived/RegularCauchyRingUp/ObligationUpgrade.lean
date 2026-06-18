import BEDC.Derived.RegularCauchyRingUp.TasteGate

namespace BEDC.Derived.RegularCauchyRingUp

open BEDC.FKernel.Hist

theorem RegularCauchyRingObligationUpgrade (x : RegularCauchyRingUp) :
    ∃ A B WA WB DA DB S G M L RS RG RM RL ES EG EM EL H C P N : BHist,
      x = RegularCauchyRingUp.mk A B WA WB DA DB S G M L RS RG RM RL ES EG EM EL H C P N ∧
        RegularCauchyRingTasteGate_single_carrier_alignment_fields x =
          [A, B, WA, WB, DA, DB, S, G, M, L, RS, RG, RM, RL, ES, EG, EM, EL, H, C, P, N] ∧
          RegularCauchyRingTasteGate_single_carrier_alignment_fields x =
            [A, B, WA, WB, DA, DB] ++ [S, G, M, L] ++
              [RS, RG, RM, RL] ++ [ES, EG, EM, EL, H, C, P, N] := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk A B WA WB DA DB S G M L RS RG RM RL ES EG EM EL H C P N =>
      exact
        ⟨A, B, WA, WB, DA, DB, S, G, M, L, RS, RG, RM, RL, ES, EG, EM, EL, H, C, P, N,
          rfl, rfl, rfl⟩

end BEDC.Derived.RegularCauchyRingUp
