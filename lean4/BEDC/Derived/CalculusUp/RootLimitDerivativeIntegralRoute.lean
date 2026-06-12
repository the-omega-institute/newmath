import BEDC.Derived.CalculusUp.TasteGate

namespace BEDC.Derived.CalculusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow

theorem CalculusRootLimitDerivativeIntegralRoute
    (R L C D I Q H T P N : BHist) :
    calculusFromEventFlow (calculusToEventFlow (CalculusUp.mk R L C D I Q H T P N)) =
        some (CalculusUp.mk R L C D I Q H T P N) ∧
      calculusToEventFlow (CalculusUp.mk R L C D I Q H T P N) =
        [calculusEncodeBHist R, calculusEncodeBHist L, calculusEncodeBHist C,
          calculusEncodeBHist D, calculusEncodeBHist I, calculusEncodeBHist Q,
          calculusEncodeBHist H, calculusEncodeBHist T, calculusEncodeBHist P,
          calculusEncodeBHist N] ∧
        calculusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · change
      some
        (CalculusUp.mk
          (calculusDecodeBHist (calculusEncodeBHist R))
          (calculusDecodeBHist (calculusEncodeBHist L))
          (calculusDecodeBHist (calculusEncodeBHist C))
          (calculusDecodeBHist (calculusEncodeBHist D))
          (calculusDecodeBHist (calculusEncodeBHist I))
          (calculusDecodeBHist (calculusEncodeBHist Q))
          (calculusDecodeBHist (calculusEncodeBHist H))
          (calculusDecodeBHist (calculusEncodeBHist T))
          (calculusDecodeBHist (calculusEncodeBHist P))
          (calculusDecodeBHist (calculusEncodeBHist N))) =
        some (CalculusUp.mk R L C D I Q H T P N)
    rw [CalculusTasteGate_single_carrier_alignment.1 R,
      CalculusTasteGate_single_carrier_alignment.1 L,
      CalculusTasteGate_single_carrier_alignment.1 C,
      CalculusTasteGate_single_carrier_alignment.1 D,
      CalculusTasteGate_single_carrier_alignment.1 I,
      CalculusTasteGate_single_carrier_alignment.1 Q,
      CalculusTasteGate_single_carrier_alignment.1 H,
      CalculusTasteGate_single_carrier_alignment.1 T,
      CalculusTasteGate_single_carrier_alignment.1 P,
      CalculusTasteGate_single_carrier_alignment.1 N]
  · constructor
    · rfl
    · rfl

end BEDC.Derived.CalculusUp
