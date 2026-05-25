import BEDC.Derived.DirectedSetUp.TasteGate

namespace BEDC.Derived.DirectedSetUp

theorem DirectedSetCarrier_fields_faithful :
    ∀ x y : DirectedSetUp, directedSetFields x = directedSetFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I1 Le1 W1 U1 H1 C1 P1 N1 =>
      cases y with
      | mk I2 Le2 W2 U2 H2 C2 P2 N2 =>
          cases hfields
          rfl

end BEDC.Derived.DirectedSetUp
