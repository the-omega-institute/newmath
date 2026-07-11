import BedcMathlibBridge.Constructive.SecantNumber

/-!
Export witness for the secant-number small-window readback correspondence.
-/

namespace BedcMathlibBridge.Export.SecantNumber

open BedcMathlibBridge.Constructive.SecantNumber

structure SecantNumberExportWitness where
  relation : Nat -> Nat -> Prop
  relation_apply :
    forall n a : Nat,
      relation n a ↔
        BedcMathlibBridge.Constructive.SecantNumber.relationReadback n a
  bedc_apply :
    forall n a : Nat,
      relation n a ↔ BEDC.Derived.ZigzagNumberUp.secantNumber n a
  zero_apply : relation 0 (Nat.pow 1 1)
  one_apply : relation 1 (Nat.pow 1 1)
  two_apply : relation 2 (Nat.pow 2 2 + 1)
  nat_pow_small_values :
    BEDC.Derived.ZigzagNumberUp.secantNumber 0 (Nat.pow 1 1) ∧
      BEDC.Derived.ZigzagNumberUp.secantNumber 1 (Nat.pow 1 1) ∧
        BEDC.Derived.ZigzagNumberUp.secantNumber 2 (Nat.pow 2 2 + 1)
  even_zigzag_small_values :
    (BEDC.Derived.ZigzagNumberUp.secantNumber 0 (Nat.pow 1 1) ∧
        BEDC.Derived.ZigzagNumberUp.ZigzagNumber 0 (Nat.pow 1 1)) ∧
      (BEDC.Derived.ZigzagNumberUp.secantNumber 1 (Nat.pow 1 1) ∧
        BEDC.Derived.ZigzagNumberUp.ZigzagNumber 2 (Nat.pow 1 1)) ∧
        (BEDC.Derived.ZigzagNumberUp.secantNumber 2 (Nat.pow 2 2 + 1) ∧
          BEDC.Derived.ZigzagNumberUp.ZigzagNumber 4 (Nat.pow 2 2 + 1))
  mathlib_anchor : Nat.succ_injective = Nat.succ_injective

def secantNumberExport : SecantNumberExportWitness where
  relation := relationReadback
  relation_apply := by
    intro n a
    rfl
  bedc_apply := by
    intro n a
    exact relationReadback_apply
  zero_apply := zero_value
  one_apply := one_value
  two_apply := two_value
  nat_pow_small_values := small_values_nat_pow_anchor
  even_zigzag_small_values :=
    ⟨⟨zero_value, BEDC.Derived.ZigzagNumberUp.zigzag_A0⟩,
      ⟨⟨one_value, BEDC.Derived.ZigzagNumberUp.zigzag_A2⟩,
        ⟨two_value, BEDC.Derived.ZigzagNumberUp.zigzag_A4⟩⟩⟩
  mathlib_anchor := mathlibPowAnchor

theorem secantNumber_small_values_nat_pow_anchor
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibPowAnchor) :
    BEDC.Derived.ZigzagNumberUp.secantNumber 0 (Nat.pow 1 1) ∧
      BEDC.Derived.ZigzagNumberUp.secantNumber 1 (Nat.pow 1 1) ∧
        BEDC.Derived.ZigzagNumberUp.secantNumber 2 (Nat.pow 2 2 + 1) :=
  BedcMathlibBridge.Constructive.SecantNumber.small_values_nat_pow_anchor

end BedcMathlibBridge.Export.SecantNumber
