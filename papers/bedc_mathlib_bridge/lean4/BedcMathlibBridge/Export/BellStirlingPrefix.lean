import BedcMathlibBridge.Constructive.BellStirlingPrefix

namespace BedcMathlibBridge.Export.BellStirlingPrefix

open BedcMathlibBridge.Constructive.BellStirlingPrefix

structure BellStirlingPrefixExportWitness where
  readback : Nat -> Nat -> Nat
  readback_apply : ∀ n k : Nat, readback n k = prefixToNat n k
  bedc_apply : ∀ n k : Nat, readback n k = BEDC.Derived.BellNumberUp.bellStirlingPrefix n k
  zero_apply : ∀ n : Nat, readback n 0 = Nat.stirlingSecond n 0
  succ_increment_apply : ∀ n k : Nat,
    readback n (Nat.succ k) = readback n k + Nat.stirlingSecond n (Nat.succ k)
  succ_increment_recurrence_apply : ∀ n k : Nat,
    readback (Nat.succ n) (Nat.succ k) =
      readback (Nat.succ n) k +
        (Nat.succ k * Nat.stirlingSecond n (Nat.succ k) + Nat.stirlingSecond n k)

def bellStirlingPrefixExport : BellStirlingPrefixExportWitness where
  readback := prefixToNat
  readback_apply := by
    intro n k
    rfl
  bedc_apply := prefixToNat_apply
  zero_apply := prefixToNat_zero
  succ_increment_apply := prefixToNat_succ_increment
  succ_increment_recurrence_apply := prefixToNat_succ_succ_increment_mathlib_recurrence

theorem bellStirlingPrefix_increment_eq_nat_stirlingSecond (n k : Nat) :
    BEDC.Derived.BellNumberUp.bellStirlingPrefix n (Nat.succ k) =
      BEDC.Derived.BellNumberUp.bellStirlingPrefix n k +
        Nat.stirlingSecond n (Nat.succ k) := by
  change
    prefixToNat n (Nat.succ k) =
      prefixToNat n k + Nat.stirlingSecond n (Nat.succ k)
  exact prefixToNat_succ_increment n k

theorem bellStirlingPrefix_increment_matches_nat_stirlingSecond_recurrence (n k : Nat) :
    BEDC.Derived.BellNumberUp.bellStirlingPrefix (Nat.succ n) (Nat.succ k) =
      BEDC.Derived.BellNumberUp.bellStirlingPrefix (Nat.succ n) k +
        (Nat.succ k * Nat.stirlingSecond n (Nat.succ k) + Nat.stirlingSecond n k) := by
  change
    prefixToNat (Nat.succ n) (Nat.succ k) =
      prefixToNat (Nat.succ n) k +
        (Nat.succ k * Nat.stirlingSecond n (Nat.succ k) + Nat.stirlingSecond n k)
  exact prefixToNat_succ_succ_increment_mathlib_recurrence n k

end BedcMathlibBridge.Export.BellStirlingPrefix
