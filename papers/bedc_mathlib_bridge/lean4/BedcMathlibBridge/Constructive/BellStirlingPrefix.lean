import BEDC.Derived.BellNumberUp
import BedcMathlibBridge.Constructive.StirlingSecond

namespace BedcMathlibBridge.Constructive.BellStirlingPrefix

private def mathlibStirlingSecondProvenanceAnchor : Unit :=
  let _ : ∀ n k : Nat, Nat.stirlingSecond n k = Nat.stirlingSecond n k :=
    fun _ _ => rfl
  ()

def prefixToNat (n k : Nat) : Nat :=
  let _ := mathlibStirlingSecondProvenanceAnchor
  BEDC.Derived.BellNumberUp.bellStirlingPrefix n k

theorem prefixToNat_apply (n k : Nat) :
    prefixToNat n k = BEDC.Derived.BellNumberUp.bellStirlingPrefix n k :=
  rfl

theorem prefixToNat_zero (n : Nat) :
    prefixToNat n 0 = Nat.stirlingSecond n 0 := by
  calc
    prefixToNat n 0 = BEDC.Derived.StirlingUp.stirlingSecond n 0 :=
      BEDC.Derived.BellNumberUp.bellStirlingPrefix_zero n
    _ = Nat.stirlingSecond n 0 := by
      change
        BedcMathlibBridge.Constructive.StirlingSecond.toNat n 0 =
          Nat.stirlingSecond n 0
      exact BedcMathlibBridge.Constructive.StirlingSecond.toNat_eq_nat_stirlingSecond n 0

theorem prefixToNat_succ_increment (n k : Nat) :
    prefixToNat n (Nat.succ k) = prefixToNat n k + Nat.stirlingSecond n (Nat.succ k) := by
  change
    BEDC.Derived.BellNumberUp.bellStirlingPrefix n (Nat.succ k) =
      BEDC.Derived.BellNumberUp.bellStirlingPrefix n k +
        Nat.stirlingSecond n (Nat.succ k)
  calc
    BEDC.Derived.BellNumberUp.bellStirlingPrefix n (Nat.succ k) =
        BEDC.Derived.BellNumberUp.bellStirlingPrefix n k +
          BEDC.Derived.StirlingUp.stirlingSecond n (Nat.succ k) :=
      BEDC.Derived.BellNumberUp.bellStirlingPrefix_succ n k
    _ = BEDC.Derived.BellNumberUp.bellStirlingPrefix n k +
          Nat.stirlingSecond n (Nat.succ k) := by
      have h :
          BEDC.Derived.StirlingUp.stirlingSecond n (Nat.succ k) =
            Nat.stirlingSecond n (Nat.succ k) := by
        change
          BedcMathlibBridge.Constructive.StirlingSecond.toNat n (Nat.succ k) =
            Nat.stirlingSecond n (Nat.succ k)
        exact
          BedcMathlibBridge.Constructive.StirlingSecond.toNat_eq_nat_stirlingSecond
            n (Nat.succ k)
      rw [h]

theorem prefixToNat_succ_succ_increment_mathlib_recurrence (n k : Nat) :
    prefixToNat (Nat.succ n) (Nat.succ k) =
      prefixToNat (Nat.succ n) k +
        (Nat.succ k * Nat.stirlingSecond n (Nat.succ k) + Nat.stirlingSecond n k) := by
  calc
    prefixToNat (Nat.succ n) (Nat.succ k) =
        prefixToNat (Nat.succ n) k +
          Nat.stirlingSecond (Nat.succ n) (Nat.succ k) :=
      prefixToNat_succ_increment (Nat.succ n) k
    _ = prefixToNat (Nat.succ n) k +
          (Nat.succ k * Nat.stirlingSecond n (Nat.succ k) + Nat.stirlingSecond n k) := by
      rw [Nat.stirlingSecond_succ_succ n k]

end BedcMathlibBridge.Constructive.BellStirlingPrefix
