import BedcMathlibBridge.Constructive.Lah
import BEDC.Derived.LahNumberUp
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic

namespace BedcMathlibBridge.Constructive.LahNumber

private def mathlibChooseFactorialProvenanceAnchor : Unit :=
  let _ : ∀ n k : Nat, Nat.choose n k = Nat.choose n k := fun _ _ => rfl
  let _ : ∀ n : Nat, Nat.factorial n = Nat.factorial n := fun _ => rfl
  ()

def firstColumnChooseReadback (n : Nat) : Nat :=
  let _ := mathlibChooseFactorialProvenanceAnchor
  BEDC.Derived.LahNumberUp.lahNumber (Nat.succ n) 1

theorem firstColumnChooseReadback_apply (n : Nat) :
    firstColumnChooseReadback n =
      BEDC.Derived.LahNumberUp.lahNumber (Nat.succ n) 1 := by
  rfl

theorem firstColumnChooseReadback_eq_nat_choose_factorial (n : Nat) :
    firstColumnChooseReadback n =
      Nat.choose n 0 * Nat.factorial (Nat.succ n) := by
  calc
    firstColumnChooseReadback n =
        BEDC.Derived.LahNumberUp.lahNumber (Nat.succ n) 1 := by
      rfl
    _ = BEDC.Derived.LahNumberUp.factorialNat (Nat.succ n) :=
      BEDC.Derived.LahNumberUp.lahNumber_succ_one n
    _ = Nat.factorial (Nat.succ n) := by
      change BEDC.Derived.StirlingFirstUp.factorialNat (Nat.succ n) =
        Nat.factorial (Nat.succ n)
      exact BedcMathlibBridge.Constructive.Lah.factorialNat_eq_nat_factorial
        (Nat.succ n)
    _ = Nat.choose n 0 * Nat.factorial (Nat.succ n) := by
      rw [Nat.choose_zero_right, Nat.one_mul]

end BedcMathlibBridge.Constructive.LahNumber
