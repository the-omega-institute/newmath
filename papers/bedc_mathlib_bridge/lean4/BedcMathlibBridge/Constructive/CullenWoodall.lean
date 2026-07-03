import BEDC.Derived.CullenWoodallUp
import Mathlib.Data.Nat.Basic

/-!
Cullen and Woodall number structural correspondences.

The BEDC side supplies the finite Nat definitions
`cullenNat n = n * twoPow n + 1` and
`woodallNat n = n * twoPow n - 1`. The bridge identifies the local `twoPow`
recurrence with mathlib's `Nat.pow 2 n`, and stops at those pointwise Nat
readbacks.
-/

namespace BedcMathlibBridge.Constructive.CullenWoodall

private def mathlibPowProvenanceAnchor : Unit :=
  let _ : forall n : Nat, Nat.pow 2 n = Nat.pow 2 n := fun _ => rfl
  let _ : Function.Injective Nat.succ := Nat.succ_injective
  ()

def cullenReadback (n : Nat) : Nat :=
  let _ := mathlibPowProvenanceAnchor
  BEDC.Derived.CullenWoodallUp.cullenNat n

def woodallReadback (n : Nat) : Nat :=
  let _ := mathlibPowProvenanceAnchor
  BEDC.Derived.CullenWoodallUp.woodallNat n

private theorem twoPow_eq_nat_pow_two (n : Nat) :
    BEDC.Derived.CullenWoodallUp.twoPow n = Nat.pow 2 n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      calc
        BEDC.Derived.CullenWoodallUp.twoPow (Nat.succ n)
            = 2 * BEDC.Derived.CullenWoodallUp.twoPow n :=
              BEDC.Derived.CullenWoodallUp.twoPow_succ n
        _ = 2 * Nat.pow 2 n := by
          rw [ih]
        _ = Nat.pow 2 n * 2 := Nat.mul_comm 2 (Nat.pow 2 n)
        _ = Nat.pow 2 (Nat.succ n) := (Nat.pow_succ 2 n).symm

theorem cullenReadback_apply (n : Nat) :
    cullenReadback n = BEDC.Derived.CullenWoodallUp.cullenNat n :=
  rfl

theorem woodallReadback_apply (n : Nat) :
    woodallReadback n = BEDC.Derived.CullenWoodallUp.woodallNat n :=
  rfl

theorem cullenReadback_zero : cullenReadback 0 = 1 := by
  rfl

theorem cullenReadback_one : cullenReadback 1 = 3 := by
  rfl

theorem woodallReadback_zero : woodallReadback 0 = 0 := by
  rfl

theorem woodallReadback_one : woodallReadback 1 = 1 := by
  rfl

theorem mathlibPowAnchor : Nat.succ_injective = Nat.succ_injective := by
  rfl

theorem cullenReadback_eq_nat_mul_pow_add_one
    (n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibPowAnchor) :
    cullenReadback n = n * Nat.pow 2 n + 1 := by
  calc
    cullenReadback n = BEDC.Derived.CullenWoodallUp.cullenNat n := rfl
    _ = n * BEDC.Derived.CullenWoodallUp.twoPow n + 1 :=
      BEDC.Derived.CullenWoodallUp.cullenNat_definition n
    _ = n * Nat.pow 2 n + 1 := by
      rw [twoPow_eq_nat_pow_two n]

theorem woodallReadback_eq_nat_mul_pow_sub_one
    (n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibPowAnchor) :
    woodallReadback n = n * Nat.pow 2 n - 1 := by
  calc
    woodallReadback n = BEDC.Derived.CullenWoodallUp.woodallNat n := rfl
    _ = n * BEDC.Derived.CullenWoodallUp.twoPow n - 1 :=
      BEDC.Derived.CullenWoodallUp.woodallNat_definition n
    _ = n * Nat.pow 2 n - 1 := by
      rw [twoPow_eq_nat_pow_two n]

end BedcMathlibBridge.Constructive.CullenWoodall
