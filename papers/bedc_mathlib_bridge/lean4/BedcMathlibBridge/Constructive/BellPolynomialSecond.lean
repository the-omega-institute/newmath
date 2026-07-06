import BEDC.Derived.BellPolynomialSecondUp
import BedcMathlibBridge.Constructive.StirlingSecond
import Mathlib.Combinatorics.Enumerative.Stirling

namespace BedcMathlibBridge.Constructive.BellPolynomialSecond

private def mathlibStirlingSecondProvenanceAnchor : Unit :=
  let _ : forall n k : Nat, Nat.stirlingSecond n k = Nat.stirlingSecond n k :=
    fun _ _ => rfl
  ()

def prefixToNat (n x k : Nat) : Nat :=
  let _ := mathlibStirlingSecondProvenanceAnchor
  BEDC.Derived.BellPolynomialSecondUp.phiPrefix n x k

theorem prefixToNat_apply (n x k : Nat) :
    prefixToNat n x k = BEDC.Derived.BellPolynomialSecondUp.phiPrefix n x k := by
  rfl

theorem prefixToNat_zero (n x : Nat) :
    prefixToNat n x 0 =
      BEDC.Derived.BellPolynomialSecondUp.stirlingSecond n 0 *
        BEDC.Derived.BellPolynomialSecondUp.natPow x 0 := by
  change
    BEDC.Derived.BellPolynomialSecondUp.phiPrefix n x 0 =
      BEDC.Derived.BellPolynomialSecondUp.stirlingSecond n 0 *
        BEDC.Derived.BellPolynomialSecondUp.natPow x 0
  exact BEDC.Derived.BellPolynomialSecondUp.phiPrefix_zero n x

theorem prefixToNat_succ_bedc (n x k : Nat) :
    prefixToNat n x (Nat.succ k) =
      prefixToNat n x k +
        BEDC.Derived.BellPolynomialSecondUp.stirlingSecond n (Nat.succ k) *
          BEDC.Derived.BellPolynomialSecondUp.natPow x (Nat.succ k) := by
  change
    BEDC.Derived.BellPolynomialSecondUp.phiPrefix n x (Nat.succ k) =
      BEDC.Derived.BellPolynomialSecondUp.phiPrefix n x k +
        BEDC.Derived.BellPolynomialSecondUp.stirlingSecond n (Nat.succ k) *
          BEDC.Derived.BellPolynomialSecondUp.natPow x (Nat.succ k)
  exact BEDC.Derived.BellPolynomialSecondUp.phiPrefix_succ n x k

theorem prefixToNat_increment_eq_nat_stirlingSecond (n x k : Nat) :
    prefixToNat n x (Nat.succ k) =
      prefixToNat n x k +
        Nat.stirlingSecond n (Nat.succ k) *
          BEDC.Derived.BellPolynomialSecondUp.natPow x (Nat.succ k) := by
  calc
    prefixToNat n x (Nat.succ k) =
        prefixToNat n x k +
          BEDC.Derived.BellPolynomialSecondUp.stirlingSecond n (Nat.succ k) *
            BEDC.Derived.BellPolynomialSecondUp.natPow x (Nat.succ k) :=
      prefixToNat_succ_bedc n x k
    _ =
        prefixToNat n x k +
          Nat.stirlingSecond n (Nat.succ k) *
            BEDC.Derived.BellPolynomialSecondUp.natPow x (Nat.succ k) := by
      have h :
          BEDC.Derived.BellPolynomialSecondUp.stirlingSecond n (Nat.succ k) =
            Nat.stirlingSecond n (Nat.succ k) := by
        change
          BEDC.Derived.StirlingUp.stirlingSecond n (Nat.succ k) =
            Nat.stirlingSecond n (Nat.succ k)
        exact
          BedcMathlibBridge.Constructive.StirlingSecond.toNat_eq_nat_stirlingSecond
            n (Nat.succ k)
      rw [h]

theorem prefixToNat_succ_row_increment_matches_nat_stirlingSecond (n x k : Nat) :
    prefixToNat (Nat.succ n) x (Nat.succ k) =
      prefixToNat (Nat.succ n) x k +
        (Nat.succ k * Nat.stirlingSecond n (Nat.succ k) + Nat.stirlingSecond n k) *
          BEDC.Derived.BellPolynomialSecondUp.natPow x (Nat.succ k) := by
  calc
    prefixToNat (Nat.succ n) x (Nat.succ k) =
        prefixToNat (Nat.succ n) x k +
          Nat.stirlingSecond (Nat.succ n) (Nat.succ k) *
            BEDC.Derived.BellPolynomialSecondUp.natPow x (Nat.succ k) :=
      prefixToNat_increment_eq_nat_stirlingSecond (Nat.succ n) x k
    _ =
        prefixToNat (Nat.succ n) x k +
          (Nat.succ k * Nat.stirlingSecond n (Nat.succ k) + Nat.stirlingSecond n k) *
            BEDC.Derived.BellPolynomialSecondUp.natPow x (Nat.succ k) := by
      rw [Nat.stirlingSecond_succ_succ n k]

end BedcMathlibBridge.Constructive.BellPolynomialSecond
