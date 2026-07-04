import BedcMathlibBridge.Constructive.Binomial
import BEDC.Derived.StirlingSecondCompleteUp
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic

/-!
Associated Stirling power-term readback.

The BEDC side already carries the signed explicit power balance for the
second-kind Stirling table. This bridge exports only the factor readback that
rewrites BEDC factorial, binomial, and power-term factors to mathlib
`Nat.factorial`, `Nat.choose`, and `Nat.pow`.
-/

namespace BedcMathlibBridge.Constructive.AssociatedStirling

private def mathlibChooseFactorialPowProvenanceAnchor : Unit :=
  let _ : forall n k : Nat, Nat.choose n k = Nat.choose n k := fun _ _ => rfl
  let _ : forall n : Nat, Nat.factorial n = Nat.factorial n := fun _ => rfl
  let _ : forall n k : Nat, n ^ k = n ^ k := fun _ _ => rfl
  ()

def factorialReadback (k : Nat) : Nat :=
  let _ := mathlibChooseFactorialPowProvenanceAnchor
  BEDC.Derived.StirlingSecondCompleteUp.factorialCount k

def chooseReadback (k j : Nat) : Nat :=
  let _ := mathlibChooseFactorialPowProvenanceAnchor
  BEDC.Derived.StirlingSecondCompleteUp.C k j

def powerTermReadback (n k j : Nat) : Nat :=
  let _ := mathlibChooseFactorialPowProvenanceAnchor
  BEDC.Derived.StirlingSecondCompleteUp.explicitPowerTerm n k j

def mathlibPowerTerm (n k j : Nat) : Nat :=
  Nat.choose k j * (k - j) ^ n

theorem factorialReadback_apply (k : Nat) :
    factorialReadback k =
      BEDC.Derived.StirlingSecondCompleteUp.factorialCount k := by
  rfl

theorem chooseReadback_apply (k j : Nat) :
    chooseReadback k j = BEDC.Derived.StirlingSecondCompleteUp.C k j := by
  rfl

theorem powerTermReadback_apply (n k j : Nat) :
    powerTermReadback n k j =
      BEDC.Derived.StirlingSecondCompleteUp.explicitPowerTerm n k j := by
  rfl

theorem factorialCount_eq_nat_factorial (k : Nat) :
    BEDC.Derived.StirlingSecondCompleteUp.factorialCount k = Nat.factorial k := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      calc
        BEDC.Derived.StirlingSecondCompleteUp.factorialCount (Nat.succ k) =
            BEDC.Derived.StirlingSecondCompleteUp.factorialCount k * Nat.succ k := by
          exact BEDC.Derived.PochhammerUp.natFactorialCount_succ k
        _ = Nat.factorial k * Nat.succ k := by
          rw [ih]
        _ = Nat.succ k * Nat.factorial k := by
          exact Nat.mul_comm (Nat.factorial k) (Nat.succ k)
        _ = Nat.factorial (Nat.succ k) := by
          exact (Nat.factorial_succ k).symm

private theorem C_eq_nat_choose (k j : Nat) :
    BEDC.Derived.StirlingSecondCompleteUp.C k j = Nat.choose k j := by
  change BEDC.Derived.BinomialIdentitiesUp.C k j = Nat.choose k j
  change BEDC.Derived.LucasTheoremUp.bedcChooseNat k j = Nat.choose k j
  exact BedcMathlibBridge.Constructive.Binomial.bedcChoose_eq_nat_choose k j

theorem factorialReadback_eq_nat_factorial (k : Nat) :
    factorialReadback k = Nat.factorial k := by
  rw [factorialReadback_apply]
  exact factorialCount_eq_nat_factorial k

theorem chooseReadback_eq_nat_choose (k j : Nat) :
    chooseReadback k j = Nat.choose k j := by
  rw [chooseReadback_apply]
  exact C_eq_nat_choose k j

theorem powerTermReadback_eq_mathlib (n k j : Nat) :
    powerTermReadback n k j = mathlibPowerTerm n k j := by
  unfold powerTermReadback mathlibPowerTerm
  unfold BEDC.Derived.StirlingSecondCompleteUp.explicitPowerTerm
  rw [C_eq_nat_choose k j]

end BedcMathlibBridge.Constructive.AssociatedStirling
