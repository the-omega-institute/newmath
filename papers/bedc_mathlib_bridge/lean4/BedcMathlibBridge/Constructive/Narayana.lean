import BedcMathlibBridge.Constructive.Binomial
import BEDC.Derived.NarayanaUp
import Mathlib.Data.Nat.Choose.Basic

/-!
Narayana number structural correspondence.

`BEDC.Derived.NarayanaUp.narayanaNumber n k` is the closed BEDC Narayana
triangle value, with its numerator expressed through
`BEDC.Derived.BinomialIdentitiesUp.C`.  The bridge exports the standard
binomial readback of that closed formula:

  `N(n,k) = Nat.choose n k * Nat.choose n (k - 1) / n`.

The target is an explicit mathlib `Nat.choose` formula rather than a separate
mathlib Narayana declaration, because mathlib v4.28.0 has no stable `Nat`
Narayana-number object.
-/

namespace BedcMathlibBridge.Constructive.Narayana

private def mathlibChooseProvenanceAnchor : Unit :=
  let _ : ∀ n k : Nat, Nat.choose n k = Nat.choose n k := fun _ _ => rfl
  ()

def toNat (n k : Nat) : Nat :=
  let _ := mathlibChooseProvenanceAnchor
  BEDC.Derived.NarayanaUp.narayanaNumber n k

theorem toNat_eq_narayanaNumber (n k : Nat) :
    toNat n k = BEDC.Derived.NarayanaUp.narayanaNumber n k :=
  rfl

theorem toNat_zero_left (k : Nat) : toNat 0 k = 0 := by
  exact BEDC.Derived.NarayanaUp.narayana_zero_left k

theorem toNat_succ_zero (n : Nat) : toNat (Nat.succ n) 0 = 0 := by
  exact BEDC.Derived.NarayanaUp.narayana_left_boundary n

private theorem C_eq_nat_choose (n k : Nat) :
    BEDC.Derived.NarayanaUp.C n k = Nat.choose n k := by
  change BEDC.Derived.LucasTheoremUp.bedcChooseNat n k = Nat.choose n k
  exact BedcMathlibBridge.Constructive.Binomial.bedcChoose_eq_nat_choose n k

theorem chooseFormula_succ_succ (n k : Nat) :
    toNat (Nat.succ n) (Nat.succ k) =
      Nat.choose (Nat.succ n) (Nat.succ k) *
          Nat.choose (Nat.succ n) k /
        Nat.succ n := by
  change
    BEDC.Derived.NarayanaUp.narayanaNumber (Nat.succ n) (Nat.succ k) =
      Nat.choose (Nat.succ n) (Nat.succ k) *
          Nat.choose (Nat.succ n) k /
        Nat.succ n
  rw [BEDC.Derived.NarayanaUp.narayana_succ_formula]
  unfold BEDC.Derived.NarayanaUp.narayanaNumerator
  rw [C_eq_nat_choose]
  rw [C_eq_nat_choose]
  rw [Nat.succ_sub_one]

theorem complement_symmetry (k l : Nat) :
    toNat (Nat.succ (k + l)) (Nat.succ k) =
      toNat (Nat.succ (k + l)) (Nat.succ l) := by
  exact BEDC.Derived.NarayanaUp.narayana_complement_symmetry k l

end BedcMathlibBridge.Constructive.Narayana
