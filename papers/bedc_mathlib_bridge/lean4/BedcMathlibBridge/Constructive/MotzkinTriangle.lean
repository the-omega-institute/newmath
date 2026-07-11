import BEDC.Derived.MotzkinTriangleUp
import Mathlib.Data.Nat.Basic

/-!
Motzkin triangle recurrence readback correspondence.

The BEDC object is the closed `Nat` table
`BEDC.Derived.MotzkinTriangleUp.motzkinTriangle`. The bridge records the
zero-column, row-sum, and three-term triangle recurrence through host `Nat.add`.
-/

namespace BedcMathlibBridge.Constructive.MotzkinTriangle

private def mathlibNatProvenanceAnchor : Unit :=
  let _ : Function.Injective Nat.succ := Nat.succ_injective
  let _ : forall a b : Nat, a + b = Nat.add a b := fun _ _ => rfl
  ()

def readback (n k : Nat) : Nat :=
  let _ := mathlibNatProvenanceAnchor
  BEDC.Derived.MotzkinTriangleUp.motzkinTriangle n k

def numberReadback (n : Nat) : Nat :=
  let _ := mathlibNatProvenanceAnchor
  BEDC.Derived.MotzkinTriangleUp.motzkinNumber n

def rowSumReadback (n : Nat) : Nat :=
  let _ := mathlibNatProvenanceAnchor
  BEDC.Derived.MotzkinTriangleUp.motzkinTriangleRowSum n

theorem readback_apply (n k : Nat) :
    readback n k = BEDC.Derived.MotzkinTriangleUp.motzkinTriangle n k := by
  rfl

theorem numberReadback_apply (n : Nat) :
    numberReadback n = BEDC.Derived.MotzkinTriangleUp.motzkinNumber n := by
  rfl

theorem rowSumReadback_apply (n : Nat) :
    rowSumReadback n =
      BEDC.Derived.MotzkinTriangleUp.motzkinTriangleRowSum n := by
  rfl

theorem readback_zero_zero :
    readback 0 0 = 1 := by
  rfl

theorem readback_zero_succ (k : Nat) :
    readback 0 (Nat.succ k) = 0 := by
  rfl

theorem mathlibNatAnchor :
    Nat.succ_injective = Nat.succ_injective := by
  rfl

theorem readback_zero_step_nat_add
    (n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    readback (Nat.succ n) 0 =
      Nat.add (readback n 0) (readback n 1) := by
  change
    BEDC.Derived.MotzkinTriangleUp.motzkinTriangle (Nat.succ n) 0 =
      Nat.add
        (BEDC.Derived.MotzkinTriangleUp.motzkinTriangle n 0)
        (BEDC.Derived.MotzkinTriangleUp.motzkinTriangle n 1)
  exact BEDC.Derived.MotzkinTriangleUp.motzkinTriangle_zero_step n

theorem readback_recurrence_nat_add
    (n k : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    readback (Nat.succ n) (Nat.succ k) =
      Nat.add
        (Nat.add (readback n k) (readback n (Nat.succ k)))
        (readback n (Nat.succ (Nat.succ k))) := by
  change
    BEDC.Derived.MotzkinTriangleUp.motzkinTriangle (Nat.succ n) (Nat.succ k) =
      Nat.add
        (Nat.add
          (BEDC.Derived.MotzkinTriangleUp.motzkinTriangle n k)
          (BEDC.Derived.MotzkinTriangleUp.motzkinTriangle n (Nat.succ k)))
        (BEDC.Derived.MotzkinTriangleUp.motzkinTriangle n
          (Nat.succ (Nat.succ k)))
  exact BEDC.Derived.MotzkinTriangleUp.motzkinTriangle_recurrence n k

theorem readback_zero_eq_number (n : Nat) :
    readback n 0 = numberReadback n := by
  change
    BEDC.Derived.MotzkinTriangleUp.motzkinTriangle n 0 =
      BEDC.Derived.MotzkinTriangleUp.motzkinNumber n
  exact BEDC.Derived.MotzkinTriangleUp.motzkinTriangle_zero_eq_motzkinNumber n

theorem rowSumReadback_prefix (n : Nat) :
    rowSumReadback n =
      BEDC.Derived.MotzkinTriangleUp.motzkinTrianglePrefix n n := by
  change
    BEDC.Derived.MotzkinTriangleUp.motzkinTriangleRowSum n =
      BEDC.Derived.MotzkinTriangleUp.motzkinTrianglePrefix n n
  exact BEDC.Derived.MotzkinTriangleUp.motzkinTriangleRowSum_prefix n

theorem numberReadback_small_zero_column :
    numberReadback 0 = 1 ∧ numberReadback 1 = 1 ∧
      numberReadback 2 = 2 ∧ numberReadback 3 = 4 ∧
        numberReadback 4 = 9 ∧ numberReadback 5 = 21 := by
  exact BEDC.Derived.MotzkinTriangleUp.motzkinTriangle_small_zero_column

theorem rowSumReadback_small_values :
    rowSumReadback 0 = 1 ∧ rowSumReadback 1 = 2 ∧
      rowSumReadback 2 = 5 ∧ rowSumReadback 3 = 13 := by
  exact ⟨
    BEDC.Derived.MotzkinTriangleUp.motzkinTriangleRowSum_zero,
    BEDC.Derived.MotzkinTriangleUp.motzkinTriangleRowSum_one,
    BEDC.Derived.MotzkinTriangleUp.motzkinTriangleRowSum_two,
    BEDC.Derived.MotzkinTriangleUp.motzkinTriangleRowSum_three⟩

end BedcMathlibBridge.Constructive.MotzkinTriangle
