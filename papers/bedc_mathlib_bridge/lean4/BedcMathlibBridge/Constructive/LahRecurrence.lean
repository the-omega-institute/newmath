import BEDC.Derived.LahNumberUp
import Mathlib.Data.Nat.Basic

/-!
Lah table recurrence readback.

The BEDC side is the closed `Nat` Lah table and row-prefix surface in
`BEDC.Derived.LahNumberUp`. The bridge exposes only the recurrence and row
ledger through host `Nat.add` and `Nat.mul`.
-/

namespace BedcMathlibBridge.Constructive.LahRecurrence

private def mathlibNatArithmeticAnchor : Unit :=
  let _ : Function.Injective Nat.succ := Nat.succ_injective
  let _ : forall a b : Nat, a + b = Nat.add a b := fun _ _ => rfl
  let _ : forall a b : Nat, a * b = Nat.mul a b := fun _ _ => rfl
  ()

def tableReadback (n k : Nat) : Nat :=
  let _ := mathlibNatArithmeticAnchor
  BEDC.Derived.LahNumberUp.lahNumber n k

def rowPrefixReadback (n k : Nat) : Nat :=
  let _ := mathlibNatArithmeticAnchor
  BEDC.Derived.LahNumberUp.lahRowPrefix n k

def rowSumReadback (n : Nat) : Nat :=
  let _ := mathlibNatArithmeticAnchor
  BEDC.Derived.LahNumberUp.lahRowSum n

theorem tableReadback_apply (n k : Nat) :
    tableReadback n k = BEDC.Derived.LahNumberUp.lahNumber n k := by
  rfl

theorem rowPrefixReadback_apply (n k : Nat) :
    rowPrefixReadback n k = BEDC.Derived.LahNumberUp.lahRowPrefix n k := by
  rfl

theorem rowSumReadback_apply (n : Nat) :
    rowSumReadback n = BEDC.Derived.LahNumberUp.lahRowSum n := by
  rfl

theorem table_zero_zero :
    tableReadback 0 0 = 1 := by
  rfl

theorem table_zero_succ (k : Nat) :
    tableReadback 0 (Nat.succ k) = 0 := by
  rfl

theorem table_succ_zero (n : Nat) :
    tableReadback (Nat.succ n) 0 = 0 := by
  rfl

theorem mathlibNatAnchor :
    Nat.succ_injective = Nat.succ_injective := by
  rfl

theorem table_recurrence_nat_add_mul
    (n k : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    tableReadback (Nat.succ n) (Nat.succ k) =
      Nat.add
        (Nat.mul (Nat.add n (Nat.succ k))
          (tableReadback n (Nat.succ k)))
        (tableReadback n k) := by
  change
    BEDC.Derived.LahNumberUp.lahNumber (Nat.succ n) (Nat.succ k) =
      (n + Nat.succ k) *
        BEDC.Derived.LahNumberUp.lahNumber n (Nat.succ k) +
          BEDC.Derived.LahNumberUp.lahNumber n k
  exact BEDC.Derived.LahNumberUp.lahNumber_recurrence n k

theorem table_self (n : Nat) :
    tableReadback n n = 1 := by
  exact BEDC.Derived.LahNumberUp.lahNumber_self n

theorem table_above (n extra : Nat) :
    tableReadback n (Nat.succ (n + extra)) = 0 := by
  exact BEDC.Derived.LahNumberUp.lahNumber_above n extra

theorem rowPrefix_succ_nat_add (n k : Nat) :
    rowPrefixReadback n (Nat.succ k) =
      Nat.add (rowPrefixReadback n k)
        (tableReadback n (Nat.succ k)) := by
  rfl

theorem rowSum_definition (n : Nat) :
    rowSumReadback n = rowPrefixReadback n n := by
  rfl

theorem rowPrefix_above_self (n extra : Nat) :
    rowPrefixReadback n (n + extra) = rowSumReadback n := by
  exact BEDC.Derived.LahNumberUp.lahRowPrefix_above_self n extra

theorem rowPrefix_succ_row_recurrence_nat_add_mul
    (n k : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    rowPrefixReadback (Nat.succ n) (Nat.succ k) =
      Nat.add
        (rowPrefixReadback (Nat.succ n) k)
        (Nat.add
          (Nat.mul (Nat.add n (Nat.succ k))
            (tableReadback n (Nat.succ k)))
          (tableReadback n k)) := by
  change
    BEDC.Derived.LahNumberUp.lahRowPrefix (Nat.succ n) (Nat.succ k) =
      BEDC.Derived.LahNumberUp.lahRowPrefix (Nat.succ n) k +
        ((n + Nat.succ k) *
          BEDC.Derived.LahNumberUp.lahNumber n (Nat.succ k) +
            BEDC.Derived.LahNumberUp.lahNumber n k)
  exact BEDC.Derived.LahNumberUp.lahRowPrefix_succ_row_recurrence n k

theorem rowSum_small_values :
    rowSumReadback 0 = 1 ∧ rowSumReadback 1 = 1 ∧
      rowSumReadback 2 = 3 ∧ rowSumReadback 3 = 13 := by
  exact ⟨BEDC.Derived.LahNumberUp.lahRowSum_zero,
    BEDC.Derived.LahNumberUp.lahRowSum_one,
    BEDC.Derived.LahNumberUp.lahRowSum_two,
    BEDC.Derived.LahNumberUp.lahRowSum_three⟩

theorem lahNumber_table_recurrence_nat_add_mul
    (n k : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    BEDC.Derived.LahNumberUp.lahNumber (Nat.succ n) (Nat.succ k) =
      Nat.add
        (Nat.mul (Nat.add n (Nat.succ k))
          (BEDC.Derived.LahNumberUp.lahNumber n (Nat.succ k)))
        (BEDC.Derived.LahNumberUp.lahNumber n k) := by
  exact BEDC.Derived.LahNumberUp.lahNumber_recurrence n k

end BedcMathlibBridge.Constructive.LahRecurrence
