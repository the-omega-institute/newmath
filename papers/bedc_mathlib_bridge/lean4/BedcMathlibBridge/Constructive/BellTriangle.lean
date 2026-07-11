import BEDC.Derived.BellNumberUp
import BedcMathlibBridge.Constructive.Binomial
import Mathlib.Data.Nat.Choose.Basic

/-!
Bell recurrence triangle readback through `Nat.choose`.

The BEDC surface is `BellNumberUp.bellNumberByRecurrence` together with its
prefix recurrence. The bridge exposes only the binomial-coefficient recurrence
layer; the host `Nat.bell` object remains covered by the boundary row.
-/

namespace BedcMathlibBridge.Constructive.BellTriangle

private def mathlibChooseProvenanceAnchor : Unit :=
  let _ : forall n k : Nat, Nat.choose n k = Nat.choose n k := fun _ _ => rfl
  ()

def chooseReadback (n k : Nat) : Nat :=
  let _ := mathlibChooseProvenanceAnchor
  BEDC.Derived.BellNumberUp.natChooseCount n k

def recurrencePrefixReadback (B : Nat -> Nat) (n k : Nat) : Nat :=
  let _ := mathlibChooseProvenanceAnchor
  BEDC.Derived.BellNumberUp.bellRecurrencePrefix B n k

def recurrenceReadback (n : Nat) : Nat :=
  let _ := mathlibChooseProvenanceAnchor
  BEDC.Derived.BellNumberUp.bellNumberByRecurrence n

theorem chooseReadback_apply (n k : Nat) :
    chooseReadback n k = BEDC.Derived.BellNumberUp.natChooseCount n k := by
  rfl

theorem recurrencePrefixReadback_apply (B : Nat -> Nat) (n k : Nat) :
    recurrencePrefixReadback B n k =
      BEDC.Derived.BellNumberUp.bellRecurrencePrefix B n k := by
  rfl

theorem recurrenceReadback_apply (n : Nat) :
    recurrenceReadback n =
      BEDC.Derived.BellNumberUp.bellNumberByRecurrence n := by
  rfl

theorem natChooseCount_eq_nat_choose (n k : Nat) :
    BEDC.Derived.BellNumberUp.natChooseCount n k = Nat.choose n k := by
  change BEDC.Derived.LucasTheoremUp.bedcChooseNat n k = Nat.choose n k
  exact BedcMathlibBridge.Constructive.Binomial.bedcChoose_eq_nat_choose n k

theorem chooseReadback_eq_nat_choose (n k : Nat) :
    chooseReadback n k = Nat.choose n k := by
  rw [chooseReadback_apply, natChooseCount_eq_nat_choose]

theorem recurrencePrefixReadback_zero_nat_choose (B : Nat -> Nat) (n : Nat) :
    recurrencePrefixReadback B n 0 = Nat.choose n 0 * B 0 := by
  unfold recurrencePrefixReadback
  rw [BEDC.Derived.BellNumberUp.bellRecurrencePrefix_zero]
  rw [natChooseCount_eq_nat_choose]

theorem recurrencePrefixReadback_succ_nat_choose
    (B : Nat -> Nat) (n k : Nat) :
    recurrencePrefixReadback B n (Nat.succ k) =
      recurrencePrefixReadback B n k + Nat.choose n (Nat.succ k) * B (Nat.succ k) := by
  unfold recurrencePrefixReadback
  rw [BEDC.Derived.BellNumberUp.bellRecurrencePrefix_succ]
  rw [natChooseCount_eq_nat_choose]

theorem recurrenceReadback_succ (n : Nat) :
    recurrenceReadback (Nat.succ n) =
      recurrencePrefixReadback recurrenceReadback n n := by
  unfold recurrenceReadback recurrencePrefixReadback
  exact BEDC.Derived.BellNumberUp.bellNumberByRecurrence_standard_recurrence n

theorem bellNumberByRecurrence_mathlib_choose_recurrence_readback (n : Nat) :
    recurrenceReadback (Nat.succ n) =
        recurrencePrefixReadback recurrenceReadback n n ∧
      (forall k : Nat,
        recurrencePrefixReadback recurrenceReadback n (Nat.succ k) =
          recurrencePrefixReadback recurrenceReadback n k +
            Nat.choose n (Nat.succ k) * recurrenceReadback (Nat.succ k)) := by
  constructor
  · exact recurrenceReadback_succ n
  · intro k
    exact recurrencePrefixReadback_succ_nat_choose recurrenceReadback n k

end BedcMathlibBridge.Constructive.BellTriangle
