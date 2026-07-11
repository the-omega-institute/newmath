import BedcMathlibBridge.Constructive.Binomial
import BEDC.Derived.LobbUp
import Mathlib.Data.Nat.Choose.Basic

/-!
Lobb number structural correspondence.

`BEDC.Derived.LobbUp.lobbNat m n` is the difference of two BEDC binomial
counts in row `2n`, at columns `n + m` and `n + m + 1`.  The bridge transports
only those two counters to mathlib's `Nat.choose`.
-/

namespace BedcMathlibBridge.Constructive.Lobb

private def mathlibChooseProvenanceAnchor : Unit :=
  let _ : forall n k : Nat, Nat.choose n k = Nat.choose n k := fun _ _ => rfl
  ()

private theorem C_eq_nat_choose (n k : Nat) :
    BEDC.Derived.LobbUp.C n k = Nat.choose n k := by
  change BEDC.Derived.LucasTheoremUp.bedcChooseNat n k = Nat.choose n k
  exact BedcMathlibBridge.Constructive.Binomial.bedcChoose_eq_nat_choose n k

/-- Direct `Nat` readback of the BEDC Lobb number. -/
def toNat (m n : Nat) : Nat :=
  let _ := mathlibChooseProvenanceAnchor
  BEDC.Derived.LobbUp.lobbNat m n

theorem toNat_apply (m n : Nat) :
    toNat m n = BEDC.Derived.LobbUp.lobbNat m n := by
  rfl

/-- The left edge of the Lobb triangle is the BEDC Catalan readback. -/
theorem toNat_zero_left (n : Nat) :
    toNat 0 n = BEDC.Derived.LobbUp.catalanNat n := by
  change BEDC.Derived.LobbUp.lobbNat 0 n = BEDC.Derived.LobbUp.catalanNat n
  exact BEDC.Derived.LobbUp.lobbNat_zero_left n

/-- The main structural correspondence with mathlib's `Nat.choose`. -/
theorem toNat_eq_nat_choose_diff (m n : Nat) :
    toNat m n =
      Nat.choose (n + n) (n + m) - Nat.choose (n + n) (Nat.succ (n + m)) := by
  calc
    toNat m n = BEDC.Derived.LobbUp.lobbNat m n := rfl
    _ =
        BEDC.Derived.LobbUp.C (BEDC.Derived.LobbUp.lobbTop n)
            (BEDC.Derived.LobbUp.lobbLowerIndex m n) -
          BEDC.Derived.LobbUp.C (BEDC.Derived.LobbUp.lobbTop n)
            (BEDC.Derived.LobbUp.lobbUpperIndex m n) := by
      rfl
    _ =
        Nat.choose (BEDC.Derived.LobbUp.lobbTop n)
            (BEDC.Derived.LobbUp.lobbLowerIndex m n) -
          Nat.choose (BEDC.Derived.LobbUp.lobbTop n)
            (BEDC.Derived.LobbUp.lobbUpperIndex m n) := by
      rw [
        C_eq_nat_choose (BEDC.Derived.LobbUp.lobbTop n)
          (BEDC.Derived.LobbUp.lobbLowerIndex m n),
        C_eq_nat_choose (BEDC.Derived.LobbUp.lobbTop n)
          (BEDC.Derived.LobbUp.lobbUpperIndex m n)]
    _ =
        Nat.choose (n + n) (n + m) - Nat.choose (n + n) (Nat.succ (n + m)) := by
      rfl

end BedcMathlibBridge.Constructive.Lobb
