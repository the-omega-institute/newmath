import BedcMathlibBridge.Constructive.Binomial
import BEDC.Derived.BinomialIdentitiesUp
import Mathlib.Data.Nat.Choose.Basic

/-!
Binomial identities structural correspondence.

`BEDC.Derived.BinomialIdentitiesUp.C` is the Pascal-recursive binomial count used
by the finite row, hockey-stick, and Vandermonde identities in the BEDC carrier.
The bridge exports the closed count itself to mathlib's `Nat.choose` and records
that the BEDC Pascal step is the same recurrence as `Nat.choose_succ_succ`.
-/

namespace BedcMathlibBridge.Constructive.BinomialIdentities

private def mathlibChooseProvenanceAnchor : Unit :=
  let _ : ∀ n k : Nat, Nat.choose n k = Nat.choose n k := fun _ _ => rfl
  ()

/-- Direct `Nat` readback of the BEDC binomial-identity count. -/
def toNat (n k : Nat) : Nat :=
  let _ := mathlibChooseProvenanceAnchor
  BEDC.Derived.BinomialIdentitiesUp.C n k

theorem toNat_apply (n k : Nat) :
    toNat n k = BEDC.Derived.BinomialIdentitiesUp.C n k :=
  rfl

/-- The carrier-local BEDC count is definitionally the same unary-factorial
readback already bridged to `Nat.choose`. -/
theorem toNat_eq_nat_choose (n k : Nat) :
    toNat n k = Nat.choose n k := by
  change BEDC.Derived.LucasTheoremUp.bedcChooseNat n k = Nat.choose n k
  exact BedcMathlibBridge.Constructive.Binomial.bedcChoose_eq_nat_choose n k

/-- BEDC's Pascal recurrence, read through the carrier-local count. -/
theorem toNat_pascal_bedc (n k : Nat) :
    toNat (Nat.succ n) (Nat.succ k) = toNat n k + toNat n (Nat.succ k) := by
  change
    BEDC.Derived.BinomialIdentitiesUp.C (Nat.succ n) (Nat.succ k) =
      BEDC.Derived.BinomialIdentitiesUp.C n k +
        BEDC.Derived.BinomialIdentitiesUp.C n (Nat.succ k)
  exact BEDC.Derived.BinomialIdentitiesUp.binomial_pascal n k

/-- The same Pascal step after transporting the BEDC count to mathlib's
`Nat.choose`. The final step is mathlib's pre-existing `Nat.choose_succ_succ`. -/
theorem toNat_pascal_mathlib (n k : Nat) :
    toNat (Nat.succ n) (Nat.succ k) = Nat.choose n k + Nat.choose n (Nat.succ k) := by
  calc
    toNat (Nat.succ n) (Nat.succ k) = Nat.choose (Nat.succ n) (Nat.succ k) :=
      toNat_eq_nat_choose (Nat.succ n) (Nat.succ k)
    _ = Nat.choose n k + Nat.choose n (Nat.succ k) :=
      Nat.choose_succ_succ n k

end BedcMathlibBridge.Constructive.BinomialIdentities
