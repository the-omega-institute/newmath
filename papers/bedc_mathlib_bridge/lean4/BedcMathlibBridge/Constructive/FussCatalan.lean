import BedcMathlibBridge.Constructive.BinomialIdentities
import BEDC.Derived.FussCatalanUp
import Mathlib.Data.Nat.Choose.Central

namespace BedcMathlibBridge.Constructive.FussCatalan

private def mathlibChooseProvenanceAnchor : Unit :=
  let _ : ∀ n k : Nat, Nat.choose n k = Nat.choose n k := fun _ _ => rfl
  let _ : ∀ n : Nat, Nat.centralBinom n = Nat.centralBinom n := fun _ => rfl
  ()

def toNat (m n : Nat) : Nat :=
  let _ := mathlibChooseProvenanceAnchor
  BEDC.Derived.FussCatalanUp.fussCatalanCount m n

theorem toNat_apply (m n : Nat) :
    toNat m n = BEDC.Derived.FussCatalanUp.fussCatalanCount m n :=
  rfl

theorem numerator_eq_nat_choose (m n : Nat) :
    BEDC.Derived.FussCatalanUp.fussCatalanNumerator m n =
      Nat.choose (m * n) n := by
  unfold BEDC.Derived.FussCatalanUp.fussCatalanNumerator
  change BEDC.Derived.BinomialIdentitiesUp.C (m * n) n = Nat.choose (m * n) n
  exact BedcMathlibBridge.Constructive.BinomialIdentities.toNat_eq_nat_choose (m * n) n

theorem toNat_eq_nat_choose_div (m n : Nat) :
    toNat m n = Nat.choose (m * n) n / ((m - 1) * n + 1) := by
  unfold toNat BEDC.Derived.FussCatalanUp.fussCatalanCount
  unfold BEDC.Derived.FussCatalanUp.fussCatalanDenom
  rw [numerator_eq_nat_choose]

theorem toNat_eq_nat_choose_formula (m n : Nat) :
    toNat m n = Nat.choose (m * n) n / ((m - 1) * n + 1) :=
  toNat_eq_nat_choose_div m n

theorem toNat_binary_eq_centralBinom_div (n : Nat) :
    toNat 2 n = Nat.centralBinom n / (n + 1) := by
  calc
    toNat 2 n = Nat.choose (2 * n) n / ((2 - 1) * n + 1) :=
      toNat_eq_nat_choose_formula 2 n
    _ = Nat.centralBinom n / (n + 1) := by
      rw [Nat.centralBinom_eq_two_mul_choose]
      change Nat.choose (2 * n) n / (1 * n + 1) = Nat.choose (2 * n) n / (n + 1)
      rw [Nat.one_mul]

end BedcMathlibBridge.Constructive.FussCatalan
