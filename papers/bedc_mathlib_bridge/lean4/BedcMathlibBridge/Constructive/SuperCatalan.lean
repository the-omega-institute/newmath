import BedcMathlibBridge.Constructive.Binomial
import BEDC.Derived.BinomialIdentitiesUp
import Mathlib.Data.Nat.Choose.Basic

/-!
Super-Catalan choose-formula readback.

The BEDC side uses the existing binomial counter `C`. The bridge exposes only
the three-counter quotient expression against mathlib `Nat.choose`.
-/

namespace BedcMathlibBridge.Constructive.SuperCatalan

private def mathlibChooseProvenanceAnchor : Unit :=
  let _ : forall n k : Nat, Nat.choose n k = Nat.choose n k := fun _ _ => rfl
  ()

private theorem C_eq_nat_choose (n k : Nat) :
    BEDC.Derived.BinomialIdentitiesUp.C n k = Nat.choose n k := by
  change BEDC.Derived.LucasTheoremUp.bedcChooseNat n k = Nat.choose n k
  exact BedcMathlibBridge.Constructive.Binomial.bedcChoose_eq_nat_choose n k

def superCatalan (m n : Nat) : Nat :=
  let _ := mathlibChooseProvenanceAnchor
  (BEDC.Derived.BinomialIdentitiesUp.C (m + m) m *
      BEDC.Derived.BinomialIdentitiesUp.C (n + n) n) /
    BEDC.Derived.BinomialIdentitiesUp.C (m + n) m

theorem superCatalan_eq_bedc_choose_formula (m n : Nat) :
    superCatalan m n =
      (BEDC.Derived.BinomialIdentitiesUp.C (m + m) m *
          BEDC.Derived.BinomialIdentitiesUp.C (n + n) n) /
        BEDC.Derived.BinomialIdentitiesUp.C (m + n) m := by
  rfl

theorem bedc_choose_formula_eq_nat_choose_formula (m n : Nat) :
    (BEDC.Derived.BinomialIdentitiesUp.C (m + m) m *
        BEDC.Derived.BinomialIdentitiesUp.C (n + n) n) /
      BEDC.Derived.BinomialIdentitiesUp.C (m + n) m =
    (Nat.choose (m + m) m * Nat.choose (n + n) n) /
      Nat.choose (m + n) m := by
  rw [C_eq_nat_choose (m + m) m, C_eq_nat_choose (n + n) n,
    C_eq_nat_choose (m + n) m]

theorem superCatalan_eq_nat_choose_formula (m n : Nat) :
    superCatalan m n =
      (Nat.choose (m + m) m * Nat.choose (n + n) n) /
        Nat.choose (m + n) m := by
  rw [superCatalan_eq_bedc_choose_formula]
  exact bedc_choose_formula_eq_nat_choose_formula m n

theorem superCatalan_zero_zero :
    superCatalan 0 0 = 1 := by
  rw [superCatalan_eq_nat_choose_formula]
  rfl

end BedcMathlibBridge.Constructive.SuperCatalan
