import BedcMathlibBridge.Constructive.BellPolynomialSecond

namespace BedcMathlibBridge.Export.BellPolynomialSecond

open BedcMathlibBridge.Constructive.BellPolynomialSecond

structure BellPolynomialSecondExportWitness where
  readback : Nat -> Nat -> Nat -> Nat
  readback_apply :
    forall n x k : Nat, readback n x k = prefixToNat n x k
  bedc_apply :
    forall n x k : Nat,
      readback n x k = BEDC.Derived.BellPolynomialSecondUp.phiPrefix n x k
  zero_apply :
    forall n x : Nat,
      readback n x 0 =
        BEDC.Derived.BellPolynomialSecondUp.stirlingSecond n 0 *
          BEDC.Derived.BellPolynomialSecondUp.natPow x 0
  bedc_succ_apply :
    forall n x k : Nat,
      readback n x (Nat.succ k) =
        readback n x k +
          BEDC.Derived.BellPolynomialSecondUp.stirlingSecond n (Nat.succ k) *
            BEDC.Derived.BellPolynomialSecondUp.natPow x (Nat.succ k)
  nat_stirlingSecond_increment_apply :
    forall n x k : Nat,
      readback n x (Nat.succ k) =
        readback n x k +
          Nat.stirlingSecond n (Nat.succ k) *
            BEDC.Derived.BellPolynomialSecondUp.natPow x (Nat.succ k)
  nat_stirlingSecond_succ_row_increment_apply :
    forall n x k : Nat,
      readback (Nat.succ n) x (Nat.succ k) =
        readback (Nat.succ n) x k +
          (Nat.succ k * Nat.stirlingSecond n (Nat.succ k) + Nat.stirlingSecond n k) *
            BEDC.Derived.BellPolynomialSecondUp.natPow x (Nat.succ k)

def bellPolynomialSecondExport : BellPolynomialSecondExportWitness where
  readback := prefixToNat
  readback_apply := by
    intro n x k
    rfl
  bedc_apply := prefixToNat_apply
  zero_apply := prefixToNat_zero
  bedc_succ_apply := prefixToNat_succ_bedc
  nat_stirlingSecond_increment_apply := prefixToNat_increment_eq_nat_stirlingSecond
  nat_stirlingSecond_succ_row_increment_apply :=
    prefixToNat_succ_row_increment_matches_nat_stirlingSecond

theorem phiPrefix_increment_eq_nat_stirlingSecond (n x k : Nat) :
    BEDC.Derived.BellPolynomialSecondUp.phiPrefix n x (Nat.succ k) =
      BEDC.Derived.BellPolynomialSecondUp.phiPrefix n x k +
        Nat.stirlingSecond n (Nat.succ k) *
          BEDC.Derived.BellPolynomialSecondUp.natPow x (Nat.succ k) := by
  change
    BedcMathlibBridge.Constructive.BellPolynomialSecond.prefixToNat n x (Nat.succ k) =
      BedcMathlibBridge.Constructive.BellPolynomialSecond.prefixToNat n x k +
        Nat.stirlingSecond n (Nat.succ k) *
          BEDC.Derived.BellPolynomialSecondUp.natPow x (Nat.succ k)
  exact
    BedcMathlibBridge.Constructive.BellPolynomialSecond.prefixToNat_increment_eq_nat_stirlingSecond
      n x k

theorem phiPrefix_succ_row_increment_matches_nat_stirlingSecond (n x k : Nat) :
    BEDC.Derived.BellPolynomialSecondUp.phiPrefix (Nat.succ n) x (Nat.succ k) =
      BEDC.Derived.BellPolynomialSecondUp.phiPrefix (Nat.succ n) x k +
        (Nat.succ k * Nat.stirlingSecond n (Nat.succ k) + Nat.stirlingSecond n k) *
          BEDC.Derived.BellPolynomialSecondUp.natPow x (Nat.succ k) := by
  change
    BedcMathlibBridge.Constructive.BellPolynomialSecond.prefixToNat
        (Nat.succ n) x (Nat.succ k) =
      BedcMathlibBridge.Constructive.BellPolynomialSecond.prefixToNat
        (Nat.succ n) x k +
        (Nat.succ k * Nat.stirlingSecond n (Nat.succ k) + Nat.stirlingSecond n k) *
          BEDC.Derived.BellPolynomialSecondUp.natPow x (Nat.succ k)
  exact
    prefixToNat_succ_row_increment_matches_nat_stirlingSecond n x k

end BedcMathlibBridge.Export.BellPolynomialSecond
