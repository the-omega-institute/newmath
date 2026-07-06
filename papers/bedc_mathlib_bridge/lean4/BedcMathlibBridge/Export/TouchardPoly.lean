import BedcMathlibBridge.Constructive.TouchardPoly

namespace BedcMathlibBridge.Export.TouchardPoly

open BedcMathlibBridge.Constructive.TouchardPoly

structure TouchardCoeffExportWitness where
  readback : Nat -> Nat -> Nat
  readback_apply : ∀ n k : Nat, readback n k = coeffToNat n k
  bedc_apply : ∀ n k : Nat, readback n k = BEDC.Derived.TouchardPolyUp.touchardCoeff n k
  bedc_stirlingSecond_apply : ∀ n k : Nat,
    readback n k = BEDC.Derived.StirlingUp.stirlingSecond n k
  nat_stirlingSecond_apply : ∀ n k : Nat, readback n k = Nat.stirlingSecond n k
  bedc_recurrence_apply : ∀ n k : Nat,
    readback (Nat.succ n) (Nat.succ k) =
      Nat.succ k * readback n (Nat.succ k) + readback n k
  recurrence_apply : ∀ n k : Nat,
    readback (Nat.succ n) (Nat.succ k) =
      Nat.succ k * Nat.stirlingSecond n (Nat.succ k) + Nat.stirlingSecond n k

def touchardCoeffExport : TouchardCoeffExportWitness where
  readback := coeffToNat
  readback_apply := by
    intro n k
    rfl
  bedc_apply := coeffToNat_apply
  bedc_stirlingSecond_apply := coeffToNat_eq_bedc_stirlingSecond
  nat_stirlingSecond_apply := coeffToNat_eq_nat_stirlingSecond
  bedc_recurrence_apply := coeffToNat_succ_succ_bedc_recurrence
  recurrence_apply := coeffToNat_succ_succ_mathlib_recurrence

theorem touchardCoeff_eq_nat_stirlingSecond (n k : Nat) :
    BEDC.Derived.TouchardPolyUp.touchardCoeff n k = Nat.stirlingSecond n k := by
  change coeffToNat n k = Nat.stirlingSecond n k
  exact BedcMathlibBridge.Constructive.TouchardPoly.coeffToNat_eq_nat_stirlingSecond n k

theorem touchardCoeff_recurrence_matches_nat_stirlingSecond (n k : Nat) :
    BEDC.Derived.TouchardPolyUp.touchardCoeff (Nat.succ n) (Nat.succ k) =
      Nat.succ k * Nat.stirlingSecond n (Nat.succ k) + Nat.stirlingSecond n k := by
  calc
    BEDC.Derived.TouchardPolyUp.touchardCoeff (Nat.succ n) (Nat.succ k) =
        Nat.succ k * BEDC.Derived.TouchardPolyUp.touchardCoeff n (Nat.succ k) +
          BEDC.Derived.TouchardPolyUp.touchardCoeff n k :=
      BEDC.Derived.TouchardPolyUp.stirlingSecond_succ_coeff_recurrence n k
    _ = Nat.succ k * Nat.stirlingSecond n (Nat.succ k) + Nat.stirlingSecond n k := by
      rw [touchardCoeff_eq_nat_stirlingSecond n (Nat.succ k),
        touchardCoeff_eq_nat_stirlingSecond n k]

end BedcMathlibBridge.Export.TouchardPoly
