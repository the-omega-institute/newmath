import BEDC.Derived.TouchardPolyUp
import BedcMathlibBridge.Constructive.StirlingSecond

namespace BedcMathlibBridge.Constructive.TouchardPoly

private def mathlibStirlingSecondProvenanceAnchor : Unit :=
  let _ : ∀ n k : Nat, Nat.stirlingSecond n k = Nat.stirlingSecond n k :=
    fun _ _ => rfl
  ()

def coeffToNat (n k : Nat) : Nat :=
  let _ := mathlibStirlingSecondProvenanceAnchor
  BEDC.Derived.TouchardPolyUp.touchardCoeff n k

theorem coeffToNat_apply (n k : Nat) :
    coeffToNat n k = BEDC.Derived.TouchardPolyUp.touchardCoeff n k :=
  rfl

theorem coeffToNat_eq_bedc_stirlingSecond (n k : Nat) :
    coeffToNat n k = BEDC.Derived.StirlingUp.stirlingSecond n k := by
  change
    BEDC.Derived.TouchardPolyUp.touchardCoeff n k =
      BEDC.Derived.StirlingUp.stirlingSecond n k
  exact BEDC.Derived.TouchardPolyUp.touchardCoeff_definition n k

theorem coeffToNat_eq_nat_stirlingSecond (n k : Nat) :
    coeffToNat n k = Nat.stirlingSecond n k := by
  calc
    coeffToNat n k = BEDC.Derived.StirlingUp.stirlingSecond n k :=
      coeffToNat_eq_bedc_stirlingSecond n k
    _ = Nat.stirlingSecond n k := by
      change
        BedcMathlibBridge.Constructive.StirlingSecond.toNat n k =
          Nat.stirlingSecond n k
      exact BedcMathlibBridge.Constructive.StirlingSecond.toNat_eq_nat_stirlingSecond n k

theorem coeffToNat_succ_succ_bedc_recurrence (n k : Nat) :
    coeffToNat (Nat.succ n) (Nat.succ k) =
      Nat.succ k * coeffToNat n (Nat.succ k) + coeffToNat n k := by
  change
    BEDC.Derived.TouchardPolyUp.touchardCoeff (Nat.succ n) (Nat.succ k) =
      Nat.succ k * BEDC.Derived.TouchardPolyUp.touchardCoeff n (Nat.succ k) +
        BEDC.Derived.TouchardPolyUp.touchardCoeff n k
  exact BEDC.Derived.TouchardPolyUp.stirlingSecond_succ_coeff_recurrence n k

theorem coeffToNat_succ_succ_mathlib_recurrence (n k : Nat) :
    coeffToNat (Nat.succ n) (Nat.succ k) =
      Nat.succ k * Nat.stirlingSecond n (Nat.succ k) + Nat.stirlingSecond n k := by
  calc
    coeffToNat (Nat.succ n) (Nat.succ k) =
        Nat.stirlingSecond (Nat.succ n) (Nat.succ k) :=
      coeffToNat_eq_nat_stirlingSecond (Nat.succ n) (Nat.succ k)
    _ = Nat.succ k * Nat.stirlingSecond n (Nat.succ k) + Nat.stirlingSecond n k :=
      Nat.stirlingSecond_succ_succ n k

end BedcMathlibBridge.Constructive.TouchardPoly
