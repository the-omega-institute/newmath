import BedcMathlibBridge.Constructive.CullenWoodall

/-!
Export witnesses for the Cullen and Woodall Nat readbacks.
-/

namespace BedcMathlibBridge.Export.CullenWoodall

open BedcMathlibBridge.Constructive.CullenWoodall

structure CullenExportWitness where
  readback : Nat -> Nat
  readback_apply :
    forall n : Nat, readback n = BEDC.Derived.CullenWoodallUp.cullenNat n
  zero_apply : readback 0 = 1
  one_apply : readback 1 = 3
  nat_pow_apply : forall n : Nat, readback n = n * Nat.pow 2 n + 1
  mathlib_anchor : Nat.succ_injective = Nat.succ_injective

def cullenExport : CullenExportWitness where
  readback := cullenReadback
  readback_apply := cullenReadback_apply
  zero_apply := cullenReadback_zero
  one_apply := cullenReadback_one
  nat_pow_apply := cullenReadback_eq_nat_mul_pow_add_one
  mathlib_anchor := mathlibPowAnchor

theorem cullenNat_eq_nat_mul_pow_add_one
    (n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibPowAnchor) :
    BEDC.Derived.CullenWoodallUp.cullenNat n = n * Nat.pow 2 n + 1 := by
  change cullenReadback n = n * Nat.pow 2 n + 1
  exact cullenReadback_eq_nat_mul_pow_add_one n

structure WoodallExportWitness where
  readback : Nat -> Nat
  readback_apply :
    forall n : Nat, readback n = BEDC.Derived.CullenWoodallUp.woodallNat n
  zero_apply : readback 0 = 0
  one_apply : readback 1 = 1
  nat_pow_apply : forall n : Nat, readback n = n * Nat.pow 2 n - 1
  mathlib_anchor : Nat.succ_injective = Nat.succ_injective

def woodallExport : WoodallExportWitness where
  readback := woodallReadback
  readback_apply := woodallReadback_apply
  zero_apply := woodallReadback_zero
  one_apply := woodallReadback_one
  nat_pow_apply := woodallReadback_eq_nat_mul_pow_sub_one
  mathlib_anchor := mathlibPowAnchor

theorem woodallNat_eq_nat_mul_pow_sub_one
    (n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibPowAnchor) :
    BEDC.Derived.CullenWoodallUp.woodallNat n = n * Nat.pow 2 n - 1 := by
  change woodallReadback n = n * Nat.pow 2 n - 1
  exact woodallReadback_eq_nat_mul_pow_sub_one n

end BedcMathlibBridge.Export.CullenWoodall
