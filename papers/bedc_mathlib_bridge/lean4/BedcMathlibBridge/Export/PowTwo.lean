import BedcMathlibBridge.Constructive.PowTwo

namespace BedcMathlibBridge.Export.PowTwo

open BedcMathlibBridge.Constructive.PowTwo

structure PowTwoExportWitness where
  readback : Nat -> Nat
  readback_apply : forall n : Nat, readback n = toNat n
  bedc_apply : forall n : Nat, readback n = BEDC.Derived.JacobsthalUp.powTwo n
  zero_apply : readback 0 = 1
  recurrence_apply : forall n : Nat, readback (n + 1) = 2 * readback n
  nat_pow_apply : forall n : Nat, readback n = Nat.pow 2 n
  mathlib_anchor : Nat.succ_injective = Nat.succ_injective

def powTwoExport : PowTwoExportWitness where
  readback := toNat
  readback_apply := by
    intro n
    rfl
  bedc_apply := toNat_apply
  zero_apply := toNat_zero
  recurrence_apply := toNat_succ
  nat_pow_apply := toNat_eq_nat_pow_two
  mathlib_anchor := mathlibPowAnchor

theorem jacobsthalPowTwo_eq_nat_pow_two
    (n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibPowAnchor) :
    BEDC.Derived.JacobsthalUp.powTwo n = Nat.pow 2 n := by
  exact BedcMathlibBridge.Constructive.PowTwo.toNat_eq_nat_pow_two n

end BedcMathlibBridge.Export.PowTwo
