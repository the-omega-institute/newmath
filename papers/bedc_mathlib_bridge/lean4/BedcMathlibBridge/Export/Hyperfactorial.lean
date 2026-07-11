import BedcMathlibBridge.Constructive.Hyperfactorial

namespace BedcMathlibBridge.Export.Hyperfactorial

open BedcMathlibBridge.Constructive.Hyperfactorial

structure HyperfactorialExportWitness where
  readback : Nat -> Nat
  readback_apply : forall n : Nat, readback n = toNat n
  bedc_apply : forall n : Nat,
    readback n = BEDC.Derived.HyperfactorialUp.hyperfactorial n
  zero_apply : readback 0 = 1
  recurrence_apply : forall n : Nat,
    readback (Nat.succ n) =
      readback n * BEDC.Derived.HyperfactorialUp.hyperfactorialTerm (Nat.succ n)
  nat_pow_term_apply : forall n : Nat,
    readback (Nat.succ n) = readback n * Nat.pow (Nat.succ n) (Nat.succ n)
  mathlib_anchor : Nat.succ_injective = Nat.succ_injective

def hyperfactorialExport : HyperfactorialExportWitness where
  readback := toNat
  readback_apply := by
    intro n
    rfl
  bedc_apply := by
    intro n
    rfl
  zero_apply := toNat_zero
  recurrence_apply := toNat_succ
  nat_pow_term_apply := toNat_succ_eq_nat_pow_term
  mathlib_anchor := mathlibPowAnchor

theorem hyperfactorial_succ_eq_nat_pow_term
    (n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibPowAnchor) :
    BEDC.Derived.HyperfactorialUp.hyperfactorial (Nat.succ n) =
      BEDC.Derived.HyperfactorialUp.hyperfactorial n *
        Nat.pow (Nat.succ n) (Nat.succ n) :=
  BedcMathlibBridge.Constructive.Hyperfactorial.hyperfactorial_succ_eq_nat_pow_term n

end BedcMathlibBridge.Export.Hyperfactorial
