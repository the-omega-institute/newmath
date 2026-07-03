import BedcMathlibBridge.Constructive.Narayana

/-!
Export witness for the Narayana-number structural correspondence.

The witness records the direct BEDC readback, the zero boundaries, complement
symmetry, and the explicit `Nat.choose` formula used as the mathlib anchor.
-/

namespace BedcMathlibBridge.Export.Narayana

open BedcMathlibBridge.Constructive.Narayana

structure NarayanaExportWitness where
  readback : Nat -> Nat -> Nat
  readback_apply : ∀ n k : Nat, readback n k = toNat n k
  bedc_apply : ∀ n k : Nat,
    readback n k = BEDC.Derived.NarayanaUp.narayanaNumber n k
  zero_left_apply : ∀ k : Nat, readback 0 k = 0
  succ_zero_apply : ∀ n : Nat, readback (Nat.succ n) 0 = 0
  nat_choose_formula_apply : ∀ n k : Nat,
    readback (Nat.succ n) (Nat.succ k) =
      Nat.choose (Nat.succ n) (Nat.succ k) *
          Nat.choose (Nat.succ n) k /
        Nat.succ n
  complement_symmetry_apply : ∀ k l : Nat,
    readback (Nat.succ (k + l)) (Nat.succ k) =
      readback (Nat.succ (k + l)) (Nat.succ l)

def narayanaExport : NarayanaExportWitness where
  readback := toNat
  readback_apply := by
    intro n k
    rfl
  bedc_apply := by
    intro n k
    rfl
  zero_left_apply := toNat_zero_left
  succ_zero_apply := toNat_succ_zero
  nat_choose_formula_apply := chooseFormula_succ_succ
  complement_symmetry_apply := complement_symmetry

theorem narayanaNumber_eq_nat_choose_formula (n k : Nat) :
    BEDC.Derived.NarayanaUp.narayanaNumber (Nat.succ n) (Nat.succ k) =
      Nat.choose (Nat.succ n) (Nat.succ k) *
          Nat.choose (Nat.succ n) k /
        Nat.succ n :=
  BedcMathlibBridge.Constructive.Narayana.chooseFormula_succ_succ n k

end BedcMathlibBridge.Export.Narayana
