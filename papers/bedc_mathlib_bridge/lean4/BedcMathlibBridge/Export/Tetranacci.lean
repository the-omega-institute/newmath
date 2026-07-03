import BedcMathlibBridge.Constructive.Tetranacci

namespace BedcMathlibBridge.Export.Tetranacci

open BedcMathlibBridge.Constructive.Tetranacci

structure TetranacciExportWitness where
  readback : Nat -> Nat
  readback_apply : forall n : Nat, readback n = toNat n
  bedc_apply : forall n : Nat, readback n = BEDC.Derived.TetranacciUp.tetranacci n
  zero_apply : readback 0 = 0
  one_apply : readback 1 = 0
  two_apply : readback 2 = 0
  three_apply : readback 3 = 1
  recurrence_apply : forall n : Nat,
    readback (n + 4) =
      Nat.add
        (Nat.add (Nat.add (readback n) (readback (n + 1))) (readback (n + 2)))
        (readback (n + 3))
  mathlib_anchor : Nat.succ_injective = Nat.succ_injective

def tetranacciExport : TetranacciExportWitness where
  readback := toNat
  readback_apply := by
    intro n
    rfl
  bedc_apply := toNat_apply
  zero_apply := toNat_zero
  one_apply := toNat_one
  two_apply := toNat_two
  three_apply := toNat_three
  recurrence_apply := toNat_recurrence
  mathlib_anchor := mathlibNatAnchor

theorem tetranacci_recurrence_nat_add
    (n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    BEDC.Derived.TetranacciUp.tetranacci (n + 4) =
      Nat.add
        (Nat.add
          (Nat.add (BEDC.Derived.TetranacciUp.tetranacci n)
            (BEDC.Derived.TetranacciUp.tetranacci (n + 1)))
          (BEDC.Derived.TetranacciUp.tetranacci (n + 2)))
        (BEDC.Derived.TetranacciUp.tetranacci (n + 3)) :=
  BedcMathlibBridge.Constructive.Tetranacci.tetranacci_recurrence_nat_add n

end BedcMathlibBridge.Export.Tetranacci
