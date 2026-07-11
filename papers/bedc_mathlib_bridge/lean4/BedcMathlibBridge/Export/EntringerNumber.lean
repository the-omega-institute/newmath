import BedcMathlibBridge.Constructive.EntringerNumber

namespace BedcMathlibBridge.Export.EntringerNumber

open BedcMathlibBridge.Constructive.EntringerNumber

structure EntringerNumberExportWitness where
  readback : Nat -> Nat -> Nat
  zigzagReadback : Nat -> Nat
  readback_apply :
    forall n k : Nat,
      readback n k = BedcMathlibBridge.Constructive.EntringerNumber.readback n k
  zigzag_readback_apply :
    forall n : Nat,
      zigzagReadback n =
        BedcMathlibBridge.Constructive.EntringerNumber.zigzagReadback n
  bedc_apply :
    forall n k : Nat,
      readback n k = BEDC.Derived.EntringerNumberUp.entringerNumber n k
  zigzag_bedc_apply :
    forall n : Nat,
      zigzagReadback n = BEDC.Derived.EntringerNumberUp.zigzagByEntringer n
  zero_zero : readback 0 0 = 1
  zero_succ : forall k : Nat, readback 0 (Nat.succ k) = 0
  succ_zero : forall n : Nat, readback (Nat.succ n) 0 = 0
  succ_succ_apply : forall n k : Nat,
    readback (Nat.succ n) (Nat.succ k) =
      Nat.add (readback (Nat.succ n) k) (readback n (Nat.sub n k))
  zigzag_zero : zigzagReadback 0 = 1
  zigzag_one : zigzagReadback 1 = 1
  zigzag_two : zigzagReadback 2 = 1
  zigzag_three : zigzagReadback 3 = 2
  zigzag_four : zigzagReadback 4 = 5
  mathlib_anchor : Nat.succ_injective = Nat.succ_injective

def entringerNumberExport : EntringerNumberExportWitness where
  readback := readback
  zigzagReadback := zigzagReadback
  readback_apply := by
    intro n k
    rfl
  zigzag_readback_apply := by
    intro n
    rfl
  bedc_apply := readback_apply
  zigzag_bedc_apply := zigzagReadback_apply
  zero_zero := readback_zero_zero
  zero_succ := readback_zero_succ
  succ_zero := readback_succ_zero
  succ_succ_apply := succ_succ_nat_add_sub
  zigzag_zero := zigzagReadback_zero
  zigzag_one := zigzagReadback_one
  zigzag_two := zigzagReadback_two
  zigzag_three := zigzagReadback_three
  zigzag_four := zigzagReadback_four
  mathlib_anchor := mathlibNatAnchor

theorem entringer_succ_succ_nat_add_sub
    (n k : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    BEDC.Derived.EntringerNumberUp.entringerNumber (Nat.succ n) (Nat.succ k) =
      Nat.add
        (BEDC.Derived.EntringerNumberUp.entringerNumber (Nat.succ n) k)
        (BEDC.Derived.EntringerNumberUp.entringerNumber n (Nat.sub n k)) := by
  change
    readback (Nat.succ n) (Nat.succ k) =
      Nat.add (readback (Nat.succ n) k) (readback n (Nat.sub n k))
  exact succ_succ_nat_add_sub n k

end BedcMathlibBridge.Export.EntringerNumber
