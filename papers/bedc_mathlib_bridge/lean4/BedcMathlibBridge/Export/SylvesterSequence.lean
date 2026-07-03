import BedcMathlibBridge.Constructive.SylvesterSequence

/-!
Export witness for the Sylvester sequence recurrence readback.
-/

namespace BedcMathlibBridge.Export.SylvesterSequence

open BedcMathlibBridge.Constructive.SylvesterSequence

structure SylvesterSequenceExportWitness where
  readback : Nat -> Nat
  prefixProductReadback : Nat -> Nat
  readback_apply :
    forall n : Nat, readback n = BEDC.Derived.SylvesterSequenceUp.sylvester n
  prefix_product_apply :
    forall n : Nat,
      prefixProductReadback n =
        BEDC.Derived.SylvesterSequenceUp.prefixProduct n
  zero_apply : readback 0 = 2
  prefix_zero_apply : prefixProductReadback 0 = 1
  recurrence_apply :
    forall n : Nat,
      readback (n + 1) =
        Nat.add (Nat.sub (Nat.mul (readback n) (readback n)) (readback n)) 1
  prefix_recurrence_apply :
    forall n : Nat,
      prefixProductReadback (n + 1) =
        Nat.mul (prefixProductReadback n) (readback n)
  prefix_identity_apply :
    forall n : Nat, readback n = Nat.add (prefixProductReadback n) 1
  mathlib_anchor : Nat.succ_injective = Nat.succ_injective

def sylvesterSequenceExport : SylvesterSequenceExportWitness where
  readback := toNat
  prefixProductReadback := prefixProductReadback
  readback_apply := toNat_apply
  prefix_product_apply := prefixProductReadback_apply
  zero_apply := toNat_zero
  prefix_zero_apply := prefixProductReadback_zero
  recurrence_apply := sylvester_succ_recurrence_nat_mul_sub_add
  prefix_recurrence_apply := prefixProduct_succ_nat_mul
  prefix_identity_apply := toNat_eq_prefixProduct_add_one
  mathlib_anchor := mathlibNatAnchor

theorem sylvester_succ_recurrence_nat_mul_sub_add
    (n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    BEDC.Derived.SylvesterSequenceUp.sylvester (n + 1) =
      Nat.add
        (Nat.sub
          (Nat.mul
            (BEDC.Derived.SylvesterSequenceUp.sylvester n)
            (BEDC.Derived.SylvesterSequenceUp.sylvester n))
          (BEDC.Derived.SylvesterSequenceUp.sylvester n))
        1 := by
  change
    toNat (n + 1) =
      Nat.add (Nat.sub (Nat.mul (toNat n) (toNat n)) (toNat n)) 1
  exact
    BedcMathlibBridge.Constructive.SylvesterSequence.sylvester_succ_recurrence_nat_mul_sub_add n

theorem sylvester_eq_prefixProduct_add_one
    (n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    BEDC.Derived.SylvesterSequenceUp.sylvester n =
      Nat.add (BEDC.Derived.SylvesterSequenceUp.prefixProduct n) 1 := by
  change toNat n = Nat.add (prefixProductReadback n) 1
  exact
    BedcMathlibBridge.Constructive.SylvesterSequence.toNat_eq_prefixProduct_add_one n

end BedcMathlibBridge.Export.SylvesterSequence
