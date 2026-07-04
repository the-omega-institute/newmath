import BedcMathlibBridge.Constructive.PellLucas

/-!
Export witness for the Pell-Lucas recurrence readback correspondence.
-/

namespace BedcMathlibBridge.Export.PellLucas

open BedcMathlibBridge.Constructive.PellLucas

structure PellLucasExportWitness where
  pellReadback : Nat -> Nat
  companionReadback : Nat -> Nat
  pell_apply :
    forall n : Nat,
      pellReadback n = BedcMathlibBridge.Constructive.PellLucas.pellReadback n
  companion_apply :
    forall n : Nat,
      companionReadback n =
        BedcMathlibBridge.Constructive.PellLucas.companionReadback n
  bedc_pell_apply :
    forall n : Nat, pellReadback n = BEDC.Derived.PellLucasUp.pellNat n
  bedc_companion_apply :
    forall n : Nat, companionReadback n = BEDC.Derived.PellLucasUp.companionPellNat n
  pell_zero : pellReadback 0 = 0
  pell_one : pellReadback 1 = 1
  companion_zero : companionReadback 0 = 2
  companion_one : companionReadback 1 = 2
  pell_recurrence : forall n : Nat,
    pellReadback (n + 2) =
      Nat.add (Nat.mul 2 (pellReadback (n + 1))) (pellReadback n)
  companion_recurrence : forall n : Nat,
    companionReadback (n + 2) =
      Nat.add (Nat.mul 2 (companionReadback (n + 1))) (companionReadback n)
  companion_adjacent_sum : forall n : Nat,
    companionReadback (n + 1) =
      Nat.add (pellReadback (n + 2)) (pellReadback n)
  mathlib_anchor : Nat.succ_injective = Nat.succ_injective

def pellLucasExport : PellLucasExportWitness where
  pellReadback := pellReadback
  companionReadback := companionReadback
  pell_apply := by
    intro n
    rfl
  companion_apply := by
    intro n
    rfl
  bedc_pell_apply := pellReadback_apply
  bedc_companion_apply := companionReadback_apply
  pell_zero := pellReadback_zero
  pell_one := pellReadback_one
  companion_zero := companionReadback_zero
  companion_one := companionReadback_one
  pell_recurrence := pellReadback_recurrence
  companion_recurrence := companionReadback_recurrence
  companion_adjacent_sum := companionReadback_adjacent_sum
  mathlib_anchor := mathlibNatAnchor

theorem pellNat_recurrence_nat_add_mul
    (n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    BEDC.Derived.PellLucasUp.pellNat (n + 2) =
      Nat.add
        (Nat.mul 2 (BEDC.Derived.PellLucasUp.pellNat (n + 1)))
        (BEDC.Derived.PellLucasUp.pellNat n) :=
  BedcMathlibBridge.Constructive.PellLucas.pellNat_recurrence_nat_add_mul n

theorem companionPellNat_recurrence_nat_add_mul
    (n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    BEDC.Derived.PellLucasUp.companionPellNat (n + 2) =
      Nat.add
        (Nat.mul 2 (BEDC.Derived.PellLucasUp.companionPellNat (n + 1)))
        (BEDC.Derived.PellLucasUp.companionPellNat n) :=
  BedcMathlibBridge.Constructive.PellLucas.companionPellNat_recurrence_nat_add_mul n

theorem companionPellNat_adjacent_sum_nat_add
    (n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    BEDC.Derived.PellLucasUp.companionPellNat (n + 1) =
      Nat.add
        (BEDC.Derived.PellLucasUp.pellNat (n + 2))
        (BEDC.Derived.PellLucasUp.pellNat n) :=
  BedcMathlibBridge.Constructive.PellLucas.companionPellNat_adjacent_sum_nat_add n

theorem pellLucas_recurrence_readback_nat_add_mul
    (n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    BEDC.Derived.PellLucasUp.pellNat (n + 2) =
        Nat.add
          (Nat.mul 2 (BEDC.Derived.PellLucasUp.pellNat (n + 1)))
          (BEDC.Derived.PellLucasUp.pellNat n) ∧
      BEDC.Derived.PellLucasUp.companionPellNat (n + 2) =
        Nat.add
          (Nat.mul 2 (BEDC.Derived.PellLucasUp.companionPellNat (n + 1)))
          (BEDC.Derived.PellLucasUp.companionPellNat n) ∧
      BEDC.Derived.PellLucasUp.companionPellNat (n + 1) =
        Nat.add
          (BEDC.Derived.PellLucasUp.pellNat (n + 2))
          (BEDC.Derived.PellLucasUp.pellNat n) :=
  ⟨BedcMathlibBridge.Constructive.PellLucas.pellNat_recurrence_nat_add_mul n,
    BedcMathlibBridge.Constructive.PellLucas.companionPellNat_recurrence_nat_add_mul n,
    BedcMathlibBridge.Constructive.PellLucas.companionPellNat_adjacent_sum_nat_add n⟩

end BedcMathlibBridge.Export.PellLucas
