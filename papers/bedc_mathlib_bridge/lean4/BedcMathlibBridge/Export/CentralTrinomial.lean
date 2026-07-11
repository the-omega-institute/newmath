import BedcMathlibBridge.Constructive.CentralTrinomial

/-!
Export witness for the central trinomial recurrence readback correspondence.
-/

namespace BedcMathlibBridge.Export.CentralTrinomial

open BedcMathlibBridge.Constructive.CentralTrinomial

structure CentralTrinomialExportWitness where
  readback : Nat -> Nat
  readback_apply : forall n : Nat, readback n = toNat n
  bedc_apply :
    forall n : Nat,
      readback n = BEDC.Derived.CentralTrinomialUp.centralTrinomialNumber n
  zero_apply : readback 0 = 1
  one_apply : readback 1 = 1
  two_apply : readback 2 = 3
  three_apply : readback 3 = 7
  diagonal_recurrence_apply : forall n : Nat,
    readback (Nat.succ (Nat.succ n)) =
      Nat.add
        (Nat.add
          (BEDC.Derived.CentralTrinomialUp.trinomialCoeff (Nat.succ n)
            (Nat.succ (Nat.succ n)))
          (BEDC.Derived.CentralTrinomialUp.trinomialCoeff (Nat.succ n)
            (Nat.succ n)))
        (BEDC.Derived.CentralTrinomialUp.trinomialCoeff (Nat.succ n) n)
  mathlib_anchor : Nat.succ_injective = Nat.succ_injective

def centralTrinomialExport : CentralTrinomialExportWitness where
  readback := toNat
  readback_apply := by
    intro n
    rfl
  bedc_apply := toNat_apply
  zero_apply := toNat_zero
  one_apply := toNat_one
  two_apply := toNat_two
  three_apply := toNat_three
  diagonal_recurrence_apply := toNat_succ_succ_diagonal
  mathlib_anchor := mathlibNatAnchor

theorem centralTrinomial_recurrence_nat_add
    (n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    BEDC.Derived.CentralTrinomialUp.centralTrinomialNumber
        (Nat.succ (Nat.succ n)) =
      Nat.add
        (Nat.add
          (BEDC.Derived.CentralTrinomialUp.trinomialCoeff (Nat.succ n)
            (Nat.succ (Nat.succ n)))
          (BEDC.Derived.CentralTrinomialUp.trinomialCoeff (Nat.succ n)
            (Nat.succ n)))
        (BEDC.Derived.CentralTrinomialUp.trinomialCoeff (Nat.succ n) n) :=
  BedcMathlibBridge.Constructive.CentralTrinomial.centralTrinomial_recurrence_nat_add n

end BedcMathlibBridge.Export.CentralTrinomial
