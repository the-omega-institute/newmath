import BedcMathlibBridge.Constructive.SternDiatomic

namespace BedcMathlibBridge.Export.SternDiatomic

open BedcMathlibBridge.Constructive.SternDiatomic

structure SternDiatomicExportWitness where
  fuelReadback : Nat -> Nat -> Nat
  readback : Nat -> Nat
  fuel_apply :
    forall fuel n : Nat,
      fuelReadback fuel n =
        BedcMathlibBridge.Constructive.SternDiatomic.fuelReadback fuel n
  readback_apply :
    forall n : Nat,
      readback n = BedcMathlibBridge.Constructive.SternDiatomic.readback n
  bedc_fuel_apply :
    forall fuel n : Nat,
      fuelReadback fuel n = BEDC.Derived.SternDiatomicUp.fuscFuel fuel n
  bedc_apply :
    forall n : Nat, readback n = BEDC.Derived.SternDiatomicUp.fusc n
  zero_apply : readback 0 = 0
  one_apply : readback 1 = 1
  even_positive :
    forall fuel n : Nat,
      fuelReadback (fuel + 1)
          (BEDC.Derived.SternDiatomicUp.sternDouble (n + 1)) =
        fuelReadback fuel (n + 1)
  odd_positive :
    forall fuel n : Nat,
      fuelReadback (fuel + 1)
          (Nat.succ (BEDC.Derived.SternDiatomicUp.sternDouble (n + 1))) =
        Nat.add (fuelReadback fuel (n + 1)) (fuelReadback fuel (n + 2))
  mathlib_anchor : Nat.succ_injective = Nat.succ_injective

def sternDiatomicExport : SternDiatomicExportWitness where
  fuelReadback := fuelReadback
  readback := readback
  fuel_apply := by
    intro fuel n
    rfl
  readback_apply := by
    intro n
    rfl
  bedc_fuel_apply := fuelReadback_apply
  bedc_apply := readback_apply
  zero_apply := readback_zero
  one_apply := readback_one
  even_positive := fuelReadback_even_positive
  odd_positive := fuelReadback_odd_positive_nat_add
  mathlib_anchor := mathlibNatAnchor

theorem fuscFuel_odd_positive_nat_add
    (fuel n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    BEDC.Derived.SternDiatomicUp.fuscFuel (fuel + 1)
        (Nat.succ (BEDC.Derived.SternDiatomicUp.sternDouble (n + 1))) =
      Nat.add
        (BEDC.Derived.SternDiatomicUp.fuscFuel fuel (n + 1))
        (BEDC.Derived.SternDiatomicUp.fuscFuel fuel (n + 2)) :=
  BedcMathlibBridge.Constructive.SternDiatomic.fuscFuel_odd_positive_nat_add
    fuel n

end BedcMathlibBridge.Export.SternDiatomic
