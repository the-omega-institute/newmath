import BedcMathlibBridge.Constructive.Raney

namespace BedcMathlibBridge.Export.Raney

open BedcMathlibBridge.Constructive.Raney

structure RaneyExportWitness where
  readback : Nat -> Nat -> Nat -> Nat
  readback_apply :
    forall m r n : Nat, readback m r n = toNat m r n
  bedc_apply :
    forall m r n : Nat,
      readback m r n = BEDC.Derived.RaneyNumberUp.raneyNumber m r n
  nat_choose_formula_apply :
    forall m r n : Nat,
      readback m r n = r * Nat.choose (m * n + r) n / (m * n + r)

def raneyExport : RaneyExportWitness where
  readback := toNat
  readback_apply := by
    intro m r n
    rfl
  bedc_apply := toNat_apply
  nat_choose_formula_apply := toNat_eq_nat_choose_formula

theorem raneyNumber_eq_nat_choose_formula (m r n : Nat) :
    BEDC.Derived.RaneyNumberUp.raneyNumber m r n =
      r * Nat.choose (m * n + r) n / (m * n + r) :=
  BedcMathlibBridge.Constructive.Raney.toNat_eq_nat_choose_formula m r n

end BedcMathlibBridge.Export.Raney
