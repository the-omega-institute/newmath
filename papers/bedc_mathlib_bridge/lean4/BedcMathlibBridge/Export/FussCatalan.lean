import BedcMathlibBridge.Constructive.FussCatalan

namespace BedcMathlibBridge.Export.FussCatalan

open BedcMathlibBridge.Constructive.FussCatalan

structure FussCatalanExportWitness where
  readback : Nat -> Nat -> Nat
  readback_apply :
    forall m n : Nat, readback m n = toNat m n
  bedc_apply :
    forall m n : Nat,
      readback m n = BEDC.Derived.FussCatalanUp.fussCatalanCount m n
  nat_choose_formula_apply :
    forall m n : Nat,
      readback m n = Nat.choose (m * n) n / ((m - 1) * n + 1)
  prompt_shift_apply :
    forall m n : Nat,
      readback (Nat.succ m) n =
        BEDC.Derived.FussCatalanUp.fussCatalanPromptCount m n

def fussCatalanExport : FussCatalanExportWitness where
  readback := toNat
  readback_apply := by
    intro m n
    rfl
  bedc_apply := toNat_apply
  nat_choose_formula_apply := toNat_eq_nat_choose_formula
  prompt_shift_apply := toNat_prompt_shift

theorem fussCatalanCount_eq_nat_choose_formula (m n : Nat) :
    BEDC.Derived.FussCatalanUp.fussCatalanCount m n =
      Nat.choose (m * n) n / ((m - 1) * n + 1) :=
  BedcMathlibBridge.Constructive.FussCatalan.toNat_eq_nat_choose_formula m n

end BedcMathlibBridge.Export.FussCatalan
