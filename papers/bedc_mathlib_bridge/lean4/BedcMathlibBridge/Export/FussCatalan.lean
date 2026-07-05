import BedcMathlibBridge.Constructive.FussCatalan

namespace BedcMathlibBridge.Export.FussCatalan

open BedcMathlibBridge.Constructive.FussCatalan

structure FussCatalanExportWitness where
  readback : Nat -> Nat -> Nat
  readback_apply : ∀ m n : Nat, readback m n = toNat m n
  bedc_apply : ∀ m n : Nat,
    readback m n = BEDC.Derived.FussCatalanUp.fussCatalanCount m n
  nat_choose_div_apply : ∀ m n : Nat,
    readback m n = Nat.choose (m * n) n / ((m - 1) * n + 1)
  binary_central_binom_apply : ∀ n : Nat,
    readback 2 n = Nat.centralBinom n / (n + 1)

def fussCatalanExport : FussCatalanExportWitness where
  readback := toNat
  readback_apply := by
    intro m n
    rfl
  bedc_apply := toNat_apply
  nat_choose_div_apply := toNat_eq_nat_choose_formula
  binary_central_binom_apply := toNat_binary_eq_centralBinom_div

theorem fussCatalanCount_eq_nat_choose_formula (m n : Nat) :
    BEDC.Derived.FussCatalanUp.fussCatalanCount m n =
      Nat.choose (m * n) n / ((m - 1) * n + 1) :=
  calc
    BEDC.Derived.FussCatalanUp.fussCatalanCount m n = toNat m n :=
      (toNat_apply m n).symm
    _ = Nat.choose (m * n) n / ((m - 1) * n + 1) :=
      BedcMathlibBridge.Constructive.FussCatalan.toNat_eq_nat_choose_formula m n

theorem fussCatalanCount_eq_nat_choose_div (m n : Nat) :
    BEDC.Derived.FussCatalanUp.fussCatalanCount m n =
      Nat.choose (m * n) n / ((m - 1) * n + 1) :=
  fussCatalanCount_eq_nat_choose_formula m n

theorem fussCatalan_binary_eq_centralBinom_div (n : Nat) :
    BEDC.Derived.FussCatalanUp.fussCatalanCount 2 n =
      Nat.centralBinom n / (n + 1) :=
  by
    change toNat 2 n = Nat.centralBinom n / (n + 1)
    exact BedcMathlibBridge.Constructive.FussCatalan.toNat_binary_eq_centralBinom_div n

end BedcMathlibBridge.Export.FussCatalan
