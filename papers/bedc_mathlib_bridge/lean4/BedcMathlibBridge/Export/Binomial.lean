import BedcMathlibBridge.Constructive.Binomial

namespace BedcMathlibBridge.Export.Binomial

open BedcMathlibBridge.Constructive.Binomial

structure BinomialExportWitness where
  bedc_apply : ∀ n k : Nat,
    BEDC.Derived.LucasTheoremUp.bedcChooseNat n k =
      BEDC.Derived.LucasTheoremUp.bedcChooseNat n k
  nat_choose_apply : ∀ n k : Nat, Nat.choose n k = Nat.choose n k
  zero_zero : BEDC.Derived.LucasTheoremUp.bedcChooseNat 0 0 = 1
  zero_succ : ∀ k : Nat,
    BEDC.Derived.LucasTheoremUp.bedcChooseNat 0 (Nat.succ k) = 0
  succ_zero : ∀ n : Nat,
    BEDC.Derived.LucasTheoremUp.bedcChooseNat (Nat.succ n) 0 = 1
  pascal_apply : ∀ n k : Nat,
    BEDC.Derived.LucasTheoremUp.bedcChooseNat (Nat.succ n) (Nat.succ k) =
      BEDC.Derived.LucasTheoremUp.bedcChooseNat n k +
        BEDC.Derived.LucasTheoremUp.bedcChooseNat n (Nat.succ k)

def binomialExport : BinomialExportWitness where
  bedc_apply := by
    intro n k
    rfl
  nat_choose_apply := by
    intro n k
    rfl
  zero_zero := by
    calc
      BEDC.Derived.LucasTheoremUp.bedcChooseNat 0 0 = Nat.choose 0 0 :=
        bedcChoose_eq_nat_choose 0 0
      _ = 1 := rfl
  zero_succ := by
    intro k
    calc
      BEDC.Derived.LucasTheoremUp.bedcChooseNat 0 (Nat.succ k) =
          Nat.choose 0 (Nat.succ k) :=
        bedcChoose_eq_nat_choose 0 (Nat.succ k)
      _ = 0 := Nat.choose_zero_succ k
  succ_zero := by
    intro n
    calc
      BEDC.Derived.LucasTheoremUp.bedcChooseNat (Nat.succ n) 0 =
          Nat.choose (Nat.succ n) 0 :=
        bedcChoose_eq_nat_choose (Nat.succ n) 0
      _ = 1 := Nat.choose_zero_right (Nat.succ n)
  pascal_apply := BEDC.Derived.LucasTheoremUp.bedcChooseNat_pascal

theorem bedcChoose_eq_nat_choose (n k : Nat) :
    BEDC.Derived.LucasTheoremUp.bedcChooseNat n k = Nat.choose n k :=
  BedcMathlibBridge.Constructive.Binomial.bedcChoose_eq_nat_choose n k

end BedcMathlibBridge.Export.Binomial
