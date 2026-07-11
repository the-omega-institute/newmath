import BedcMathlibBridge.Constructive.NatChooseSuccSuccPrime

namespace BedcMathlibBridge.Export.NatChooseSuccSuccPrime

open BedcMathlibBridge.Constructive.NatChooseSuccSuccPrime

structure NatChooseSuccSuccPrimeExportWitness where
  readback : ∀ n k : Nat,
    Nat.choose (n + 1) (k + 1) = Nat.choose n k + Nat.choose n (k + 1)
  readback_apply :
    ∀ n k : Nat, readback n k = chooseSuccSuccPrimeReadback n k
  mathlib_apply :
    ∀ n k : Nat, readback n k = Nat.choose_succ_succ' n k
  mathlib_anchor : Function.Injective Nat.succ
  mathlib_anchor_apply : mathlib_anchor = Nat.succ_injective

def natChooseSuccSuccPrimeExport : NatChooseSuccSuccPrimeExportWitness where
  readback := chooseSuccSuccPrimeReadback
  readback_apply := by
    intro n k
    rfl
  mathlib_apply := chooseSuccSuccPrimeReadback_eq_nat_choose_succ_succ_prime
  mathlib_anchor := Nat.succ_injective
  mathlib_anchor_apply := by
    rfl

theorem nat_choose_succ_succ_prime_mathlib_correspondence (n k : Nat) :
    chooseSuccSuccPrimeReadback n k = Nat.choose_succ_succ' n k := by
  exact chooseSuccSuccPrimeReadback_eq_nat_choose_succ_succ_prime n k

end BedcMathlibBridge.Export.NatChooseSuccSuccPrime
