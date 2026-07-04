import Mathlib.Data.Nat.Choose.Basic

namespace BedcMathlibBridge.Constructive.NatChooseSuccSuccPrime

private def mathlibNatChooseSuccSuccPrimeProvenanceAnchor : Unit :=
  let _ : ∀ n k : Nat,
      Nat.choose (n + 1) (k + 1) = Nat.choose n k + Nat.choose n (k + 1) :=
    Nat.choose_succ_succ'
  ()

def chooseSuccSuccPrimeReadback (n k : Nat) :
    Nat.choose (n + 1) (k + 1) = Nat.choose n k + Nat.choose n (k + 1) :=
  let _ := mathlibNatChooseSuccSuccPrimeProvenanceAnchor
  Nat.choose_succ_succ' n k

theorem chooseSuccSuccPrimeReadback_eq_nat_choose_succ_succ_prime (n k : Nat) :
    chooseSuccSuccPrimeReadback n k = Nat.choose_succ_succ' n k := by
  rfl

end BedcMathlibBridge.Constructive.NatChooseSuccSuccPrime
