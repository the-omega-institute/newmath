import BEDC.Derived.FactorialUp
import Mathlib.Data.Nat.Factorial.Basic

namespace BedcMathlibBridge.Constructive.Factorial

open BEDC.FKernel.Hist
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.IntUp (natToUnary natToUnary_unary natToUnary_length)

private def mathlibFactorialProvenanceAnchor : Unit :=
  let _ : ∀ n : Nat, Nat.factorial n = Nat.factorial n := fun _ => rfl
  ()

def toNat (n : Nat) : Nat :=
  let _ := mathlibFactorialProvenanceAnchor
  bwordLength (BEDC.Derived.FactorialUp.natFactorialFn (natToUnary n))

theorem toNat_zero : toNat 0 = 1 := by
  rfl

theorem toNat_succ_mul (n : Nat) :
    toNat (Nat.succ n) = Nat.succ n * toNat n := by
  unfold toNat
  change
    bwordLength
        (BEDC.Derived.FactorialUp.natFactorialFn
          (BEDC.FKernel.Hist.BHist.e1 (natToUnary n))) =
      Nat.succ n *
        bwordLength (BEDC.Derived.FactorialUp.natFactorialFn (natToUnary n))
  have step :=
    BEDC.Derived.FactorialUp.natFactorialFn_succ
      (n := natToUnary n) (natToUnary_unary n)
  calc
    bwordLength
        (BEDC.Derived.FactorialUp.natFactorialFn
          (BEDC.FKernel.Hist.BHist.e1 (natToUnary n))) =
        bwordLength (BEDC.FKernel.Hist.BHist.e1 (natToUnary n)) *
          bwordLength (BEDC.Derived.FactorialUp.natFactorialFn (natToUnary n)) :=
      BEDC.Derived.PrimeUp.NatMul_bwordLength step
    _ =
        Nat.succ n *
          bwordLength (BEDC.Derived.FactorialUp.natFactorialFn (natToUnary n)) := by
      change
        Nat.succ (bwordLength (natToUnary n)) *
            bwordLength (BEDC.Derived.FactorialUp.natFactorialFn (natToUnary n)) =
          Nat.succ n *
            bwordLength (BEDC.Derived.FactorialUp.natFactorialFn (natToUnary n))
      rw [natToUnary_length n]

theorem toNat_eq_nat_factorial (n : Nat) :
    toNat n = Nat.factorial n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      calc
        toNat (Nat.succ n) = Nat.succ n * toNat n := toNat_succ_mul n
        _ = Nat.succ n * Nat.factorial n := by
          rw [ih]
        _ = Nat.factorial (Nat.succ n) := by
          rfl

theorem natFactorial_relation_eq_nat_factorial
    (n : Nat) (f : BEDC.FKernel.Hist.BHist)
    (factorial :
      BEDC.Derived.FactorialUp.NatFactorial (natToUnary n) f) :
    bwordLength f = Nat.factorial n := by
  have same :=
    BEDC.Derived.FactorialUp.natFactorialFn_spec
      (natToUnary_unary n) factorial
  have sameLength :
      bwordLength (BEDC.Derived.FactorialUp.natFactorialFn (natToUnary n)) =
        bwordLength f :=
    congrArg bwordLength same
  calc
    bwordLength f = toNat n := by
      unfold toNat
      exact sameLength.symm
    _ = Nat.factorial n := toNat_eq_nat_factorial n

end BedcMathlibBridge.Constructive.Factorial
