import BEDC.Algebra.FiniteFold
import BEDC.Derived.FactorialUp
import BEDC.Derived.StirlingFirstUp
import BEDC.Derived.StirlingUp
import BEDC.Derived.BinomialIdentitiesUp

namespace BEDC.Derived.BesselNumberUp

open BEDC.FKernel.Hist
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.IntUp (natToUnary natToUnary_unary natToUnary_length)

abbrev UnaryOne : BHist := BHist.e1 BHist.Empty

-- $B(n,k)$ 计数 $n$ 点行上恰含 $k$ 个换位配对的对合。
def besselNumber : Nat -> Nat -> Nat
  | 0, 0 => 1
  | 0, Nat.succ _ => 0
  | Nat.succ _, 0 => 1
  | Nat.succ 0, Nat.succ _ => 0
  | Nat.succ (Nat.succ n), Nat.succ k =>
      besselNumber (Nat.succ n) (Nat.succ k) +
        Nat.succ n * besselNumber n k

def besselRowPrefix (n : Nat) : Nat -> Nat
  | 0 => besselNumber n 0
  | Nat.succ k => besselRowPrefix n k + besselNumber n (Nat.succ k)

def besselRowSum (n : Nat) : Nat :=
  besselRowPrefix n n

def involutionNumber : Nat -> Nat
  | 0 => 1
  | Nat.succ 0 => 1
  | Nat.succ (Nat.succ n) =>
      involutionNumber (Nat.succ n) + Nat.succ n * involutionNumber n

def matchingPairCount : Nat -> Nat
  | 0 => 1
  | Nat.succ k => Nat.succ (k + k) * matchingPairCount k

def besselClosedFormula (n k : Nat) : Nat :=
  BEDC.Derived.StirlingFirstUp.factorialNat n /
    ((2 ^ k) * BEDC.Derived.StirlingFirstUp.factorialNat k *
      BEDC.Derived.StirlingFirstUp.factorialNat (n - (k + k)))

def hermiteUnsignedCoefficient (n k : Nat) : Nat :=
  besselNumber n k

def hermiteSign : Nat -> Int
  | 0 => 1
  | Nat.succ k => - hermiteSign k

def hermiteSignedCoefficient (n k : Nat) : Int :=
  hermiteSign k * Int.ofNat (besselNumber n k)

def besselNumberFn (n k : BHist) : BHist :=
  natToUnary (besselNumber (bwordLength n) (bwordLength k))

def besselRowSumFn (n : BHist) : BHist :=
  natToUnary (besselRowSum (bwordLength n))

def involutionNumberFn (n : BHist) : BHist :=
  natToUnary (involutionNumber (bwordLength n))

theorem besselNumber_zero_zero :
    besselNumber 0 0 = 1 := by
  rfl

theorem besselNumber_zero_succ (k : Nat) :
    besselNumber 0 (Nat.succ k) = 0 := by
  rfl

theorem besselNumber_zero_right (n : Nat) :
    besselNumber n 0 = 1 := by
  cases n <;> rfl

theorem besselNumber_one_succ (k : Nat) :
    besselNumber 1 (Nat.succ k) = 0 := by
  rfl

theorem besselNumber_recurrence (n k : Nat) :
    besselNumber (Nat.succ (Nat.succ n)) (Nat.succ k) =
      besselNumber (Nat.succ n) (Nat.succ k) +
        Nat.succ n * besselNumber n k := by
  rfl

theorem besselRowPrefix_zero (n : Nat) :
    besselRowPrefix n 0 = besselNumber n 0 := by
  rfl

theorem besselRowPrefix_succ (n k : Nat) :
    besselRowPrefix n (Nat.succ k) =
      besselRowPrefix n k + besselNumber n (Nat.succ k) := by
  rfl

private theorem add_pair_rebracket (a b c d : Nat) :
    (a + c) + (b + d) = (a + b) + (c + d) := by
  calc
    (a + c) + (b + d) = a + (c + (b + d)) :=
      Nat.add_assoc a c (b + d)
    _ = a + (b + (c + d)) := by
      rw [Nat.add_left_comm c b d]
    _ = (a + b) + (c + d) :=
      (Nat.add_assoc a b (c + d)).symm

theorem besselRowPrefix_pair_recurrence (n k : Nat) :
    besselRowPrefix (Nat.succ (Nat.succ n)) (Nat.succ k) =
      besselRowPrefix (Nat.succ n) (Nat.succ k) +
        Nat.succ n * besselRowPrefix n k := by
  induction k with
  | zero =>
      change
        1 + (besselNumber (Nat.succ n) 1 +
            Nat.succ n * besselNumber n 0) =
          (1 + besselNumber (Nat.succ n) 1) +
            Nat.succ n * besselNumber n 0
      exact (Nat.add_assoc 1 (besselNumber (Nat.succ n) 1)
        (Nat.succ n * besselNumber n 0)).symm
  | succ k ih =>
      change
        besselRowPrefix (Nat.succ (Nat.succ n)) (Nat.succ k) +
            (besselNumber (Nat.succ n) (Nat.succ (Nat.succ k)) +
              Nat.succ n * besselNumber n (Nat.succ k)) =
          (besselRowPrefix (Nat.succ n) (Nat.succ k) +
              besselNumber (Nat.succ n) (Nat.succ (Nat.succ k))) +
            Nat.succ n *
              (besselRowPrefix n k + besselNumber n (Nat.succ k))
      rw [ih]
      rw [Nat.mul_add]
      exact add_pair_rebracket
        (besselRowPrefix (Nat.succ n) (Nat.succ k))
        (besselNumber (Nat.succ n) (Nat.succ (Nat.succ k)))
        (Nat.succ n * besselRowPrefix n k)
        (Nat.succ n * besselNumber n (Nat.succ k))

theorem besselNumber_above_pair :
    ∀ n : Nat,
      (∀ extra : Nat, besselNumber n (Nat.succ (n + extra)) = 0) ∧
        (∀ extra : Nat,
          besselNumber (Nat.succ n) (Nat.succ (Nat.succ n + extra)) = 0)
  | 0 => by
      constructor
      · intro extra
        rfl
      · intro extra
        exact besselNumber_one_succ (Nat.succ extra)
  | Nat.succ n => by
      have ih := besselNumber_above_pair n
      constructor
      · intro extra
        exact ih.right extra
      · intro extra
        rw [show Nat.succ (Nat.succ (Nat.succ n) + extra) =
            Nat.succ (Nat.succ (Nat.succ n + extra)) by
          rw [Nat.succ_add]]
        change
          besselNumber (Nat.succ n) (Nat.succ (Nat.succ (Nat.succ n + extra))) +
              Nat.succ n * besselNumber n (Nat.succ (Nat.succ n + extra)) = 0
        have rightZero :
            besselNumber (Nat.succ n)
              (Nat.succ (Nat.succ (Nat.succ n + extra))) = 0 := by
          have raw := ih.right (Nat.succ extra)
          rw [Nat.add_succ] at raw
          exact raw
        have leftZero :
            besselNumber n (Nat.succ (Nat.succ n + extra)) = 0 := by
          have raw := ih.left (Nat.succ extra)
          rw [Nat.add_succ] at raw
          rw [Nat.succ_add]
          exact raw
        rw [rightZero, leftZero]
        rfl

theorem besselNumber_above (n extra : Nat) :
    besselNumber n (Nat.succ (n + extra)) = 0 :=
  (besselNumber_above_pair n).left extra

theorem besselRowPrefix_above_self (n : Nat) :
    besselRowPrefix n (Nat.succ n) = besselRowPrefix n n := by
  change besselRowPrefix n n + besselNumber n (Nat.succ n) =
    besselRowPrefix n n
  rw [besselNumber_above n 0]
  exact Nat.add_zero (besselRowPrefix n n)

theorem besselRowSum_recurrence (n : Nat) :
    besselRowSum (Nat.succ (Nat.succ n)) =
      besselRowSum (Nat.succ n) + Nat.succ n * besselRowSum n := by
  unfold besselRowSum
  rw [besselRowPrefix_pair_recurrence n (Nat.succ n)]
  rw [besselRowPrefix_above_self (Nat.succ n)]
  rw [besselRowPrefix_above_self n]

theorem involutionNumber_zero :
    involutionNumber 0 = 1 := by
  rfl

theorem involutionNumber_one :
    involutionNumber 1 = 1 := by
  rfl

theorem involutionNumber_recurrence (n : Nat) :
    involutionNumber (Nat.succ (Nat.succ n)) =
      involutionNumber (Nat.succ n) + Nat.succ n * involutionNumber n := by
  rfl

theorem besselRowSum_eq_involutionNumber_pair :
    ∀ n : Nat,
      besselRowSum n = involutionNumber n ∧
        besselRowSum (Nat.succ n) = involutionNumber (Nat.succ n)
  | 0 => by
      constructor
      · rfl
      · rfl
  | Nat.succ n => by
      have ih := besselRowSum_eq_involutionNumber_pair n
      constructor
      · exact ih.right
      · rw [besselRowSum_recurrence n]
        rw [involutionNumber_recurrence n]
        rw [ih.left]
        rw [ih.right]

theorem besselRowSum_eq_involutionNumber (n : Nat) :
    besselRowSum n = involutionNumber n :=
  (besselRowSum_eq_involutionNumber_pair n).left

theorem besselNumberFn_unary_result (n k : BHist) :
    BEDC.FKernel.Unary.UnaryHistory (besselNumberFn n k) := by
  unfold besselNumberFn
  exact natToUnary_unary _

theorem besselRowSumFn_unary_result (n : BHist) :
    BEDC.FKernel.Unary.UnaryHistory (besselRowSumFn n) := by
  unfold besselRowSumFn
  exact natToUnary_unary _

theorem involutionNumberFn_unary_result (n : BHist) :
    BEDC.FKernel.Unary.UnaryHistory (involutionNumberFn n) := by
  unfold involutionNumberFn
  exact natToUnary_unary _

theorem besselNumberFn_recurrence_natToUnary (n k : Nat) :
    besselNumberFn (natToUnary (Nat.succ (Nat.succ n))) (natToUnary (Nat.succ k)) =
      natToUnary
        (besselNumber (Nat.succ n) (Nat.succ k) +
          Nat.succ n * besselNumber n k) := by
  unfold besselNumberFn
  rw [natToUnary_length, natToUnary_length]
  rfl

theorem besselRowSumFn_eq_involutionNumberFn_natToUnary (n : Nat) :
    besselRowSumFn (natToUnary n) = involutionNumberFn (natToUnary n) := by
  unfold besselRowSumFn involutionNumberFn
  rw [natToUnary_length]
  rw [besselRowSum_eq_involutionNumber n]

theorem matchingPairCount_zero :
    matchingPairCount 0 = 1 := by
  rfl

theorem matchingPairCount_succ (k : Nat) :
    matchingPairCount (Nat.succ k) =
      Nat.succ (k + k) * matchingPairCount k := by
  rfl

theorem besselClosedFormula_definition (n k : Nat) :
    besselClosedFormula n k =
      BEDC.Derived.StirlingFirstUp.factorialNat n /
        ((2 ^ k) * BEDC.Derived.StirlingFirstUp.factorialNat k *
          BEDC.Derived.StirlingFirstUp.factorialNat (n - (k + k))) := by
  rfl

theorem hermiteUnsignedCoefficient_matches_besselNumber (n k : Nat) :
    hermiteUnsignedCoefficient n k = besselNumber n k := by
  rfl

theorem hermiteSignedCoefficient_definition (n k : Nat) :
    hermiteSignedCoefficient n k =
      hermiteSign k * Int.ofNat (besselNumber n k) := by
  rfl

theorem BesselNumberUp_constructive_export :
    (∀ n k : Nat,
      besselNumber (Nat.succ (Nat.succ n)) (Nat.succ k) =
        besselNumber (Nat.succ n) (Nat.succ k) +
          Nat.succ n * besselNumber n k) ∧
      (∀ n : Nat,
        besselRowSum (Nat.succ (Nat.succ n)) =
          besselRowSum (Nat.succ n) + Nat.succ n * besselRowSum n) ∧
      (∀ n : Nat, besselRowSum n = involutionNumber n) ∧
      (∀ n k : Nat, hermiteUnsignedCoefficient n k = besselNumber n k) := by
  constructor
  · intro n k
    exact besselNumber_recurrence n k
  · constructor
    · intro n
      exact besselRowSum_recurrence n
    · constructor
      · intro n
        exact besselRowSum_eq_involutionNumber n
      · intro n k
        exact hermiteUnsignedCoefficient_matches_besselNumber n k

end BEDC.Derived.BesselNumberUp
