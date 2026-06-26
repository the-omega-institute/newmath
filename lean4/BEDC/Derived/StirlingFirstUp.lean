import BEDC.Derived.FactorialUp

namespace BEDC.Derived.StirlingFirstUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.FactorialUp
open BEDC.Derived.IntUp (natToUnary natToUnary_unary natToUnary_length natMulFn)

abbrev UnaryOne : BHist := BHist.e1 BHist.Empty

-- 无符号第一类 Stirling 数。
def stirlingFirst : Nat -> Nat -> Nat
  | 0, 0 => 1
  | 0, Nat.succ _ => 0
  | Nat.succ _, 0 => 0
  | Nat.succ n, Nat.succ k =>
      n * stirlingFirst n (Nat.succ k) + stirlingFirst n k

def stirlingFirstPrefix (n : Nat) : Nat -> Nat
  | 0 => stirlingFirst n 0
  | Nat.succ k => stirlingFirstPrefix n k + stirlingFirst n (Nat.succ k)

def stirlingFirstRowSum (n : Nat) : Nat :=
  stirlingFirstPrefix n n

def factorialNat : Nat -> Nat
  | 0 => 1
  | Nat.succ n => Nat.succ n * factorialNat n

def stirlingFirstFn (n k : BHist) : BHist :=
  natToUnary (stirlingFirst (bwordLength n) (bwordLength k))

def stirlingFirstRowSumFn (n : BHist) : BHist :=
  natToUnary (stirlingFirstRowSum (bwordLength n))

theorem stirlingFirst_zero_zero :
    stirlingFirst 0 0 = 1 := by
  rfl

theorem stirlingFirst_zero_succ (k : Nat) :
    stirlingFirst 0 (Nat.succ k) = 0 := by
  rfl

theorem stirlingFirst_succ_zero (n : Nat) :
    stirlingFirst (Nat.succ n) 0 = 0 := by
  rfl

theorem stirlingFirst_zero_boundary (n : Nat) :
    stirlingFirst n 0 = if n = 0 then 1 else 0 := by
  cases n with
  | zero =>
      rfl
  | succ _ =>
      rfl

theorem stirlingFirst_recurrence (n k : Nat) :
    stirlingFirst (Nat.succ n) (Nat.succ k) =
      n * stirlingFirst n (Nat.succ k) + stirlingFirst n k := by
  rfl

theorem stirlingFirst_self_and_above :
    ∀ n : Nat, stirlingFirst n n = 1 ∧
      ∀ extra : Nat, stirlingFirst n (Nat.succ (n + extra)) = 0 := by
  intro n
  induction n with
  | zero =>
      constructor
      · rfl
      · intro extra
        rfl
  | succ n ih =>
      constructor
      · change n * stirlingFirst n (Nat.succ n) + stirlingFirst n n = 1
        rw [ih.right 0, ih.left]
        rfl
      · intro extra
        change n * stirlingFirst n (Nat.succ (Nat.succ n + extra)) +
          stirlingFirst n (Nat.succ n + extra) = 0
        rw [Nat.succ_add]
        rw [ih.right extra]
        rw [show Nat.succ (Nat.succ (n + extra)) =
            Nat.succ (n + Nat.succ extra) by
          rw [Nat.add_succ]]
        rw [ih.right (Nat.succ extra)]
        rfl

theorem stirlingFirst_self (n : Nat) :
    stirlingFirst n n = 1 :=
  (stirlingFirst_self_and_above n).left

theorem stirlingFirst_above (n extra : Nat) :
    stirlingFirst n (Nat.succ (n + extra)) = 0 :=
  (stirlingFirst_self_and_above n).right extra

theorem stirlingFirst_zero_column_mul_index (n : Nat) :
    n * stirlingFirst n 0 = 0 := by
  cases n with
  | zero =>
      rfl
  | succ _ =>
      rfl

theorem stirlingFirstPrefix_succ (n k : Nat) :
    stirlingFirstPrefix n (Nat.succ k) =
      stirlingFirstPrefix n k + stirlingFirst n (Nat.succ k) := by
  rfl

theorem stirlingFirst_succ_prefix_recurrence (n k : Nat) :
    stirlingFirstPrefix (Nat.succ n) (Nat.succ k) =
      n * stirlingFirstPrefix n (Nat.succ k) + stirlingFirstPrefix n k := by
  induction k with
  | zero =>
      change 0 + (n * stirlingFirst n 1 + stirlingFirst n 0) =
        n * (stirlingFirst n 0 + stirlingFirst n 1) + stirlingFirst n 0
      rw [Nat.zero_add]
      rw [Nat.mul_add]
      rw [stirlingFirst_zero_column_mul_index n]
      rw [Nat.zero_add]
  | succ k ih =>
      change
        stirlingFirstPrefix (Nat.succ n) (Nat.succ k) +
            (n * stirlingFirst n (Nat.succ (Nat.succ k)) +
              stirlingFirst n (Nat.succ k)) =
          n * (stirlingFirstPrefix n (Nat.succ k) +
              stirlingFirst n (Nat.succ (Nat.succ k))) +
            (stirlingFirstPrefix n k + stirlingFirst n (Nat.succ k))
      rw [ih]
      rw [Nat.mul_add]
      rw [Nat.add_assoc]
      rw [Nat.add_assoc]
      rw [Nat.add_left_comm (stirlingFirstPrefix n k)
        (n * stirlingFirst n (Nat.succ (Nat.succ k)))
        (stirlingFirst n (Nat.succ k))]

theorem stirlingFirstRowSum_succ (n : Nat) :
    stirlingFirstRowSum (Nat.succ n) =
      Nat.succ n * stirlingFirstRowSum n := by
  unfold stirlingFirstRowSum
  rw [stirlingFirst_succ_prefix_recurrence n n]
  rw [stirlingFirstPrefix_succ]
  rw [stirlingFirst_above n 0]
  rw [Nat.add_zero]
  rw [Nat.succ_mul]

theorem stirlingFirstRowSum_eq_factorial (n : Nat) :
    stirlingFirstRowSum n = factorialNat n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [stirlingFirstRowSum_succ n]
      change Nat.succ n * stirlingFirstRowSum n = Nat.succ n * factorialNat n
      rw [ih]

theorem natToUnary_append (m n : Nat) :
    append (natToUnary m) (natToUnary n) = natToUnary (m + n) := by
  induction n with
  | zero =>
      rw [Nat.add_zero]
      rfl
  | succ n ih =>
      change BHist.e1 (append (natToUnary m) (natToUnary n)) =
        natToUnary (m + Nat.succ n)
      rw [ih]
      rw [Nat.add_succ]
      rfl

theorem natMulFn_natToUnary (m n : Nat) :
    natMulFn (natToUnary m) (natToUnary n) = natToUnary (m * n) := by
  induction n with
  | zero =>
      rw [Nat.mul_zero]
      rfl
  | succ n ih =>
      change append (natMulFn (natToUnary m) (natToUnary n)) (natToUnary m) =
        natToUnary (m * Nat.succ n)
      rw [ih]
      rw [natToUnary_append]
      rw [Nat.mul_succ]

theorem natFactorialFn_natToUnary (n : Nat) :
    natFactorialFn (natToUnary n) = natToUnary (factorialNat n) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change natMulFn (natToUnary (Nat.succ n)) (natFactorialFn (natToUnary n)) =
        natToUnary (Nat.succ n * factorialNat n)
      rw [ih]
      rw [natMulFn_natToUnary]

theorem stirlingFirstFn_unary_result (n k : BHist) :
    UnaryHistory (stirlingFirstFn n k) := by
  unfold stirlingFirstFn
  exact natToUnary_unary _

theorem stirlingFirstRowSumFn_unary_result (n : BHist) :
    UnaryHistory (stirlingFirstRowSumFn n) := by
  unfold stirlingFirstRowSumFn
  exact natToUnary_unary _

theorem stirlingFirstFn_recurrence_natToUnary (n k : Nat) :
    stirlingFirstFn (natToUnary (Nat.succ n)) (natToUnary (Nat.succ k)) =
      natToUnary
        (n * stirlingFirst n (Nat.succ k) + stirlingFirst n k) := by
  unfold stirlingFirstFn
  rw [natToUnary_length, natToUnary_length]
  rfl

theorem stirlingFirstFn_zero_boundary (n : Nat) :
    stirlingFirstFn (natToUnary n) BHist.Empty =
      if n = 0 then UnaryOne else BHist.Empty := by
  unfold stirlingFirstFn
  rw [natToUnary_length]
  cases n with
  | zero =>
      rfl
  | succ _ =>
      rfl

theorem stirlingFirstFn_self (n : Nat) :
    stirlingFirstFn (natToUnary n) (natToUnary n) = UnaryOne := by
  unfold stirlingFirstFn
  rw [natToUnary_length]
  rw [stirlingFirst_self]
  rfl

theorem stirlingFirstRowSumFn_natFactorialFn (n : Nat) :
    stirlingFirstRowSumFn (natToUnary n) = natFactorialFn (natToUnary n) := by
  unfold stirlingFirstRowSumFn
  rw [natToUnary_length]
  rw [stirlingFirstRowSum_eq_factorial]
  rw [natFactorialFn_natToUnary]

end BEDC.Derived.StirlingFirstUp
