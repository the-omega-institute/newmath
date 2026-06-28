import BEDC.Algebra.FiniteFold
import BEDC.Derived.FactorialUp
import BEDC.Derived.StirlingFirstUp

namespace BEDC.Derived.StirlingCycleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.FactorialUp
open BEDC.Derived.IntUp (natToUnary natToUnary_unary natToUnary_length natMulFn)

abbrev UnaryOne : BHist := BHist.e1 BHist.Empty

-- 无符号第一类 Stirling 数, 即按轮换数计数的 cycle number.
def stirlingCycle : Nat -> Nat -> Nat
  | 0, 0 => 1
  | 0, Nat.succ _ => 0
  | Nat.succ _, 0 => 0
  | Nat.succ n, Nat.succ k =>
      n * stirlingCycle n (Nat.succ k) + stirlingCycle n k

def stirlingCyclePrefix (n : Nat) : Nat -> Nat
  | 0 => stirlingCycle n 0
  | Nat.succ k => stirlingCyclePrefix n k + stirlingCycle n (Nat.succ k)

def stirlingCycleRowSum (n : Nat) : Nat :=
  stirlingCyclePrefix n n

abbrev factorialNat : Nat -> Nat :=
  BEDC.Derived.StirlingFirstUp.factorialNat

def stirlingCycleFn (n k : BHist) : BHist :=
  natToUnary (stirlingCycle (bwordLength n) (bwordLength k))

def stirlingCycleRowSumFn (n : BHist) : BHist :=
  natToUnary (stirlingCycleRowSum (bwordLength n))

-- `risingFactorialCoeff n k` 是依次乘入前 `n` 个线性因子
-- `x + 0, x + 1, ..., x + (n - 1)` 后的 `x^k` 系数.
def risingFactorialCoeff : Nat -> Nat -> Nat
  | 0, 0 => 1
  | 0, Nat.succ _ => 0
  | Nat.succ n, 0 => n * risingFactorialCoeff n 0
  | Nat.succ n, Nat.succ k =>
      n * risingFactorialCoeff n (Nat.succ k) + risingFactorialCoeff n k

def natPow (x : Nat) : Nat -> Nat
  | 0 => 1
  | Nat.succ k => natPow x k * x

def risingFactorialValue (x : Nat) : Nat -> Nat
  | 0 => 1
  | Nat.succ n => risingFactorialValue x n * (x + n)

-- 有限前缀 $\sum_{j \le k} c(n,j)x^j$, 用 fuel 递归承载索引。
def stirlingCyclePowerSumPrefix (x n : Nat) : Nat -> Nat
  | 0 => stirlingCycle n 0 * natPow x 0
  | Nat.succ k =>
      stirlingCyclePowerSumPrefix x n k +
        stirlingCycle n (Nat.succ k) * natPow x (Nat.succ k)

def stirlingCyclePowerSum (x n : Nat) : Nat :=
  stirlingCyclePowerSumPrefix x n n

theorem stirlingCycle_zero_zero :
    stirlingCycle 0 0 = 1 := by
  rfl

theorem stirlingCycle_zero_succ (k : Nat) :
    stirlingCycle 0 (Nat.succ k) = 0 := by
  rfl

theorem stirlingCycle_succ_zero (n : Nat) :
    stirlingCycle (Nat.succ n) 0 = 0 := by
  rfl

theorem stirlingCycle_zero_boundary (n : Nat) :
    stirlingCycle n 0 = if n = 0 then 1 else 0 := by
  cases n with
  | zero =>
      rfl
  | succ _ =>
      rfl

theorem stirlingCycle_recurrence (n k : Nat) :
    stirlingCycle (Nat.succ n) (Nat.succ k) =
      n * stirlingCycle n (Nat.succ k) + stirlingCycle n k := by
  rfl

theorem stirlingCycle_self_and_above :
    ∀ n : Nat, stirlingCycle n n = 1 ∧
      ∀ extra : Nat, stirlingCycle n (Nat.succ (n + extra)) = 0 := by
  intro n
  induction n with
  | zero =>
      constructor
      · rfl
      · intro extra
        rfl
  | succ n ih =>
      constructor
      · change n * stirlingCycle n (Nat.succ n) + stirlingCycle n n = 1
        rw [ih.right 0, ih.left]
        rfl
      · intro extra
        change n * stirlingCycle n (Nat.succ (Nat.succ n + extra)) +
          stirlingCycle n (Nat.succ n + extra) = 0
        rw [Nat.succ_add]
        rw [ih.right extra]
        rw [show Nat.succ (Nat.succ (n + extra)) =
            Nat.succ (n + Nat.succ extra) by
          rw [Nat.add_succ]]
        rw [ih.right (Nat.succ extra)]
        rfl

theorem stirlingCycle_self (n : Nat) :
    stirlingCycle n n = 1 :=
  (stirlingCycle_self_and_above n).left

theorem stirlingCycle_above (n extra : Nat) :
    stirlingCycle n (Nat.succ (n + extra)) = 0 :=
  (stirlingCycle_self_and_above n).right extra

theorem stirlingCycle_zero_column_mul_index (n : Nat) :
    n * stirlingCycle n 0 = 0 := by
  cases n with
  | zero =>
      rfl
  | succ _ =>
      rfl

theorem stirlingCyclePrefix_succ (n k : Nat) :
    stirlingCyclePrefix n (Nat.succ k) =
      stirlingCyclePrefix n k + stirlingCycle n (Nat.succ k) := by
  rfl

theorem stirlingCycle_succ_prefix_recurrence (n k : Nat) :
    stirlingCyclePrefix (Nat.succ n) (Nat.succ k) =
      n * stirlingCyclePrefix n (Nat.succ k) + stirlingCyclePrefix n k := by
  induction k with
  | zero =>
      change 0 + (n * stirlingCycle n 1 + stirlingCycle n 0) =
        n * (stirlingCycle n 0 + stirlingCycle n 1) + stirlingCycle n 0
      rw [Nat.zero_add]
      rw [Nat.mul_add]
      rw [stirlingCycle_zero_column_mul_index n]
      rw [Nat.zero_add]
  | succ k ih =>
      change
        stirlingCyclePrefix (Nat.succ n) (Nat.succ k) +
            (n * stirlingCycle n (Nat.succ (Nat.succ k)) +
              stirlingCycle n (Nat.succ k)) =
          n * (stirlingCyclePrefix n (Nat.succ k) +
              stirlingCycle n (Nat.succ (Nat.succ k))) +
            (stirlingCyclePrefix n k + stirlingCycle n (Nat.succ k))
      rw [ih]
      rw [Nat.mul_add]
      rw [Nat.add_assoc]
      rw [Nat.add_assoc]
      rw [Nat.add_left_comm (stirlingCyclePrefix n k)
        (n * stirlingCycle n (Nat.succ (Nat.succ k)))
        (stirlingCycle n (Nat.succ k))]

theorem stirlingCycleRowSum_succ (n : Nat) :
    stirlingCycleRowSum (Nat.succ n) =
      Nat.succ n * stirlingCycleRowSum n := by
  unfold stirlingCycleRowSum
  rw [stirlingCycle_succ_prefix_recurrence n n]
  rw [stirlingCyclePrefix_succ]
  rw [stirlingCycle_above n 0]
  rw [Nat.add_zero]
  rw [Nat.succ_mul]

theorem stirlingCycleRowSum_eq_factorial (n : Nat) :
    stirlingCycleRowSum n = factorialNat n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [stirlingCycleRowSum_succ n]
      change Nat.succ n * stirlingCycleRowSum n = Nat.succ n * factorialNat n
      rw [ih]

theorem factorialNat_eq_factorialCount (n : Nat) :
    factorialNat n = bwordLength (natFactorialFn (natToUnary n)) := by
  rw [BEDC.Derived.StirlingFirstUp.natFactorialFn_natToUnary n]
  rw [natToUnary_length]

theorem stirlingCycleRowSum_eq_factorialCount (n : Nat) :
    stirlingCycleRowSum n = bwordLength (natFactorialFn (natToUnary n)) := by
  rw [stirlingCycleRowSum_eq_factorial]
  exact factorialNat_eq_factorialCount n

theorem risingFactorialCoeff_zero_zero :
    risingFactorialCoeff 0 0 = 1 := by
  rfl

theorem risingFactorialCoeff_zero_succ (k : Nat) :
    risingFactorialCoeff 0 (Nat.succ k) = 0 := by
  rfl

theorem risingFactorialCoeff_step_zero (n : Nat) :
    risingFactorialCoeff (Nat.succ n) 0 =
      n * risingFactorialCoeff n 0 := by
  rfl

theorem risingFactorialCoeff_step_succ (n k : Nat) :
    risingFactorialCoeff (Nat.succ n) (Nat.succ k) =
      n * risingFactorialCoeff n (Nat.succ k) +
        risingFactorialCoeff n k := by
  rfl

private theorem nat_mul_assoc_clean (a b c : Nat) :
    (a * b) * c = a * (b * c) := by
  induction c with
  | zero =>
      rfl
  | succ c ih =>
      calc
        (a * b) * Nat.succ c = (a * b) * c + a * b := Nat.mul_succ (a * b) c
        _ = a * (b * c) + a * b := congrArg (fun t => t + a * b) ih
        _ = a * (b * c + b) := (Nat.mul_add a (b * c) b).symm
        _ = a * (b * Nat.succ c) := congrArg (fun t => a * t) (Nat.mul_succ b c).symm

private theorem nat_add_mul_clean (a b c : Nat) :
    (a + b) * c = a * c + b * c := by
  induction c with
  | zero =>
      rw [Nat.mul_zero, Nat.mul_zero, Nat.mul_zero]
  | succ c ih =>
      calc
        (a + b) * Nat.succ c =
            (a + b) * c + (a + b) := Nat.mul_succ (a + b) c
        _ = (a * c + b * c) + (a + b) :=
          congrArg (fun t => t + (a + b)) ih
        _ = a * c + (b * c + (a + b)) :=
          Nat.add_assoc (a * c) (b * c) (a + b)
        _ = a * c + ((b * c + a) + b) :=
          congrArg (fun t => a * c + t) (Nat.add_assoc (b * c) a b).symm
        _ = a * c + ((a + b * c) + b) :=
          congrArg (fun t => a * c + (t + b)) (Nat.add_comm (b * c) a)
        _ = a * c + (a + (b * c + b)) :=
          congrArg (fun t => a * c + t) (Nat.add_assoc a (b * c) b)
        _ = (a * c + a) + (b * c + b) :=
          (Nat.add_assoc (a * c) a (b * c + b)).symm
        _ = a * Nat.succ c + (b * c + b) :=
          congrArg (fun t => t + (b * c + b)) (Nat.mul_succ a c).symm
        _ = a * Nat.succ c + b * Nat.succ c :=
          congrArg (fun t => a * Nat.succ c + t) (Nat.mul_succ b c).symm

private theorem nat_add_four_acbd_grouped (a b c d : Nat) :
    a + b + (c + d) = (a + c) + (b + d) := by
  calc
    a + b + (c + d) = a + (b + (c + d)) := Nat.add_assoc a b (c + d)
    _ = a + ((b + c) + d) :=
      congrArg (fun t => a + t) (Nat.add_assoc b c d).symm
    _ = a + ((c + b) + d) :=
      congrArg (fun t => a + (t + d)) (Nat.add_comm b c)
    _ = a + (c + (b + d)) :=
      congrArg (fun t => a + t) (Nat.add_assoc c b d)
    _ = (a + c) + (b + d) := (Nat.add_assoc a c (b + d)).symm

private theorem nat_mul_rotate_clean (a q x : Nat) :
    a * (q * x) = x * (a * q) := by
  rw [← nat_mul_assoc_clean]
  rw [Nat.mul_comm (a * q) x]

private theorem nat_power_sum_step_clean (x n P A B Q : Nat) :
    n * (P + A * Q) + x * P + (n * B + A) * (Q * x) =
      n * (P + A * Q + B * (Q * x)) + x * (P + A * Q) := by
  calc
    n * (P + A * Q) + x * P + (n * B + A) * (Q * x)
        = n * (P + A * Q) + x * P + ((n * B) * (Q * x) + A * (Q * x)) := by
          rw [nat_add_mul_clean]
    _ = n * (P + A * Q) + x * P + (n * (B * (Q * x)) + A * (Q * x)) := by
          rw [nat_mul_assoc_clean]
    _ = (n * (P + A * Q) + n * (B * (Q * x))) + (x * P + A * (Q * x)) := by
          exact nat_add_four_acbd_grouped (n * (P + A * Q)) (x * P)
            (n * (B * (Q * x))) (A * (Q * x))
    _ = n * ((P + A * Q) + B * (Q * x)) + (x * P + A * (Q * x)) := by
          rw [← Nat.mul_add n (P + A * Q) (B * (Q * x))]
    _ = n * ((P + A * Q) + B * (Q * x)) + (x * P + x * (A * Q)) := by
          rw [nat_mul_rotate_clean A Q x]
    _ = n * ((P + A * Q) + B * (Q * x)) + x * (P + A * Q) := by
          rw [← Nat.mul_add x P (A * Q)]
    _ = n * (P + A * Q + B * (Q * x)) + x * (P + A * Q) := by
          rfl

theorem natPow_succ (x k : Nat) :
    natPow x (Nat.succ k) = natPow x k * x := by
  rfl

theorem risingFactorialValue_succ (x n : Nat) :
    risingFactorialValue x (Nat.succ n) =
      risingFactorialValue x n * (x + n) := by
  rfl

theorem stirlingCyclePowerSumPrefix_succ (x n k : Nat) :
    stirlingCyclePowerSumPrefix x n (Nat.succ k) =
      stirlingCyclePowerSumPrefix x n k +
        stirlingCycle n (Nat.succ k) * natPow x (Nat.succ k) := by
  rfl

theorem stirlingCyclePowerSumPrefix_above (x n : Nat) :
    stirlingCyclePowerSumPrefix x n (Nat.succ n) =
      stirlingCyclePowerSumPrefix x n n := by
  rw [stirlingCyclePowerSumPrefix_succ]
  rw [stirlingCycle_above n 0]
  rw [Nat.zero_mul]
  rw [Nat.add_zero]

theorem stirlingCyclePowerSumPrefix_succ_row_recurrence (x n k : Nat) :
    stirlingCyclePowerSumPrefix x (Nat.succ n) (Nat.succ k) =
      n * stirlingCyclePowerSumPrefix x n (Nat.succ k) +
        x * stirlingCyclePowerSumPrefix x n k := by
  induction k with
  | zero =>
      change 0 * natPow x 0 +
          (n * stirlingCycle n 1 + stirlingCycle n 0) * (natPow x 0 * x) =
        n * (stirlingCycle n 0 * natPow x 0 + stirlingCycle n 1 * (natPow x 0 * x)) +
          x * (stirlingCycle n 0 * natPow x 0)
      cases n with
      | zero =>
          change 0 * 1 + (0 * 0 + 1) * (1 * x) =
            0 * (1 * 1 + 0 * (1 * x)) + x * (1 * 1)
          rw [Nat.zero_mul]
          rw [Nat.zero_add]
          rw [Nat.one_mul]
          rw [Nat.one_mul]
          rw [Nat.mul_one]
          rw [Nat.zero_mul]
          rw [Nat.zero_add]
          rw [Nat.mul_one]
      | succ n =>
          change 0 * 1 +
              (Nat.succ n * stirlingCycle (Nat.succ n) 1 + 0) * (1 * x) =
            Nat.succ n * (0 * 1 + stirlingCycle (Nat.succ n) 1 * (1 * x)) +
              x * (0 * 1)
          rw [Nat.zero_mul]
          rw [Nat.zero_add]
          rw [Nat.add_zero]
          rw [Nat.one_mul]
          rw [Nat.zero_add]
          rw [Nat.mul_zero]
          rw [Nat.add_zero]
          rw [nat_mul_assoc_clean]
  | succ k ih =>
      change
        stirlingCyclePowerSumPrefix x (Nat.succ n) (Nat.succ k) +
            (n * stirlingCycle n (Nat.succ (Nat.succ k)) +
              stirlingCycle n (Nat.succ k)) * (natPow x (Nat.succ k) * x) =
          n * (stirlingCyclePowerSumPrefix x n (Nat.succ k) +
              stirlingCycle n (Nat.succ (Nat.succ k)) *
                (natPow x (Nat.succ k) * x)) +
            x * stirlingCyclePowerSumPrefix x n (Nat.succ k)
      rw [ih]
      rw [stirlingCyclePowerSumPrefix_succ]
      exact nat_power_sum_step_clean x n (stirlingCyclePowerSumPrefix x n k)
        (stirlingCycle n (Nat.succ k))
        (stirlingCycle n (Nat.succ (Nat.succ k)))
        (natPow x (Nat.succ k))

theorem stirlingCyclePowerSum_succ (x n : Nat) :
    stirlingCyclePowerSum x (Nat.succ n) =
      stirlingCyclePowerSum x n * (x + n) := by
  unfold stirlingCyclePowerSum
  rw [stirlingCyclePowerSumPrefix_succ_row_recurrence x n n]
  rw [stirlingCyclePowerSumPrefix_above]
  rw [Nat.mul_comm (stirlingCyclePowerSumPrefix x n n) (x + n)]
  rw [nat_add_mul_clean]
  rw [Nat.add_comm]

theorem risingFactorialCoeff_eq_stirlingCycle :
    ∀ n k : Nat, risingFactorialCoeff n k = stirlingCycle n k := by
  intro n
  induction n with
  | zero =>
      intro k
      cases k with
      | zero =>
          rfl
      | succ _ =>
          rfl
  | succ n ih =>
      intro k
      cases k with
      | zero =>
          change n * risingFactorialCoeff n 0 = stirlingCycle (Nat.succ n) 0
          rw [ih 0]
          rw [stirlingCycle_succ_zero n]
          exact stirlingCycle_zero_column_mul_index n
      | succ k =>
          change
            n * risingFactorialCoeff n (Nat.succ k) + risingFactorialCoeff n k =
              n * stirlingCycle n (Nat.succ k) + stirlingCycle n k
          rw [ih (Nat.succ k)]
          rw [ih k]

theorem stirlingCycle_expands_rising_factorial_coeff (n k : Nat) :
    risingFactorialCoeff n k = stirlingCycle n k :=
  risingFactorialCoeff_eq_stirlingCycle n k

theorem stirlingCyclePowerSum_eq_risingFactorialValue (x n : Nat) :
    stirlingCyclePowerSum x n = risingFactorialValue x n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [stirlingCyclePowerSum_succ]
      rw [ih]
      rfl

theorem risingFactorialValue_expansion (x n : Nat) :
    risingFactorialValue x n = stirlingCyclePowerSum x n :=
  (stirlingCyclePowerSum_eq_risingFactorialValue x n).symm

theorem stirlingCycleFn_unary_result (n k : BHist) :
    UnaryHistory (stirlingCycleFn n k) := by
  unfold stirlingCycleFn
  exact natToUnary_unary _

theorem stirlingCycleRowSumFn_unary_result (n : BHist) :
    UnaryHistory (stirlingCycleRowSumFn n) := by
  unfold stirlingCycleRowSumFn
  exact natToUnary_unary _

theorem stirlingCycleFn_recurrence_natToUnary (n k : Nat) :
    stirlingCycleFn (natToUnary (Nat.succ n)) (natToUnary (Nat.succ k)) =
      natToUnary
        (n * stirlingCycle n (Nat.succ k) + stirlingCycle n k) := by
  unfold stirlingCycleFn
  rw [natToUnary_length, natToUnary_length]
  rfl

theorem stirlingCycleFn_zero_boundary (n : Nat) :
    stirlingCycleFn (natToUnary n) BHist.Empty =
      if n = 0 then UnaryOne else BHist.Empty := by
  unfold stirlingCycleFn
  rw [natToUnary_length]
  cases n with
  | zero =>
      rfl
  | succ _ =>
      rfl

theorem stirlingCycleFn_self (n : Nat) :
    stirlingCycleFn (natToUnary n) (natToUnary n) = UnaryOne := by
  unfold stirlingCycleFn
  rw [natToUnary_length]
  rw [stirlingCycle_self]
  rfl

theorem stirlingCycleRowSumFn_natFactorialFn (n : Nat) :
    stirlingCycleRowSumFn (natToUnary n) = natFactorialFn (natToUnary n) := by
  unfold stirlingCycleRowSumFn
  rw [natToUnary_length]
  rw [stirlingCycleRowSum_eq_factorial]
  rw [BEDC.Derived.StirlingFirstUp.natFactorialFn_natToUnary n]

theorem StirlingCycleUp_constructive_export :
    (∀ n k : Nat,
      stirlingCycle (Nat.succ n) (Nat.succ k) =
        n * stirlingCycle n (Nat.succ k) + stirlingCycle n k) ∧
      (∀ n : Nat, stirlingCycleRowSum n = factorialNat n) ∧
      (∀ n : Nat,
        stirlingCycleRowSum n = bwordLength (natFactorialFn (natToUnary n))) ∧
      (∀ n : Nat,
        stirlingCycleRowSumFn (natToUnary n) = natFactorialFn (natToUnary n)) ∧
      (∀ n k : Nat, risingFactorialCoeff n k = stirlingCycle n k) ∧
      (∀ x n : Nat, risingFactorialValue x n = stirlingCyclePowerSum x n) := by
  constructor
  · intro n k
    exact stirlingCycle_recurrence n k
  · constructor
    · intro n
      exact stirlingCycleRowSum_eq_factorial n
    · constructor
      · intro n
        exact stirlingCycleRowSum_eq_factorialCount n
      · constructor
        · intro n
          exact stirlingCycleRowSumFn_natFactorialFn n
        · constructor
          · intro n k
            exact risingFactorialCoeff_eq_stirlingCycle n k
          · intro x n
            exact risingFactorialValue_expansion x n

end BEDC.Derived.StirlingCycleUp
