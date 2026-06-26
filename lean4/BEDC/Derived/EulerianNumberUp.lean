import BEDC.Derived.BinomialIdentitiesUp
import BEDC.Derived.StirlingFirstUp
import BEDC.Derived.StirlingUp

namespace BEDC.Derived.EulerianNumberUp

open BEDC.FKernel.Hist
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.IntUp (natToUnary natToUnary_unary natToUnary_length)

abbrev C (n k : Nat) : Nat :=
  BEDC.Derived.BinomialIdentitiesUp.C n k

-- Eulerian 数按升降数递归闭生成；第二个指标超过可见行时自然落到零。
def eulerianNumber : Nat -> Nat -> Nat
  | 0, 0 => 1
  | 0, Nat.succ _ => 0
  | Nat.succ _, 0 => 1
  | Nat.succ n, Nat.succ k =>
      Nat.succ (Nat.succ k) * eulerianNumber n (Nat.succ k) +
        (n - k) * eulerianNumber n k

def eulerianPrefix (n : Nat) : Nat -> Nat
  | 0 => eulerianNumber n 0
  | Nat.succ k => eulerianPrefix n k + eulerianNumber n (Nat.succ k)

def eulerianRowSum (n : Nat) : Nat :=
  eulerianPrefix n n

def eulerianNumberFn (n k : BHist) : BHist :=
  natToUnary (eulerianNumber (bwordLength n) (bwordLength k))

def eulerianRowSumFn (n : BHist) : BHist :=
  natToUnary (eulerianRowSum (bwordLength n))

def worpitzkyNatSum (n x : Nat) : Nat :=
  BEDC.Derived.BinomialIdentitiesUp.finiteFoldNatSum
    (fun k => eulerianNumber n k * C (x + k) n) n

theorem eulerian_zero_zero :
    eulerianNumber 0 0 = 1 := by
  rfl

theorem eulerian_zero_succ (k : Nat) :
    eulerianNumber 0 (Nat.succ k) = 0 := by
  rfl

theorem eulerian_left_boundary (n : Nat) :
    eulerianNumber n 0 = 1 := by
  cases n with
  | zero =>
      rfl
  | succ _ =>
      rfl

theorem eulerian_recurrence (n k : Nat) :
    eulerianNumber (Nat.succ n) (Nat.succ k) =
      Nat.succ (Nat.succ k) * eulerianNumber n (Nat.succ k) +
        (n - k) * eulerianNumber n k := by
  rfl

theorem eulerian_succ_above :
    ∀ n extra : Nat, eulerianNumber n (Nat.succ (n + extra)) = 0 := by
  intro n
  induction n with
  | zero =>
      intro extra
      rfl
  | succ n ih =>
      intro extra
      rw [Nat.succ_add]
      rw [show Nat.succ (n + extra) = n + Nat.succ extra by
        rw [Nat.add_succ]]
      change
        Nat.succ (Nat.succ (n + Nat.succ extra)) *
            eulerianNumber n (Nat.succ (n + Nat.succ extra)) +
          (n - (n + Nat.succ extra)) * eulerianNumber n (Nat.succ (n + extra)) = 0
      rw [ih (Nat.succ extra)]
      rw [ih extra]
      rw [Nat.mul_zero, Nat.mul_zero]

theorem eulerian_succ_diagonal_zero (n : Nat) :
    eulerianNumber (Nat.succ n) (Nat.succ n) = 0 := by
  change
    Nat.succ (Nat.succ n) * eulerianNumber n (Nat.succ n) +
      (n - n) * eulerianNumber n n = 0
  rw [eulerian_succ_above n 0]
  rw [Nat.sub_self, Nat.mul_zero, Nat.zero_mul, Nat.zero_add]

private theorem add_succ_right_shape (k extra : Nat) :
    Nat.succ k + extra = k + Nat.succ extra := by
  rw [Nat.succ_add, Nat.add_succ]

private theorem add_one_add_right_shape (k extra : Nat) :
    k + 1 + extra = k + Nat.succ extra := by
  rw [← Nat.succ_eq_add_one]
  exact add_succ_right_shape k extra

private theorem succ_add_factor_shape (k extra : Nat) :
    Nat.succ (Nat.succ k) + extra = Nat.succ (Nat.succ k + extra) := by
  rw [Nat.succ_add]

private theorem nat_add_succ_sub_left (k extra : Nat) :
    k + Nat.succ extra - k = Nat.succ extra := by
  induction k with
  | zero =>
      rw [Nat.zero_add]
      exact Nat.sub_zero (Nat.succ extra)
  | succ k ih =>
      rw [Nat.succ_add]
      change Nat.succ (k + Nat.succ extra) - Nat.succ k = Nat.succ extra
      rw [Nat.succ_sub_succ_eq_sub]
      exact ih

private theorem add_middle_swap (a b c d : Nat) :
    (a + (b + c)) + d = (a + c) + (b + d) := by
  calc
    (a + (b + c)) + d = a + ((b + c) + d) :=
      Nat.add_assoc a (b + c) d
    _ = a + (b + (c + d)) := by
      rw [Nat.add_assoc b c d]
    _ = a + (c + (b + d)) := by
      rw [Nat.add_left_comm b c d]
    _ = (a + c) + (b + d) :=
      (Nat.add_assoc a c (b + d)).symm

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
          congrArg (fun x => x + (a + b)) ih
        _ = a * c + (b * c + (a + b)) :=
          Nat.add_assoc (a * c) (b * c) (a + b)
        _ = a * c + ((b * c + a) + b) :=
          congrArg (fun x => a * c + x) (Nat.add_assoc (b * c) a b).symm
        _ = a * c + ((a + b * c) + b) :=
          congrArg (fun x => a * c + (x + b)) (Nat.add_comm (b * c) a)
        _ = a * c + (a + (b * c + b)) :=
          congrArg (fun x => a * c + x) (Nat.add_assoc a (b * c) b)
        _ = (a * c + a) + (b * c + b) :=
          (Nat.add_assoc (a * c) a (b * c + b)).symm
        _ = a * Nat.succ c + (b * c + b) :=
          congrArg (fun x => x + (b * c + b)) (Nat.mul_succ a c).symm
        _ = a * Nat.succ c + b * Nat.succ c :=
          congrArg (fun x => a * Nat.succ c + x) (Nat.mul_succ b c).symm

private theorem eulerianPrefix_succ_balance_below :
    ∀ k extra : Nat,
      eulerianPrefix (Nat.succ (k + extra)) k +
          extra * eulerianNumber (k + extra) k =
        Nat.succ (k + extra) * eulerianPrefix (k + extra) k := by
  intro k
  induction k with
  | zero =>
      intro extra
      rw [Nat.zero_add]
      change 1 + extra * eulerianNumber extra 0 =
        Nat.succ extra * eulerianNumber extra 0
      rw [eulerian_left_boundary extra]
      rw [Nat.mul_one, Nat.mul_one, Nat.add_comm]
  | succ k ih =>
      intro extra
      have prev := ih (Nat.succ extra)
      rw [add_one_add_right_shape k extra]
      dsimp [eulerianPrefix]
      rw [eulerian_recurrence (k + Nat.succ extra) k]
      rw [Nat.mul_add]
      rw [nat_add_succ_sub_left k extra]
      calc
        (eulerianPrefix (Nat.succ (k + Nat.succ extra)) k +
              (Nat.succ (Nat.succ k) *
                  eulerianNumber (k + Nat.succ extra) (Nat.succ k) +
                Nat.succ extra *
                  eulerianNumber (k + Nat.succ extra) k)) +
            extra * eulerianNumber (k + Nat.succ extra) (Nat.succ k) =
            (eulerianPrefix (Nat.succ (k + Nat.succ extra)) k +
                Nat.succ extra *
                  eulerianNumber (k + Nat.succ extra) k) +
              (Nat.succ (Nat.succ k) *
                  eulerianNumber (k + Nat.succ extra) (Nat.succ k) +
                extra * eulerianNumber (k + Nat.succ extra) (Nat.succ k)) := by
          exact add_middle_swap
            (eulerianPrefix (Nat.succ (k + Nat.succ extra)) k)
            (Nat.succ (Nat.succ k) *
              eulerianNumber (k + Nat.succ extra) (Nat.succ k))
            (Nat.succ extra *
              eulerianNumber (k + Nat.succ extra) k)
            (extra * eulerianNumber (k + Nat.succ extra) (Nat.succ k))
        _ =
            (eulerianPrefix (Nat.succ (k + Nat.succ extra)) k +
                Nat.succ extra *
                  eulerianNumber (k + Nat.succ extra) k) +
              ((Nat.succ (Nat.succ k) + extra) *
                  eulerianNumber (k + Nat.succ extra) (Nat.succ k)) := by
          exact
            congrArg
              (fun t =>
                (eulerianPrefix (Nat.succ (k + Nat.succ extra)) k +
                    Nat.succ extra *
                      eulerianNumber (k + Nat.succ extra) k) + t)
              (nat_add_mul_clean (Nat.succ (Nat.succ k)) extra
                (eulerianNumber (k + Nat.succ extra) (Nat.succ k))).symm
        _ =
            (eulerianPrefix (Nat.succ (k + Nat.succ extra)) k +
                Nat.succ extra *
                  eulerianNumber (k + Nat.succ extra) k) +
              (Nat.succ (k + Nat.succ extra) *
                  eulerianNumber (k + Nat.succ extra) (Nat.succ k)) := by
          rw [succ_add_factor_shape k extra]
          rw [Nat.succ_add]
          rw [Nat.add_succ]
        _ =
            Nat.succ (k + Nat.succ extra) *
                eulerianPrefix (k + Nat.succ extra) k +
              Nat.succ (k + Nat.succ extra) *
                eulerianNumber (k + Nat.succ extra) (Nat.succ k) := by
          rw [prev]

theorem eulerianRowSum_succ (n : Nat) :
    eulerianRowSum (Nat.succ n) =
      Nat.succ n * eulerianRowSum n := by
  unfold eulerianRowSum
  change eulerianPrefix (Nat.succ n) n +
      eulerianNumber (Nat.succ n) (Nat.succ n) =
    Nat.succ n * eulerianPrefix n n
  rw [eulerian_succ_diagonal_zero n]
  rw [Nat.add_zero]
  have balanced := eulerianPrefix_succ_balance_below n 0
  change eulerianPrefix (Nat.succ (n + 0)) n +
      0 * eulerianNumber (n + 0) n =
    Nat.succ (n + 0) * eulerianPrefix (n + 0) n at balanced
  rw [Nat.add_zero, Nat.zero_mul, Nat.add_zero] at balanced
  exact balanced

theorem eulerianRowSum_eq_natFactorialCount (n : Nat) :
    eulerianRowSum n = BEDC.Derived.PochhammerUp.natFactorialCount n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [eulerianRowSum_succ n]
      rw [ih]
      rw [BEDC.Derived.PochhammerUp.natFactorialCount_succ n]
      exact Nat.mul_comm (Nat.succ n)
        (BEDC.Derived.PochhammerUp.natFactorialCount n)

theorem eulerianRowSumFn_natFactorialFn (n : Nat) :
    eulerianRowSumFn (natToUnary n) =
      BEDC.Derived.FactorialUp.natFactorialFn (natToUnary n) := by
  unfold eulerianRowSumFn
  rw [natToUnary_length]
  rw [eulerianRowSum_eq_natFactorialCount n]
  unfold BEDC.Derived.PochhammerUp.natFactorialCount
  rw [BEDC.Derived.StirlingFirstUp.natFactorialFn_natToUnary n]
  rw [natToUnary_length]

theorem eulerianNumberFn_unary_result (n k : BHist) :
    BEDC.FKernel.Unary.UnaryHistory (eulerianNumberFn n k) := by
  unfold eulerianNumberFn
  exact natToUnary_unary _

theorem eulerianRowSumFn_unary_result (n : BHist) :
    BEDC.FKernel.Unary.UnaryHistory (eulerianRowSumFn n) := by
  unfold eulerianRowSumFn
  exact natToUnary_unary _

theorem EulerianNumberUp_constructive_export :
    (∀ n : Nat, eulerianNumber n 0 = 1) ∧
      (∀ n k : Nat,
        eulerianNumber (Nat.succ n) (Nat.succ k) =
          Nat.succ (Nat.succ k) * eulerianNumber n (Nat.succ k) +
            (n - k) * eulerianNumber n k) ∧
      (∀ n extra : Nat, eulerianNumber n (Nat.succ (n + extra)) = 0) ∧
      (∀ n : Nat,
        eulerianRowSum n = BEDC.Derived.PochhammerUp.natFactorialCount n) ∧
      (∀ n : Nat,
        eulerianRowSumFn (natToUnary n) =
          BEDC.Derived.FactorialUp.natFactorialFn (natToUnary n)) := by
  constructor
  · intro n
    exact eulerian_left_boundary n
  · constructor
    · intro n k
      exact eulerian_recurrence n k
    · constructor
      · intro n extra
        exact eulerian_succ_above n extra
      · constructor
        · intro n
          exact eulerianRowSum_eq_natFactorialCount n
        · intro n
          exact eulerianRowSumFn_natFactorialFn n

end BEDC.Derived.EulerianNumberUp
