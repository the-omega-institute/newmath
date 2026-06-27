import BEDC.Derived.EulerianNumberUp
import BEDC.Derived.StirlingUp

namespace BEDC.Derived.EulerianSecondOrderUp

open BEDC.FKernel.Hist
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.IntUp (natToUnary natToUnary_unary natToUnary_length)

abbrev UnaryOne : BHist := BHist.e1 BHist.Empty

-- 第二类 Eulerian 数按 Stirling 型升阶递归闭生成。
def eulerianSecondNumber : Nat -> Nat -> Nat
  | 0, 0 => 1
  | 0, Nat.succ _ => 0
  | Nat.succ _, 0 => 1
  | Nat.succ n, Nat.succ k =>
      Nat.succ (Nat.succ k) * eulerianSecondNumber n (Nat.succ k) +
        (Nat.succ (n + n) - Nat.succ k) * eulerianSecondNumber n k

def eulerianSecondPrefix (n : Nat) : Nat -> Nat
  | 0 => eulerianSecondNumber n 0
  | Nat.succ k =>
      eulerianSecondPrefix n k + eulerianSecondNumber n (Nat.succ k)

def eulerianSecondRowSum (n : Nat) : Nat :=
  eulerianSecondPrefix n n

def oddDoubleFactorialCount : Nat -> Nat
  | 0 => 1
  | Nat.succ n => Nat.succ (n + n) * oddDoubleFactorialCount n

def eulerianSecondNumberFn (n k : BHist) : BHist :=
  natToUnary (eulerianSecondNumber (bwordLength n) (bwordLength k))

def eulerianSecondRowSumFn (n : BHist) : BHist :=
  natToUnary (eulerianSecondRowSum (bwordLength n))

theorem eulerianSecond_zero_zero :
    eulerianSecondNumber 0 0 = 1 := by
  rfl

theorem eulerianSecond_zero_succ (k : Nat) :
    eulerianSecondNumber 0 (Nat.succ k) = 0 := by
  rfl

theorem eulerianSecond_left_boundary (n : Nat) :
    eulerianSecondNumber n 0 = 1 := by
  cases n with
  | zero =>
      rfl
  | succ _ =>
      rfl

theorem eulerianSecond_recurrence (n k : Nat) :
    eulerianSecondNumber (Nat.succ n) (Nat.succ k) =
      Nat.succ (Nat.succ k) * eulerianSecondNumber n (Nat.succ k) +
        (Nat.succ (n + n) - Nat.succ k) * eulerianSecondNumber n k := by
  rfl

theorem eulerianSecondPrefix_succ (n k : Nat) :
    eulerianSecondPrefix n (Nat.succ k) =
      eulerianSecondPrefix n k + eulerianSecondNumber n (Nat.succ k) := by
  rfl

theorem oddDoubleFactorialCount_zero :
    oddDoubleFactorialCount 0 = 1 := by
  rfl

theorem oddDoubleFactorialCount_succ (n : Nat) :
    oddDoubleFactorialCount (Nat.succ n) =
      Nat.succ (n + n) * oddDoubleFactorialCount n := by
  rfl

theorem eulerianSecond_succ_above :
    ∀ n extra : Nat, eulerianSecondNumber n (Nat.succ (n + extra)) = 0 := by
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
            eulerianSecondNumber n (Nat.succ (n + Nat.succ extra)) +
          (Nat.succ (n + n) - Nat.succ (n + Nat.succ extra)) *
            eulerianSecondNumber n (Nat.succ (n + extra)) = 0
      rw [ih (Nat.succ extra)]
      rw [ih extra]
      rw [Nat.mul_zero, Nat.mul_zero]

theorem eulerianSecond_succ_diagonal_zero (n : Nat) :
    eulerianSecondNumber (Nat.succ n) (Nat.succ n) = 0 := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change
        Nat.succ (Nat.succ (Nat.succ n)) *
            eulerianSecondNumber (Nat.succ n) (Nat.succ (Nat.succ n)) +
          (Nat.succ (Nat.succ n + Nat.succ n) - Nat.succ (Nat.succ n)) *
            eulerianSecondNumber (Nat.succ n) (Nat.succ n) = 0
      rw [eulerianSecond_succ_above (Nat.succ n) 0]
      rw [ih]
      rw [Nat.mul_zero, Nat.mul_zero]

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

private theorem nat_add_right_sub_left_clean (a b : Nat) :
    a + b - a = b := by
  induction a with
  | zero =>
      rw [Nat.zero_add, Nat.sub_zero]
  | succ a ih =>
      rw [Nat.succ_add]
      change Nat.succ (a + b) - Nat.succ a = b
      rw [Nat.succ_sub_succ_eq_sub]
      exact ih

private theorem nat_add_sub_prefix_clean (a b : Nat) :
    a + ((a + b) - a) = a + b := by
  rw [nat_add_right_sub_left_clean a b]

private theorem nat_succ_add_sub_succ_prefix_clean (a b : Nat) :
    Nat.succ a + (Nat.succ (a + b) - Nat.succ a) =
      Nat.succ (a + b) := by
  rw [Nat.succ_sub_succ_eq_sub]
  rw [Nat.succ_add]
  exact congrArg Nat.succ (nat_add_sub_prefix_clean a b)

private theorem one_add_succ_sub_one_clean (m : Nat) :
    1 + (Nat.succ m - 1) = Nat.succ m := by
  change Nat.succ 0 + (Nat.succ m - Nat.succ 0) = Nat.succ m
  rw [Nat.succ_sub_succ_eq_sub]
  rw [Nat.sub_zero]
  rw [Nat.succ_add]
  rw [Nat.zero_add]

private theorem nat_second_coeff_shape (k extra : Nat) :
    (k + Nat.succ extra) + (k + Nat.succ extra) =
      Nat.succ k + (k + (extra + Nat.succ extra)) := by
  calc
    (k + Nat.succ extra) + (k + Nat.succ extra) =
        k + (Nat.succ extra + (k + Nat.succ extra)) :=
      Nat.add_assoc k (Nat.succ extra) (k + Nat.succ extra)
    _ = k + (k + (Nat.succ extra + Nat.succ extra)) := by
      rw [Nat.add_left_comm (Nat.succ extra) k (Nat.succ extra)]
    _ = k + (k + Nat.succ (extra + Nat.succ extra)) := by
      rw [Nat.succ_add]
    _ = k + Nat.succ (k + (extra + Nat.succ extra)) := by
      rw [Nat.add_succ]
    _ = Nat.succ (k + (k + (extra + Nat.succ extra))) := by
      rw [Nat.add_succ]
    _ = Nat.succ ((k + k) + (extra + Nat.succ extra)) := by
      rw [Nat.add_assoc]
    _ = Nat.succ k + (k + (extra + Nat.succ extra)) := by
      rw [Nat.succ_add]
      rw [Nat.add_assoc]

private theorem nat_coeff_sum_succ (k extra : Nat) :
    Nat.succ (Nat.succ k) +
        (Nat.succ ((k + Nat.succ extra) + (k + Nat.succ extra)) -
          Nat.succ (Nat.succ k)) =
      Nat.succ ((k + Nat.succ extra) + (k + Nat.succ extra)) := by
  rw [nat_second_coeff_shape k extra]
  exact nat_succ_add_sub_succ_prefix_clean (Nat.succ k)
    (k + (extra + Nat.succ extra))

private theorem prefix_add_middle_swap (a b c d : Nat) :
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

private theorem eulerianSecondPrefix_succ_balance_below :
    ∀ k extra : Nat,
      eulerianSecondPrefix (Nat.succ (k + extra)) k +
          (Nat.succ ((k + extra) + (k + extra)) - Nat.succ k) *
            eulerianSecondNumber (k + extra) k =
        Nat.succ (k + extra + (k + extra)) *
          eulerianSecondPrefix (k + extra) k := by
  intro k
  induction k with
  | zero =>
      intro extra
      rw [Nat.zero_add]
      change 1 + (Nat.succ (extra + extra) - 1) * eulerianSecondNumber extra 0 =
        Nat.succ (extra + extra) * eulerianSecondNumber extra 0
      rw [eulerianSecond_left_boundary extra]
      rw [Nat.mul_one, Nat.mul_one]
      exact one_add_succ_sub_one_clean (extra + extra)
  | succ k ih =>
      intro extra
      have prev := ih (Nat.succ extra)
      rw [show Nat.succ k + extra = k + Nat.succ extra by
        rw [Nat.succ_add, Nat.add_succ]]
      dsimp [eulerianSecondPrefix]
      rw [eulerianSecond_recurrence (k + Nat.succ extra) k]
      rw [Nat.mul_add]
      calc
        (eulerianSecondPrefix (Nat.succ (k + Nat.succ extra)) k +
              (Nat.succ (Nat.succ k) *
                  eulerianSecondNumber (k + Nat.succ extra) (Nat.succ k) +
                (Nat.succ (k + Nat.succ extra + (k + Nat.succ extra)) -
                    Nat.succ k) *
                  eulerianSecondNumber (k + Nat.succ extra) k)) +
            (Nat.succ ((k + Nat.succ extra) + (k + Nat.succ extra)) -
                Nat.succ (Nat.succ k)) *
              eulerianSecondNumber (k + Nat.succ extra) (Nat.succ k) =
            (eulerianSecondPrefix (Nat.succ (k + Nat.succ extra)) k +
                (Nat.succ (k + Nat.succ extra + (k + Nat.succ extra)) -
                    Nat.succ k) *
                  eulerianSecondNumber (k + Nat.succ extra) k) +
              (Nat.succ (Nat.succ k) *
                  eulerianSecondNumber (k + Nat.succ extra) (Nat.succ k) +
                (Nat.succ ((k + Nat.succ extra) + (k + Nat.succ extra)) -
                    Nat.succ (Nat.succ k)) *
                  eulerianSecondNumber (k + Nat.succ extra) (Nat.succ k)) := by
          exact prefix_add_middle_swap
            (eulerianSecondPrefix (Nat.succ (k + Nat.succ extra)) k)
            (Nat.succ (Nat.succ k) *
              eulerianSecondNumber (k + Nat.succ extra) (Nat.succ k))
            ((Nat.succ (k + Nat.succ extra + (k + Nat.succ extra)) -
                Nat.succ k) *
              eulerianSecondNumber (k + Nat.succ extra) k)
            ((Nat.succ ((k + Nat.succ extra) + (k + Nat.succ extra)) -
                Nat.succ (Nat.succ k)) *
              eulerianSecondNumber (k + Nat.succ extra) (Nat.succ k))
        _ =
            (eulerianSecondPrefix (Nat.succ (k + Nat.succ extra)) k +
                (Nat.succ ((k + Nat.succ extra) + (k + Nat.succ extra)) -
                    Nat.succ k) *
                  eulerianSecondNumber (k + Nat.succ extra) k) +
              ((Nat.succ (Nat.succ k) +
                    (Nat.succ ((k + Nat.succ extra) + (k + Nat.succ extra)) -
                      Nat.succ (Nat.succ k))) *
                  eulerianSecondNumber (k + Nat.succ extra) (Nat.succ k)) := by
          exact
            congrArg
              (fun t =>
                (eulerianSecondPrefix (Nat.succ (k + Nat.succ extra)) k +
                    (Nat.succ ((k + Nat.succ extra) + (k + Nat.succ extra)) -
                        Nat.succ k) *
                      eulerianSecondNumber (k + Nat.succ extra) k) + t)
              (nat_add_mul_clean (Nat.succ (Nat.succ k))
                (Nat.succ ((k + Nat.succ extra) + (k + Nat.succ extra)) -
                  Nat.succ (Nat.succ k))
                (eulerianSecondNumber (k + Nat.succ extra) (Nat.succ k))).symm
        _ =
            Nat.succ (k + Nat.succ extra + (k + Nat.succ extra)) *
                eulerianSecondPrefix (k + Nat.succ extra) k +
              (Nat.succ (k + Nat.succ extra + (k + Nat.succ extra)) *
                  eulerianSecondNumber (k + Nat.succ extra) (Nat.succ k)) := by
          rw [prev]
          rw [nat_coeff_sum_succ k extra]
        _ =
            (k + Nat.succ extra + (k + Nat.succ extra) + 1) *
                (eulerianSecondPrefix (k + Nat.succ extra) k +
                  eulerianSecondNumber (k + Nat.succ extra) (Nat.succ k)) := by
          rw [← Nat.succ_eq_add_one (k + Nat.succ extra + (k + Nat.succ extra))]
          rw [← Nat.mul_add]
        _ =
            (k + (extra + 1) + (k + (extra + 1)) + 1) *
                eulerianSecondPrefix (k + (extra + 1)) k +
              (k + (extra + 1) + (k + (extra + 1)) + 1) *
                eulerianSecondNumber (k + (extra + 1)) (k + 1) := by
          rw [← Nat.succ_eq_add_one extra]
          rw [← Nat.succ_eq_add_one k]
          rw [← Nat.mul_add]

theorem eulerianSecondRowSum_succ (n : Nat) :
    eulerianSecondRowSum (Nat.succ n) =
      Nat.succ (n + n) * eulerianSecondRowSum n := by
  unfold eulerianSecondRowSum
  change eulerianSecondPrefix (Nat.succ n) n +
      eulerianSecondNumber (Nat.succ n) (Nat.succ n) =
    Nat.succ (n + n) * eulerianSecondPrefix n n
  rw [eulerianSecond_succ_diagonal_zero n]
  rw [Nat.add_zero]
  have balanced := eulerianSecondPrefix_succ_balance_below n 0
  change eulerianSecondPrefix (Nat.succ (n + 0)) n +
      (Nat.succ ((n + 0) + (n + 0)) - Nat.succ n) *
        eulerianSecondNumber (n + 0) n =
    Nat.succ (n + 0 + (n + 0)) * eulerianSecondPrefix (n + 0) n at balanced
  rw [Nat.add_zero] at balanced
  have tailZero :
      (Nat.succ (n + n) - Nat.succ n) * eulerianSecondNumber n n = 0 := by
    cases n with
    | zero =>
        rfl
    | succ n =>
        rw [eulerianSecond_succ_diagonal_zero n]
        exact Nat.mul_zero _
  rw [tailZero, Nat.add_zero] at balanced
  exact balanced

theorem eulerianSecondRowSum_eq_oddDoubleFactorialCount (n : Nat) :
    eulerianSecondRowSum n = oddDoubleFactorialCount n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [eulerianSecondRowSum_succ n]
      rw [oddDoubleFactorialCount_succ n]
      rw [ih]

theorem eulerianSecondNumberFn_unary_result (n k : BHist) :
    BEDC.FKernel.Unary.UnaryHistory (eulerianSecondNumberFn n k) := by
  unfold eulerianSecondNumberFn
  exact natToUnary_unary _

theorem eulerianSecondRowSumFn_unary_result (n : BHist) :
    BEDC.FKernel.Unary.UnaryHistory (eulerianSecondRowSumFn n) := by
  unfold eulerianSecondRowSumFn
  exact natToUnary_unary _

theorem eulerianSecondNumberFn_recurrence_natToUnary (n k : Nat) :
    eulerianSecondNumberFn (natToUnary (Nat.succ n)) (natToUnary (Nat.succ k)) =
      natToUnary
        (Nat.succ (Nat.succ k) * eulerianSecondNumber n (Nat.succ k) +
          (Nat.succ (n + n) - Nat.succ k) * eulerianSecondNumber n k) := by
  unfold eulerianSecondNumberFn
  rw [natToUnary_length, natToUnary_length]
  rfl

theorem eulerianSecondNumberFn_zero_zero :
    eulerianSecondNumberFn BHist.Empty BHist.Empty = UnaryOne := by
  rfl

theorem eulerianSecondRowSumFn_oddDoubleFactorial (n : Nat) :
    eulerianSecondRowSumFn (natToUnary n) =
      natToUnary (oddDoubleFactorialCount n) := by
  unfold eulerianSecondRowSumFn
  rw [natToUnary_length]
  rw [eulerianSecondRowSum_eq_oddDoubleFactorialCount n]

theorem eulerianSecond_zero_row_stirling (k : Nat) :
    eulerianSecondNumber 0 k =
      BEDC.Derived.StirlingUp.stirlingSecond 0 k := by
  cases k with
  | zero =>
      rfl
  | succ _ =>
      rfl

theorem eulerianSecond_left_boundary_stirling_diagonal (n : Nat) :
    eulerianSecondNumber n 0 =
      BEDC.Derived.StirlingUp.stirlingSecond n n := by
  rw [eulerianSecond_left_boundary n]
  rw [BEDC.Derived.StirlingUp.stirlingSecond_self n]

theorem eulerianSecond_above_matches_stirling_above (n extra : Nat) :
    eulerianSecondNumber n (Nat.succ (n + extra)) =
      BEDC.Derived.StirlingUp.stirlingSecond n (Nat.succ (n + extra)) := by
  rw [eulerianSecond_succ_above n extra]
  rw [BEDC.Derived.StirlingUp.stirlingSecond_above n extra]

theorem EulerianSecondOrderUp_constructive_export :
    (eulerianSecondNumber 0 0 = 1) ∧
      (∀ n k : Nat,
        eulerianSecondNumber (Nat.succ n) (Nat.succ k) =
          Nat.succ (Nat.succ k) * eulerianSecondNumber n (Nat.succ k) +
            (Nat.succ (n + n) - Nat.succ k) * eulerianSecondNumber n k) ∧
      (∀ n extra : Nat,
        eulerianSecondNumber n (Nat.succ (n + extra)) = 0) ∧
      (∀ n : Nat,
        eulerianSecondRowSum n = oddDoubleFactorialCount n) ∧
      (∀ n : Nat,
        eulerianSecondNumber n 0 =
          BEDC.Derived.StirlingUp.stirlingSecond n n) ∧
      (∀ n extra : Nat,
        eulerianSecondNumber n (Nat.succ (n + extra)) =
          BEDC.Derived.StirlingUp.stirlingSecond n
            (Nat.succ (n + extra))) := by
  constructor
  · exact eulerianSecond_zero_zero
  · constructor
    · intro n k
      exact eulerianSecond_recurrence n k
    · constructor
      · intro n extra
        exact eulerianSecond_succ_above n extra
      · constructor
        · intro n
          exact eulerianSecondRowSum_eq_oddDoubleFactorialCount n
        · constructor
          · intro n
            exact eulerianSecond_left_boundary_stirling_diagonal n
          · intro n extra
            exact eulerianSecond_above_matches_stirling_above n extra

end BEDC.Derived.EulerianSecondOrderUp
