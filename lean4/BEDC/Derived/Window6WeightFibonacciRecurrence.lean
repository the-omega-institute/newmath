import BEDC.Derived.Window6WeightLogConcaveTuran

namespace BEDC
namespace Derived
namespace Window6WeightFibonacciRecurrence

open Window6WeightLogConcaveTuran

set_option maxRecDepth 10000

/-!
`W_m(x)` for the Fibonacci-cube weight coefficients satisfies the Fibonacci
polynomial recurrence `W_m = W_{m-1} + x W_{m-2}`.  Equivalently, its generating
function is `1 / (1 - z - x z^2)`, and the specialization `x = 1` is the golden
Fibonacci zeta carrier.  The real-rootedness route is the interlacing forcing of
the same recurrence on this finite-window carrier; the certificates here are
structural recurrence and concrete low-window algebra, not a proof of RH.
-/

theorem nat_add_zero_right (n : Nat) : n + 0 = n := by
  rfl

theorem nat_zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      exact congrArg Nat.succ ih

theorem nat_add_succ_right (a b : Nat) : a + Nat.succ b = Nat.succ (a + b) := by
  rfl

theorem nat_add_one_right (n : Nat) : n + 1 = Nat.succ n := by
  rfl

theorem nat_add_assoc_pure (a b c : Nat) : (a + b) + c = a + (b + c) := by
  induction c with
  | zero => rfl
  | succ c ih =>
      exact congrArg Nat.succ ih

theorem nat_succ_add (a b : Nat) : Nat.succ a + b = Nat.succ (a + b) := by
  induction b with
  | zero => rfl
  | succ b ih =>
      exact congrArg Nat.succ ih

theorem nat_count_front_succ (a b : Nat) : (a + b) + 1 = (a + 1) + b := by
  induction b with
  | zero => rfl
  | succ b ih =>
      exact congrArg Nat.succ ih

theorem boolWords_succ (m : Nat) :
    boolWords (Nat.succ m) =
      listAppend (listMap (fun w => false :: w) (boolWords m))
        (listMap (fun w => true :: w) (boolWords m)) := by
  rfl

theorem weightCoeffFromWords_match (k : Nat) (ys : List (List Bool)) :
    (match ys with
    | [] => 0
    | w :: rest =>
        match noAdj w with
        | true =>
            match natEqBool (trueCount w) k with
            | true => weightCoeffFromWords k rest + 1
            | false => weightCoeffFromWords k rest
        | false => weightCoeffFromWords k rest) =
      weightCoeffFromWords k ys := by
  cases ys with
  | nil => rfl
  | cons w rest => rfl

theorem weightCoeffFromWords_append (k : Nat) (xs ys : List (List Bool)) :
    weightCoeffFromWords k (listAppend xs ys) =
      weightCoeffFromWords k xs + weightCoeffFromWords k ys := by
  induction xs with
  | nil =>
      dsimp only [listAppend, weightCoeffFromWords]
      rw [nat_zero_add (weightCoeffFromWords k ys)]
  | cons w rest ih =>
      unfold listAppend
      unfold weightCoeffFromWords
      cases noAdj w with
      | false =>
          dsimp only []
          exact Eq.trans ih
            (congrArg (fun t => weightCoeffFromWords k rest + t)
              (Eq.symm (weightCoeffFromWords_match k ys)))
      | true =>
          cases natEqBool (trueCount w) k with
          | false =>
              dsimp only []
              exact Eq.trans ih
                (congrArg (fun t => weightCoeffFromWords k rest + t)
                  (Eq.symm (weightCoeffFromWords_match k ys)))
          | true =>
              dsimp only []
              exact Eq.trans
                (congrArg (fun t => t + 1) ih)
                (Eq.trans
                  (nat_count_front_succ
                    (weightCoeffFromWords k rest) (weightCoeffFromWords k ys))
                  (congrArg (fun t => (weightCoeffFromWords k rest + 1) + t)
                    (Eq.symm (weightCoeffFromWords_match k ys))))

theorem listMap_append {α β : Type} (f : α -> β) (xs ys : List α) :
    listMap f (listAppend xs ys) =
      listAppend (listMap f xs) (listMap f ys) := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
      exact congrArg (fun zs => f x :: zs) ih

theorem listMap_comp {α β γ : Type} (f : β -> γ) (g : α -> β) (xs : List α) :
    listMap f (listMap g xs) = listMap (fun x => f (g x)) xs := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
      exact congrArg (fun zs => f (g x) :: zs) ih

theorem false_prefix_weightCoeffFromWords (k : Nat) (xs : List (List Bool)) :
    weightCoeffFromWords k (listMap (fun w => false :: w) xs) =
      weightCoeffFromWords k xs := by
  induction xs with
  | nil => rfl
  | cons w rest ih =>
      unfold listMap
      unfold weightCoeffFromWords
      cases w with
      | nil =>
          rw [ih]
          rfl
      | cons b tail =>
          rw [ih]
          rfl

theorem true_true_prefix_zero (k : Nat) (xs : List (List Bool)) :
    weightCoeffFromWords (Nat.succ k) (listMap (fun w => true :: true :: w) xs) =
      0 := by
  induction xs with
  | nil => rfl
  | cons w rest ih =>
      unfold listMap
      unfold weightCoeffFromWords
      exact ih

theorem natEqBool_succ_succ (a b : Nat) :
    natEqBool (Nat.succ a) (Nat.succ b) = natEqBool a b := by
  rfl

theorem noAdj_true_false (w : List Bool) :
    noAdj (true :: false :: w) = noAdj w := by
  cases w with
  | nil => rfl
  | cons b tail => rfl

theorem trueCount_true_false (w : List Bool) :
    trueCount (true :: false :: w) = Nat.succ (trueCount w) := by
  rfl

theorem true_false_prefix_weightCoeffFromWords (k : Nat) (xs : List (List Bool)) :
    weightCoeffFromWords (Nat.succ k)
        (listMap (fun w => true :: false :: w) xs) =
      weightCoeffFromWords k xs := by
  induction xs with
  | nil => rfl
  | cons w rest ih =>
      unfold listMap
      unfold weightCoeffFromWords
      rw [noAdj_true_false w]
      rw [trueCount_true_false w]
      rw [natEqBool_succ_succ (trueCount w) k]
      cases noAdj w with
      | false =>
          dsimp only []
          exact ih
      | true =>
          cases natEqBool (trueCount w) k with
          | false =>
              dsimp only []
              exact ih
          | true =>
              dsimp only []
              rw [ih]

theorem true_prefix_boolWords_succ (m k : Nat) :
    weightCoeffFromWords (Nat.succ k)
        (listMap (fun w => true :: w) (boolWords (Nat.succ m))) =
      weightCoeff m k := by
  rw [boolWords_succ m]
  rw [listMap_append]
  rw [listMap_comp (fun w => true :: w) (fun w => false :: w) (boolWords m)]
  rw [listMap_comp (fun w => true :: w) (fun w => true :: w) (boolWords m)]
  rw [weightCoeffFromWords_append]
  rw [true_false_prefix_weightCoeffFromWords]
  rw [true_true_prefix_zero]
  unfold weightCoeff
  rw [nat_add_zero_right (weightCoeffFromWords k (boolWords m))]

theorem weightCoeff_fib_recurrence (m k : Nat) :
    weightCoeff (Nat.succ (Nat.succ m)) (Nat.succ k) =
      weightCoeff (Nat.succ m) (Nat.succ k) + weightCoeff m k := by
  unfold weightCoeff
  rw [boolWords_succ (Nat.succ m)]
  rw [weightCoeffFromWords_append]
  rw [false_prefix_weightCoeffFromWords]
  rw [true_prefix_boolWords_succ]
  rfl

theorem weightCoeff_six_zero_recurrence :
    weightCoeff 6 0 = weightCoeff 5 0 := rfl

theorem weightCoeff_six_one_recurrence :
    weightCoeff 6 1 = weightCoeff 5 1 + weightCoeff 4 0 := rfl

theorem weightCoeff_six_two_recurrence :
    weightCoeff 6 2 = weightCoeff 5 2 + weightCoeff 4 1 := rfl

theorem weightCoeff_six_three_recurrence :
    weightCoeff 6 3 = weightCoeff 5 3 + weightCoeff 4 2 := rfl

theorem weightCoeff_six_four_recurrence :
    weightCoeff 6 4 = weightCoeff 5 4 + weightCoeff 4 3 := rfl

theorem window_six_weight_fibonacci_recurrence :
    weightCoeff 6 0 = weightCoeff 5 0 ∧
    weightCoeff 6 1 = weightCoeff 5 1 + weightCoeff 4 0 ∧
    weightCoeff 6 2 = weightCoeff 5 2 + weightCoeff 4 1 ∧
    weightCoeff 6 3 = weightCoeff 5 3 + weightCoeff 4 2 ∧
    weightCoeff 6 4 = weightCoeff 5 4 + weightCoeff 4 3 := by
  constructor
  exact weightCoeff_six_zero_recurrence
  constructor
  exact weightCoeff_six_one_recurrence
  constructor
  exact weightCoeff_six_two_recurrence
  constructor
  exact weightCoeff_six_three_recurrence
  exact weightCoeff_six_four_recurrence

def evalQuadratic (a b c x : Int) : Int :=
  a * x * x + b * x + c

theorem window_six_quadratic_factor_positive_at_zero :
    evalQuadratic 2 4 1 0 = 1 := rfl

theorem window_six_quadratic_factor_positive_at_minus_one :
    evalQuadratic 2 4 1 (-1) = -1 := rfl

theorem window_six_linear_quadratic_factor_certificate :
    (2 * (-1) + 1) *
        evalQuadratic 2 4 1 (-1) = 1 := rfl

end Window6WeightFibonacciRecurrence
end Derived
end BEDC
