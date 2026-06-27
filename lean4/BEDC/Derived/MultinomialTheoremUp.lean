import BEDC.Derived.BinomialIdentitiesUp
import BEDC.Derived.MultinomialUp

namespace BEDC.Derived.MultinomialTheoremUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.IntUp (natToUnary natToUnary_unary)

abbrev C (n k : Nat) : Nat :=
  BEDC.Derived.BinomialIdentitiesUp.C n k

abbrev finiteNatSum (f : Nat -> Nat) : Nat -> Nat :=
  BEDC.Derived.BinomialIdentitiesUp.finiteFoldNatSum f

abbrev multinomialWeight : List Nat -> Nat :=
  BEDC.Derived.MultinomialUp.multinomialWeight

def multinomialCoefficient (_n : Nat) (ks : List Nat) : Nat :=
  BEDC.Derived.MultinomialUp.multinomialCount ks

abbrev multinomialFactorialDenominator : List Nat -> Nat :=
  BEDC.Derived.MultinomialUp.multinomialFactorialDenominator

def multinomialCoefficientSum : Nat -> Nat -> Nat
  | 0, 0 => 1
  | 0, Nat.succ _ => 0
  | Nat.succ m, n =>
      finiteNatSum
        (fun k => C n k * multinomialCoefficientSum m k) n

def multinomialFn (ks : List BHist) : BHist :=
  BEDC.Derived.MultinomialUp.multinomialFn ks

theorem multinomial_coefficient_factorial_identity
    (n : Nat) (ks : List Nat) (total : multinomialWeight ks = n) :
    multinomialCoefficient n ks * multinomialFactorialDenominator ks =
      BEDC.Derived.PochhammerUp.natFactorialCount n := by
  exact BEDC.Derived.MultinomialUp.multinomialFactorialQuotient_total
    n ks total

theorem multinomialFn_unary_result (ks : List BHist) :
    UnaryHistory (multinomialFn ks) := by
  exact BEDC.Derived.MultinomialUp.multinomialFn_unary_result ks

theorem multinomialFn_length (ks : List BHist) :
    bwordLength (multinomialFn ks) =
      BEDC.Derived.MultinomialUp.multinomialCount (ks.map bwordLength) := by
  exact BEDC.Derived.MultinomialUp.multinomialFn_length ks

theorem multinomial_binary_degenerates_to_binomial (k l : Nat) :
    multinomialCoefficient (k + l) [k, l] = C (k + l) k := by
  unfold multinomialCoefficient
  exact BEDC.Derived.MultinomialUp.multinomialCount_pair k l

theorem multinomial_binary_fn_degenerates_to_binomial (k l : BHist) :
    BEDC.FKernel.Hist.hsame
      (multinomialFn [k, l])
      (BEDC.Derived.FactorialUp.natChooseFn
        (natToUnary (bwordLength k + bwordLength l))
        (natToUnary (bwordLength k))) := by
  exact BEDC.Derived.MultinomialUp.multinomialFn_pair_binomial_hsame k l

theorem multinomialCoefficientSum_zero_zero :
    multinomialCoefficientSum 0 0 = 1 := by
  rfl

theorem multinomialCoefficientSum_zero_succ (n : Nat) :
    multinomialCoefficientSum 0 (Nat.succ n) = 0 := by
  rfl

theorem multinomialCoefficientSum_succ (m n : Nat) :
    multinomialCoefficientSum (Nat.succ m) n =
      finiteNatSum (fun k => C n k * multinomialCoefficientSum m k) n := by
  rfl

theorem finiteNatSum_add (f g : Nat -> Nat) :
    forall n : Nat,
      finiteNatSum (fun k => f k + g k) n =
        finiteNatSum f n + finiteNatSum g n
  | 0 => rfl
  | Nat.succ n => by
      change finiteNatSum (fun k => f k + g k) n +
          (f (Nat.succ n) + g (Nat.succ n)) =
        (finiteNatSum f n + f (Nat.succ n)) +
          (finiteNatSum g n + g (Nat.succ n))
      rw [finiteNatSum_add f g n]
      calc
        (finiteNatSum f n + finiteNatSum g n) +
            (f (Nat.succ n) + g (Nat.succ n)) =
            finiteNatSum f n +
              (finiteNatSum g n + (f (Nat.succ n) + g (Nat.succ n))) :=
          Nat.add_assoc _ _ _
        _ = finiteNatSum f n +
              (f (Nat.succ n) + (finiteNatSum g n + g (Nat.succ n))) := by
          rw [Nat.add_left_comm (finiteNatSum g n) (f (Nat.succ n)) (g (Nat.succ n))]
        _ = (finiteNatSum f n + f (Nat.succ n)) +
              (finiteNatSum g n + g (Nat.succ n)) :=
          (Nat.add_assoc _ _ _).symm

theorem finiteNatSum_mul_left (c : Nat) (f : Nat -> Nat) :
    forall n : Nat,
      finiteNatSum (fun k => c * f k) n = c * finiteNatSum f n
  | 0 => rfl
  | Nat.succ n => by
      change finiteNatSum (fun k => c * f k) n + c * f (Nat.succ n) =
        c * (finiteNatSum f n + f (Nat.succ n))
      rw [finiteNatSum_mul_left c f n]
      exact (Nat.mul_add c (finiteNatSum f n) (f (Nat.succ n))).symm

theorem finiteNatSum_ext (f g : Nat -> Nat)
    (same : ∀ k : Nat, f k = g k) :
    forall n : Nat, finiteNatSum f n = finiteNatSum g n
  | 0 => same 0
  | Nat.succ n => by
      change finiteNatSum f n + f (Nat.succ n) =
        finiteNatSum g n + g (Nat.succ n)
      rw [finiteNatSum_ext f g same n]
      rw [same (Nat.succ n)]

theorem finiteNatSum_succ_zero_tail (f : Nat -> Nat) (n : Nat)
    (lastZero : f (Nat.succ n) = 0) :
    finiteNatSum f (Nat.succ n) = finiteNatSum f n := by
  change finiteNatSum f n + f (Nat.succ n) = finiteNatSum f n
  rw [lastZero]
  exact Nat.add_zero (finiteNatSum f n)

theorem finiteNatSum_succ_decomp (f : Nat -> Nat) :
    forall n : Nat,
      finiteNatSum f (Nat.succ n) =
        f 0 + finiteNatSum (fun k => f (Nat.succ k)) n
  | 0 => by
      change f 0 + f 1 = f 0 + f 1
      rfl
  | Nat.succ n => by
      change finiteNatSum f (Nat.succ n) + f (Nat.succ (Nat.succ n)) =
        f 0 + (finiteNatSum (fun k => f (Nat.succ k)) n +
          f (Nat.succ (Nat.succ n)))
      rw [finiteNatSum_succ_decomp f n]
      exact Nat.add_assoc (f 0)
        (finiteNatSum (fun k => f (Nat.succ k)) n)
        (f (Nat.succ (Nat.succ n)))

theorem nat_mul_assoc_clean (a b c : Nat) :
    (a * b) * c = a * (b * c) := by
  induction c with
  | zero =>
      rfl
  | succ c ih =>
      calc
        (a * b) * Nat.succ c = (a * b) * c + a * b :=
          Nat.mul_succ (a * b) c
        _ = a * (b * c) + a * b :=
          congrArg (fun x => x + a * b) ih
        _ = a * (b * c + b) :=
          (Nat.mul_add a (b * c) b).symm
        _ = a * (b * Nat.succ c) :=
          congrArg (fun x => a * x) (Nat.mul_succ b c).symm

theorem nat_add_mul_clean (a b c : Nat) :
    (a + b) * c = a * c + b * c := by
  induction c with
  | zero =>
      rfl
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

theorem binomial_zero_right_value (n m : Nat) :
    C n 0 * m ^ 0 = 1 := by
  unfold C
  rw [BEDC.Derived.BinomialIdentitiesUp.binomial_zero_right n]
  rw [Nat.pow_zero]

theorem binomial_above_zero_term (n m : Nat) :
    C n (Nat.succ n) * m ^ Nat.succ n = 0 := by
  unfold C
  have above := BEDC.Derived.BinomialIdentitiesUp.binomial_above n 0
  rw [Nat.add_zero] at above
  rw [above]
  exact Nat.zero_mul (m ^ Nat.succ n)

theorem weighted_term_succ (m n k : Nat) :
    C n k * m ^ Nat.succ k = m * (C n k * m ^ k) := by
  rw [Nat.pow_succ']
  calc
    C n k * (m * m ^ k) = (C n k * m) * m ^ k :=
      (nat_mul_assoc_clean (C n k) m (m ^ k)).symm
    _ = (m * C n k) * m ^ k := by
      rw [Nat.mul_comm (C n k) m]
    _ = m * (C n k * m ^ k) :=
      nat_mul_assoc_clean m (C n k) (m ^ k)

def weightedBinomialSum (m n : Nat) : Nat :=
  finiteNatSum (fun k => C n k * m ^ k) n

def shiftedWeightedBinomialSum (m : Nat) : Nat -> Nat
  | 0 => 0
  | Nat.succ n =>
      finiteNatSum (fun k => C (Nat.succ n) (Nat.succ k) * m ^ Nat.succ k) n

theorem weightedBinomialSum_succ_decomp (m n : Nat) :
    weightedBinomialSum m (Nat.succ n) =
      1 + shiftedWeightedBinomialSum m (Nat.succ n) := by
  unfold weightedBinomialSum shiftedWeightedBinomialSum
  rw [finiteNatSum_succ_decomp]
  rw [binomial_zero_right_value (Nat.succ n) m]

theorem weightedBinomialSum_tail_decomp (m n : Nat) :
    weightedBinomialSum m n =
      1 + shiftedWeightedBinomialSum m n := by
  cases n with
  | zero =>
      unfold weightedBinomialSum shiftedWeightedBinomialSum
      change C 0 0 * m ^ 0 = 1 + 0
      exact binomial_zero_right_value 0 m
  | succ n =>
      exact weightedBinomialSum_succ_decomp m n

theorem shiftedWeightedBinomialSum_succ (m n : Nat) :
    shiftedWeightedBinomialSum m (Nat.succ n) =
      m * weightedBinomialSum m n + shiftedWeightedBinomialSum m n := by
  cases n with
  | zero =>
      unfold shiftedWeightedBinomialSum weightedBinomialSum
      change C 1 1 * m ^ 1 = m * (C 0 0 * m ^ 0) + 0
      unfold C
      rw [BEDC.Derived.BinomialIdentitiesUp.binomial_self 1]
      rw [BEDC.Derived.BinomialIdentitiesUp.binomial_zero_right 0]
      rw [Nat.pow_succ, Nat.pow_zero]
      rw [Nat.mul_one, Nat.one_mul, Nat.add_zero]
      exact Nat.one_mul m
  | succ n =>
      change
        finiteNatSum
            (fun k => C (Nat.succ (Nat.succ n)) (Nat.succ k) *
              m ^ Nat.succ k)
            (Nat.succ n) =
          m * weightedBinomialSum m (Nat.succ n) +
            finiteNatSum
              (fun k => C (Nat.succ n) (Nat.succ k) * m ^ Nat.succ k)
              n
      let row := Nat.succ n
      have pascalTerms :
          finiteNatSum
              (fun k => C (Nat.succ row) (Nat.succ k) * m ^ Nat.succ k)
              row =
            finiteNatSum
              (fun k =>
                C row k * m ^ Nat.succ k +
                  C row (Nat.succ k) * m ^ Nat.succ k)
              row := by
        apply finiteNatSum_ext
        intro k
        unfold C
        rw [BEDC.Derived.BinomialIdentitiesUp.binomial_pascal row k]
        exact nat_add_mul_clean
          (BEDC.Derived.BinomialIdentitiesUp.C row k)
          (BEDC.Derived.BinomialIdentitiesUp.C row (Nat.succ k))
          (m ^ Nat.succ k)
      rw [pascalTerms]
      rw [finiteNatSum_add]
      have firstSum :
          finiteNatSum (fun k => C row k * m ^ Nat.succ k) row =
            m * weightedBinomialSum m row := by
        rw [show finiteNatSum (fun k => C row k * m ^ Nat.succ k) row =
            finiteNatSum (fun k => m * (C row k * m ^ k)) row by
          apply finiteNatSum_ext
          intro k
          exact weighted_term_succ m row k]
        exact finiteNatSum_mul_left m (fun k => C row k * m ^ k) row
      have secondSum :
          finiteNatSum (fun k => C row (Nat.succ k) * m ^ Nat.succ k) row =
            shiftedWeightedBinomialSum m row := by
        have lastZero :
            (fun k => C row (Nat.succ k) * m ^ Nat.succ k) (Nat.succ n) = 0 := by
          change C (Nat.succ n) (Nat.succ (Nat.succ n)) *
              m ^ Nat.succ (Nat.succ n) = 0
          exact binomial_above_zero_term (Nat.succ n) m
        rw [finiteNatSum_succ_zero_tail
          (fun k => C row (Nat.succ k) * m ^ Nat.succ k) n lastZero]
        rfl
      rw [firstSum]
      rw [secondSum]
      rfl

theorem weightedBinomialSum_succ (m n : Nat) :
    weightedBinomialSum m (Nat.succ n) =
      m * weightedBinomialSum m n + weightedBinomialSum m n := by
  rw [weightedBinomialSum_succ_decomp]
  rw [shiftedWeightedBinomialSum_succ]
  have tail := weightedBinomialSum_tail_decomp m n
  calc
    1 + (m * weightedBinomialSum m n + shiftedWeightedBinomialSum m n) =
        m * weightedBinomialSum m n +
          (1 + shiftedWeightedBinomialSum m n) := by
      rw [Nat.add_left_comm 1 (m * weightedBinomialSum m n)
        (shiftedWeightedBinomialSum m n)]
    _ = m * weightedBinomialSum m n + weightedBinomialSum m n := by
      rw [← tail]

theorem weightedBinomialSum_pow (m n : Nat) :
    weightedBinomialSum m n = Nat.succ m ^ n := by
  induction n with
  | zero =>
      unfold weightedBinomialSum finiteNatSum
      rfl
  | succ n ih =>
      rw [weightedBinomialSum_succ]
      rw [ih]
      rw [Nat.pow_succ]
      change m * Nat.succ m ^ n + Nat.succ m ^ n =
        Nat.succ m ^ n * Nat.succ m
      rw [Nat.mul_succ]
      rw [Nat.mul_comm (Nat.succ m ^ n) m]

theorem multinomial_coefficients_sum_pow (m n : Nat) :
    multinomialCoefficientSum m n = m ^ n := by
  induction m generalizing n with
  | zero =>
      cases n with
      | zero =>
          rfl
      | succ n =>
          rfl
  | succ m ihM =>
      rw [multinomialCoefficientSum_succ]
      have layer :
        finiteNatSum (fun k => C n k * multinomialCoefficientSum m k) n =
            finiteNatSum (fun k => C n k * m ^ k) n := by
        apply finiteNatSum_ext
        intro k
        rw [ihM k]
      rw [layer]
      exact weightedBinomialSum_pow m n

theorem MultinomialTheoremUp_constructive_export :
    (∀ n : Nat, ∀ ks : List Nat, multinomialWeight ks = n ->
      multinomialCoefficient n ks * multinomialFactorialDenominator ks =
        BEDC.Derived.PochhammerUp.natFactorialCount n) ∧
      (∀ m n : Nat, multinomialCoefficientSum m n = m ^ n) ∧
      (∀ k l : Nat, multinomialCoefficient (k + l) [k, l] = C (k + l) k) ∧
      (∀ ks : List BHist, UnaryHistory (multinomialFn ks)) := by
  constructor
  · intro n ks total
    exact multinomial_coefficient_factorial_identity n ks total
  · constructor
    · intro m n
      exact multinomial_coefficients_sum_pow m n
    · constructor
      · intro k l
        exact multinomial_binary_degenerates_to_binomial k l
      · intro ks
        exact multinomialFn_unary_result ks

end BEDC.Derived.MultinomialTheoremUp
