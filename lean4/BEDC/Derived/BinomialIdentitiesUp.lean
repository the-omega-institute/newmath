import BEDC.Algebra.FiniteFold
import BEDC.Derived.PochhammerUp

namespace BEDC.Derived.BinomialIdentitiesUp

abbrev C (n k : Nat) : Nat :=
  BEDC.Derived.PochhammerUp.natChooseCount n k

def finiteFoldNatSum (f : Nat -> Nat) : Nat -> Nat
  | 0 => f 0
  | Nat.succ n => finiteFoldNatSum f n + f (Nat.succ n)

def rowPrefixSum (n : Nat) : Nat -> Nat :=
  finiteFoldNatSum (fun k => C n k)

def rowSum (n : Nat) : Nat :=
  rowPrefixSum n n

def hockeyStickRangeSum (r : Nat) : Nat -> Nat
  | 0 => C r r
  | Nat.succ n => hockeyStickRangeSum r n + C (r + Nat.succ n) r

def vandermondeDiagonalSum (m n offset : Nat) : Nat -> Nat
  | 0 => C m offset * C n 0
  | Nat.succ k =>
      C m offset * C n (Nat.succ k) +
        vandermondeDiagonalSum m n (Nat.succ offset) k

def vandermondeSum (m n k : Nat) : Nat :=
  vandermondeDiagonalSum m n 0 k

theorem binomial_pascal (n k : Nat) :
    C (Nat.succ n) (Nat.succ k) = C n k + C n (Nat.succ k) := by
  exact BEDC.Derived.PochhammerUp.natChooseCount_pascal n k

theorem binomial_zero_right (n : Nat) :
    C n 0 = 1 := by
  exact BEDC.Derived.PochhammerUp.natChooseCount_zero_right n

theorem binomial_zero_left_succ (k : Nat) :
    C 0 (Nat.succ k) = 0 := by
  unfold C BEDC.Derived.PochhammerUp.natChooseCount
  unfold BEDC.Derived.FactorialUp.natChooseFn
  rw [BEDC.Derived.IntUp.natToUnary_length]
  rw [BEDC.Derived.IntUp.natToUnary_length]
  cases k <;> rfl

theorem binomial_self_and_above :
    ∀ n : Nat, C n n = 1 ∧
      ∀ extra : Nat, C n (Nat.succ (n + extra)) = 0
  | 0 => by
      constructor
      · exact binomial_zero_right 0
      · intro extra
        exact binomial_zero_left_succ extra
  | Nat.succ n => by
      have ih := binomial_self_and_above n
      constructor
      · change C (Nat.succ n) (Nat.succ n) = 1
        rw [binomial_pascal n n]
        rw [ih.left]
        rw [ih.right 0]
      · intro extra
        rw [Nat.succ_add]
        change C (Nat.succ n) (Nat.succ (Nat.succ (n + extra))) = 0
        rw [binomial_pascal n (Nat.succ (n + extra))]
        rw [ih.right extra]
        have shifted : n + Nat.succ extra = Nat.succ (n + extra) := Nat.add_succ n extra
        rw [← shifted]
        rw [ih.right (Nat.succ extra)]

theorem binomial_self (n : Nat) :
    C n n = 1 :=
  (binomial_self_and_above n).left

theorem binomial_above (n extra : Nat) :
    C n (Nat.succ (n + extra)) = 0 :=
  (binomial_self_and_above n).right extra

private theorem nat_mul_one_clean (n : Nat) :
    n * 1 = n := by
  exact Nat.mul_one n

private theorem nat_one_mul_clean (n : Nat) :
    1 * n = n := by
  exact Nat.one_mul n

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

private theorem succ_add_eq_succ_add (m n : Nat) :
    Nat.succ m + n = Nat.succ (m + n) := by
  rw [Nat.succ_eq_add_one]
  rw [Nat.succ_eq_add_one]
  rw [Nat.add_assoc m 1 n]
  rw [Nat.add_comm 1 n]
  rw [← Nat.add_assoc m n 1]

private theorem succ_add_target_shape (m n : Nat) :
    Nat.succ (m + n) = m + 1 + n := by
  rw [Nat.succ_eq_add_one]
  rw [Nat.add_assoc m 1 n]
  rw [Nat.add_comm 1 n]
  rw [← Nat.add_assoc m n 1]

private theorem diagonal_zero_left_succ_offset (n offset : Nat) :
    ∀ k : Nat, vandermondeDiagonalSum 0 n (Nat.succ offset) k = 0
  | 0 => by
      change C 0 (Nat.succ offset) * C n 0 = 0
      rw [binomial_zero_left_succ offset]
      exact Nat.zero_mul (C n 0)
  | Nat.succ k => by
      change C 0 (Nat.succ offset) * C n (Nat.succ k) +
          vandermondeDiagonalSum 0 n (Nat.succ (Nat.succ offset)) k = 0
      rw [binomial_zero_left_succ offset]
      rw [diagonal_zero_left_succ_offset n (Nat.succ offset) k]
      rw [Nat.zero_mul]

private theorem vandermonde_zero_left (n k : Nat) :
    vandermondeDiagonalSum 0 n 0 k = C n k := by
  cases k with
  | zero =>
      change C 0 0 * C n 0 = C n 0
      rw [binomial_zero_right 0]
      exact nat_one_mul_clean (C n 0)
  | succ k =>
      change C 0 0 * C n (Nat.succ k) +
          vandermondeDiagonalSum 0 n 1 k = C n (Nat.succ k)
      rw [binomial_zero_right 0]
      rw [nat_one_mul_clean (C n (Nat.succ k))]
      rw [diagonal_zero_left_succ_offset n 0 k]
      exact Nat.add_zero (C n (Nat.succ k))

private theorem diagonal_pascal_left_succ_offset (m n offset : Nat) :
    ∀ k : Nat,
      vandermondeDiagonalSum (Nat.succ m) n (Nat.succ offset) k =
        vandermondeDiagonalSum m n offset k +
          vandermondeDiagonalSum m n (Nat.succ offset) k
  | 0 => by
      change C (Nat.succ m) (Nat.succ offset) * C n 0 =
        C m offset * C n 0 + C m (Nat.succ offset) * C n 0
      rw [binomial_pascal m offset]
      exact nat_add_mul_clean (C m offset) (C m (Nat.succ offset)) (C n 0)
  | Nat.succ k => by
      change C (Nat.succ m) (Nat.succ offset) * C n (Nat.succ k) +
          vandermondeDiagonalSum (Nat.succ m) n (Nat.succ (Nat.succ offset)) k =
        (C m offset * C n (Nat.succ k) +
          vandermondeDiagonalSum m n (Nat.succ offset) k) +
          (C m (Nat.succ offset) * C n (Nat.succ k) +
          vandermondeDiagonalSum m n (Nat.succ (Nat.succ offset)) k)
      rw [binomial_pascal m offset]
      rw [nat_add_mul_clean (C m offset) (C m (Nat.succ offset)) (C n (Nat.succ k))]
      rw [diagonal_pascal_left_succ_offset m n (Nat.succ offset) k]
      calc
        (C m offset * C n (Nat.succ k) +
              C m (Nat.succ offset) * C n (Nat.succ k)) +
            (vandermondeDiagonalSum m n (Nat.succ offset) k +
              vandermondeDiagonalSum m n (Nat.succ (Nat.succ offset)) k) =
            C m offset * C n (Nat.succ k) +
              (C m (Nat.succ offset) * C n (Nat.succ k) +
                (vandermondeDiagonalSum m n (Nat.succ offset) k +
                  vandermondeDiagonalSum m n (Nat.succ (Nat.succ offset)) k)) :=
          Nat.add_assoc _ _ _
        _ = C m offset * C n (Nat.succ k) +
              (vandermondeDiagonalSum m n (Nat.succ offset) k +
                (C m (Nat.succ offset) * C n (Nat.succ k) +
                  vandermondeDiagonalSum m n (Nat.succ (Nat.succ offset)) k)) :=
          congrArg (fun x => C m offset * C n (Nat.succ k) + x)
            (Nat.add_left_comm
              (C m (Nat.succ offset) * C n (Nat.succ k))
              (vandermondeDiagonalSum m n (Nat.succ offset) k)
              (vandermondeDiagonalSum m n (Nat.succ (Nat.succ offset)) k))
        _ = (C m offset * C n (Nat.succ k) +
              vandermondeDiagonalSum m n (Nat.succ offset) k) +
              (C m (Nat.succ offset) * C n (Nat.succ k) +
                vandermondeDiagonalSum m n (Nat.succ (Nat.succ offset)) k) :=
          (Nat.add_assoc
            (C m offset * C n (Nat.succ k))
            (vandermondeDiagonalSum m n (Nat.succ offset) k)
            (C m (Nat.succ offset) * C n (Nat.succ k) +
              vandermondeDiagonalSum m n (Nat.succ (Nat.succ offset)) k)).symm

private theorem diagonal_succ_left_zero_succ (m n k : Nat) :
    vandermondeDiagonalSum (Nat.succ m) n 0 (Nat.succ k) =
      vandermondeDiagonalSum m n 0 k +
        vandermondeDiagonalSum m n 0 (Nat.succ k) := by
  change C (Nat.succ m) 0 * C n (Nat.succ k) +
      vandermondeDiagonalSum (Nat.succ m) n 1 k =
    vandermondeDiagonalSum m n 0 k +
      (C m 0 * C n (Nat.succ k) +
        vandermondeDiagonalSum m n 1 k)
  rw [binomial_zero_right (Nat.succ m)]
  rw [binomial_zero_right m]
  repeat rw [nat_one_mul_clean (C n (Nat.succ k))]
  rw [diagonal_pascal_left_succ_offset m n 0 k]
  calc
    C n (Nat.succ k) +
        (vandermondeDiagonalSum m n 0 k + vandermondeDiagonalSum m n 1 k) =
        vandermondeDiagonalSum m n 0 k +
          (C n (Nat.succ k) + vandermondeDiagonalSum m n 1 k) :=
      Nat.add_left_comm (C n (Nat.succ k))
        (vandermondeDiagonalSum m n 0 k) (vandermondeDiagonalSum m n 1 k)

theorem binomial_vandermonde (m n k : Nat) :
    C (m + n) k = vandermondeSum m n k := by
  unfold vandermondeSum
  induction m generalizing k with
  | zero =>
      rw [Nat.zero_add]
      exact (vandermonde_zero_left n k).symm
  | succ m ih =>
      cases k with
      | zero =>
          change C (Nat.succ m + n) 0 = C (Nat.succ m) 0 * C n 0
          rw [binomial_zero_right (Nat.succ m + n)]
          rw [binomial_zero_right (Nat.succ m)]
          rw [binomial_zero_right n]
      | succ k =>
          rw [succ_add_eq_succ_add m n]
          rw [binomial_pascal (m + n) k]
          rw [ih k]
          rw [ih (Nat.succ k)]
          exact (diagonal_succ_left_zero_succ m n k).symm

private theorem hockey_base_self (r : Nat) :
    C r r = C (Nat.succ (r + 0)) (Nat.succ r) := by
  rw [Nat.add_zero]
  rw [binomial_self r]
  rw [binomial_self (Nat.succ r)]

theorem binomial_hockey_stick (r extra : Nat) :
    hockeyStickRangeSum r extra =
      C (Nat.succ (r + extra)) (Nat.succ r) := by
  induction extra with
  | zero =>
      exact hockey_base_self r
  | succ extra ih =>
      change hockeyStickRangeSum r extra + C (r + Nat.succ extra) r =
        C (Nat.succ (r + Nat.succ extra)) (Nat.succ r)
      rw [ih]
      rw [Nat.add_succ]
      change C (Nat.succ (r + extra)) (Nat.succ r) +
          C (Nat.succ (r + extra)) r =
        C (Nat.succ (Nat.succ (r + extra))) (Nat.succ r)
      rw [binomial_pascal (Nat.succ (r + extra)) r]
      exact Nat.add_comm (C (Nat.succ (r + extra)) (Nat.succ r))
        (C (Nat.succ (r + extra)) r)

private theorem rowPrefix_pascal (n : Nat) :
    ∀ k : Nat,
      rowPrefixSum (Nat.succ n) (Nat.succ k) =
        rowPrefixSum n k + rowPrefixSum n (Nat.succ k)
  | 0 => by
      change C (Nat.succ n) 0 + C (Nat.succ n) 1 =
        C n 0 + (C n 0 + C n 1)
      rw [binomial_zero_right (Nat.succ n)]
      rw [binomial_zero_right n]
      rw [binomial_pascal n 0]
      rw [binomial_zero_right n]
  | Nat.succ k => by
      change rowPrefixSum (Nat.succ n) (Nat.succ k) +
          C (Nat.succ n) (Nat.succ (Nat.succ k)) =
        rowPrefixSum n (Nat.succ k) +
          (rowPrefixSum n (Nat.succ k) + C n (Nat.succ (Nat.succ k)))
      rw [rowPrefix_pascal n k]
      rw [binomial_pascal n (Nat.succ k)]
      calc
        (rowPrefixSum n k + rowPrefixSum n (Nat.succ k)) +
            (C n (Nat.succ k) + C n (Nat.succ (Nat.succ k))) =
            rowPrefixSum n k +
              (rowPrefixSum n (Nat.succ k) +
                (C n (Nat.succ k) + C n (Nat.succ (Nat.succ k)))) :=
          Nat.add_assoc _ _ _
        _ = rowPrefixSum n k +
              (C n (Nat.succ k) +
                (rowPrefixSum n (Nat.succ k) +
                  C n (Nat.succ (Nat.succ k)))) :=
          congrArg (fun x => rowPrefixSum n k + x)
            (Nat.add_left_comm (rowPrefixSum n (Nat.succ k))
              (C n (Nat.succ k)) (C n (Nat.succ (Nat.succ k))))
        _ = (rowPrefixSum n k + C n (Nat.succ k)) +
              (rowPrefixSum n (Nat.succ k) +
                C n (Nat.succ (Nat.succ k))) :=
          (Nat.add_assoc (rowPrefixSum n k) (C n (Nat.succ k))
            (rowPrefixSum n (Nat.succ k) +
              C n (Nat.succ (Nat.succ k)))).symm
        _ = rowPrefixSum n (Nat.succ k) +
              (rowPrefixSum n (Nat.succ k) +
                C n (Nat.succ (Nat.succ k))) := by
          rfl

private theorem rowPrefix_above_self (n : Nat) :
    rowPrefixSum n (Nat.succ n) = rowPrefixSum n n := by
  change rowPrefixSum n n + C n (Nat.succ n) = rowPrefixSum n n
  rw [binomial_above n 0]
  exact Nat.add_zero (rowPrefixSum n n)

private theorem two_mul_as_add (n : Nat) :
    n + n = n * 2 := by
  rw [Nat.mul_succ]
  rw [Nat.mul_one]

theorem binomial_row_sum_double (n : Nat) :
    rowSum (Nat.succ n) = rowSum n + rowSum n := by
  unfold rowSum
  rw [rowPrefix_pascal n n]
  rw [rowPrefix_above_self n]

private theorem rowSum_zero :
    rowSum 0 = 1 := by
  unfold rowSum rowPrefixSum finiteFoldNatSum
  exact binomial_zero_right 0

theorem binomial_row_sum (n : Nat) :
    rowSum n = 2 ^ n := by
  induction n with
  | zero =>
      rw [rowSum_zero]
  | succ n ih =>
      rw [binomial_row_sum_double n]
      rw [ih]
      rw [Nat.pow_succ]
      exact two_mul_as_add (2 ^ n)

theorem natChooseCount_factorial_source (n k : Nat) :
    C n k =
      BEDC.FKernel.ExternalBinary.bwordLength
        (BEDC.Derived.FactorialUp.natChooseFn
          (BEDC.Derived.IntUp.natToUnary n)
          (BEDC.Derived.IntUp.natToUnary k)) := by
  rfl

theorem BinomialIdentitiesUp_constructive_export :
    (∀ n k : Nat, C (Nat.succ n) (Nat.succ k) = C n k + C n (Nat.succ k)) ∧
      (∀ m n k : Nat, C (m + n) k = vandermondeSum m n k) ∧
      (∀ r extra : Nat,
        hockeyStickRangeSum r extra =
          C (Nat.succ (r + extra)) (Nat.succ r)) ∧
      (∀ n : Nat, rowSum n = 2 ^ n) := by
  constructor
  · intro n k
    exact binomial_pascal n k
  · constructor
    · intro m n k
      exact binomial_vandermonde m n k
    · constructor
      · intro r extra
        exact binomial_hockey_stick r extra
      · intro n
        exact binomial_row_sum n

end BEDC.Derived.BinomialIdentitiesUp
