import BEDC.Derived.BinomialIdentitiesUp
import BEDC.Derived.NarayanaUp

namespace BEDC.Derived.VandermondeChuUp

abbrev C (n k : Nat) : Nat :=
  BEDC.Derived.BinomialIdentitiesUp.C n k

def chuVandermondeSum (m n r : Nat) : Nat :=
  BEDC.Derived.BinomialIdentitiesUp.vandermondeSum m n r

def equalIndexDiagonalSum (m n offset : Nat) : Nat -> Nat
  | 0 => C m offset * C n offset
  | Nat.succ k =>
      C m offset * C n offset +
        equalIndexDiagonalSum m n (Nat.succ offset) k

def equalIndexProductSum (m n : Nat) : Nat :=
  equalIndexDiagonalSum m n 0 n

def squareBinomialSum (n : Nat) : Nat :=
  equalIndexProductSum n n

theorem chu_vandermonde (m n r : Nat) :
    chuVandermondeSum m n r = C (m + n) r := by
  unfold chuVandermondeSum
  exact (BEDC.Derived.BinomialIdentitiesUp.binomial_vandermonde m n r).symm

private theorem binomial_complement_symmetry (k l : Nat) :
    C (k + l) k = C (k + l) l := by
  exact BEDC.Derived.NarayanaUp.binomial_complement_symmetry k l

private theorem offset_add_succ_eq_succ_add (offset k : Nat) :
    offset + Nat.succ k = Nat.succ offset + k := by
  rw [Nat.add_succ]
  rw [Nat.succ_add]

private theorem equalIndexDiagonalSum_to_vandermondeDiagonalSum (m offset : Nat) :
    ∀ k : Nat,
      equalIndexDiagonalSum m (offset + k) offset k =
        BEDC.Derived.BinomialIdentitiesUp.vandermondeDiagonalSum
          m (offset + k) offset k
  | 0 => by
      change C m offset * C (offset + 0) offset =
        C m offset * C (offset + 0) 0
      rw [Nat.add_zero]
      unfold C
      rw [BEDC.Derived.BinomialIdentitiesUp.binomial_self offset]
      rw [BEDC.Derived.BinomialIdentitiesUp.binomial_zero_right offset]
  | Nat.succ k => by
      change C m offset * C (offset + Nat.succ k) offset +
          equalIndexDiagonalSum m (offset + Nat.succ k) (Nat.succ offset) k =
        C m offset * C (offset + Nat.succ k) (Nat.succ k) +
          BEDC.Derived.BinomialIdentitiesUp.vandermondeDiagonalSum
            m (offset + Nat.succ k) (Nat.succ offset) k
      have comp :=
        binomial_complement_symmetry offset (Nat.succ k)
      rw [comp]
      have tail :=
        equalIndexDiagonalSum_to_vandermondeDiagonalSum m (Nat.succ offset) k
      rw [← offset_add_succ_eq_succ_add offset k] at tail
      rw [tail]

theorem equal_index_product_sum (m n : Nat) :
    equalIndexProductSum m n = C (m + n) n := by
  unfold equalIndexProductSum
  have diag := equalIndexDiagonalSum_to_vandermondeDiagonalSum m 0 n
  rw [Nat.zero_add] at diag
  rw [diag]
  exact chu_vandermonde m n n

private theorem central_twice_shape (n : Nat) :
    n + n = 2 * n := by
  rw [Nat.two_mul]

theorem central_binomial_square_sum (n : Nat) :
    squareBinomialSum n = C (2 * n) n := by
  unfold squareBinomialSum
  rw [equal_index_product_sum n n]
  rw [central_twice_shape n]

theorem equal_index_product_sum_complement (m n : Nat) :
    equalIndexProductSum m n = C (m + n) m := by
  rw [equal_index_product_sum m n]
  have symm := binomial_complement_symmetry m n
  exact symm.symm

theorem VandermondeChuUp_constructive_export :
    (∀ m n r : Nat, chuVandermondeSum m n r = C (m + n) r) ∧
      (∀ n : Nat, squareBinomialSum n = C (2 * n) n) ∧
        (∀ m n : Nat, equalIndexProductSum m n = C (m + n) n) := by
  constructor
  · intro m n r
    exact chu_vandermonde m n r
  · constructor
    · intro n
      exact central_binomial_square_sum n
    · intro m n
      exact equal_index_product_sum m n

end BEDC.Derived.VandermondeChuUp
