import BEDC.Derived.PolygonalNumberUp
import BEDC.Derived.TetrahedralUp

namespace BEDC.Derived.PronicNumberUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.IntUp (natToUnary natToUnary_unary natToUnary_length)

abbrev triangularNumber : Nat -> Nat :=
  BEDC.Derived.PolygonalNumberUp.triangularNumber

abbrev squareNumber : Nat -> Nat :=
  BEDC.Derived.PolygonalNumberUp.squareNumber

abbrev triangularPrefix : Nat -> Nat :=
  BEDC.Derived.TetrahedralUp.triangularPrefix

abbrev tetrahedralNumber : Nat -> Nat :=
  BEDC.Derived.TetrahedralUp.tetrahedralNumber

def pronicNumber (n : Nat) : Nat :=
  n * Nat.succ n

def pronicFn (n : BHist) : BHist :=
  natToUnary (pronicNumber (bwordLength n))

def pronicPrefixSum : Nat -> Nat
  | 0 => 0
  | Nat.succ n => pronicPrefixSum n + pronicNumber n

def IsPerfectSquare (n : Nat) : Prop :=
  ∃ root : Nat, n = squareNumber root

theorem pronicFn_unary (n : BHist) :
    UnaryHistory (pronicFn n) := by
  unfold pronicFn
  exact natToUnary_unary _

theorem pronicNumber_formula (n : Nat) :
    pronicNumber n = n * Nat.succ n := by
  rfl

theorem pronic_eq_two_mul_triangular (n : Nat) :
    pronicNumber n = 2 * triangularNumber n := by
  unfold pronicNumber
  exact (BEDC.Derived.PolygonalNumberUp.triangular_double_relation n).symm

theorem pronic_eq_square_add_self (n : Nat) :
    pronicNumber n = squareNumber n + n := by
  unfold pronicNumber
  change n * Nat.succ n = n * n + n
  exact Nat.mul_succ n n

theorem square_succ_eq_pronic_add_succ (n : Nat) :
    squareNumber (Nat.succ n) = pronicNumber n + Nat.succ n := by
  calc
    squareNumber (Nat.succ n) = squareNumber n + n + Nat.succ n :=
      BEDC.Derived.PolygonalUp.square_succ n
    _ = pronicNumber n + Nat.succ n :=
      congrArg (fun x => x + Nat.succ n) (pronic_eq_square_add_self n).symm

theorem pronic_between_adjacent_squares (n : Nat) :
    pronicNumber n = squareNumber n + n ∧
      squareNumber (Nat.succ n) = pronicNumber n + Nat.succ n := by
  constructor
  · exact pronic_eq_square_add_self n
  · exact square_succ_eq_pronic_add_succ n

theorem pronicPrefixSum_zero :
    pronicPrefixSum 0 = 0 := by
  rfl

theorem pronicPrefixSum_succ (n : Nat) :
    pronicPrefixSum (Nat.succ n) = pronicPrefixSum n + pronicNumber n := by
  rfl

theorem pronicPrefixSum_succ_triangular_step (n : Nat) :
    pronicPrefixSum (Nat.succ n) =
      pronicPrefixSum n + 2 * triangularNumber n := by
  rw [pronicPrefixSum_succ]
  rw [pronic_eq_two_mul_triangular]

theorem pronicPrefixSum_succ_eq_two_triangularPrefix (n : Nat) :
    pronicPrefixSum (Nat.succ n) = 2 * triangularPrefix n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [pronicPrefixSum_succ]
      rw [pronic_eq_two_mul_triangular]
      rw [ih]
      unfold triangularPrefix
      rw [BEDC.Derived.TetrahedralUp.triangularPrefix_succ]
      exact (Nat.mul_add 2
        (BEDC.Derived.TetrahedralUp.triangularPrefix n)
        (triangularNumber (Nat.succ n))).symm

theorem pronicPrefixSum_succ_eq_two_tetrahedral (n : Nat) :
    pronicPrefixSum (Nat.succ n) = 2 * tetrahedralNumber n := by
  rw [pronicPrefixSum_succ_eq_two_triangularPrefix]
  unfold triangularPrefix tetrahedralNumber
  rw [BEDC.Derived.TetrahedralUp.tetrahedral_sum_triangular]

private theorem squareNumber_mono {m n : Nat} :
    m ≤ n -> squareNumber m ≤ squareNumber n := by
  intro h
  change m * m ≤ n * n
  exact Nat.mul_le_mul h h

theorem square_lt_pronic_of_pos {n : Nat} :
    0 < n -> squareNumber n < pronicNumber n := by
  intro nPos
  rw [pronic_eq_square_add_self]
  exact Nat.lt_add_of_pos_right nPos

theorem pronic_lt_next_square (n : Nat) :
    pronicNumber n < squareNumber (Nat.succ n) := by
  calc
    pronicNumber n < pronicNumber n + Nat.succ n :=
      Nat.lt_add_of_pos_right (Nat.succ_pos n)
    _ = squareNumber (Nat.succ n) :=
      (square_succ_eq_pronic_add_succ n).symm

theorem pronic_not_square_of_pos (n root : Nat) :
    0 < n -> pronicNumber n = squareNumber root -> False := by
  intro nPos squareEq
  cases Nat.lt_or_ge root (Nat.succ n) with
  | inl rootLtSucc =>
      have rootLeN : root ≤ n := Nat.le_of_lt_succ rootLtSucc
      have rootSquareLe : squareNumber root ≤ squareNumber n :=
        squareNumber_mono rootLeN
      have lowerGap : squareNumber n < pronicNumber n :=
        square_lt_pronic_of_pos nPos
      have impossible : squareNumber root < squareNumber root := by
        calc
          squareNumber root ≤ squareNumber n := rootSquareLe
          _ < pronicNumber n := lowerGap
          _ = squareNumber root := squareEq
      exact Nat.lt_irrefl (squareNumber root) impossible
  | inr succLeRoot =>
      have nextSquareLe : squareNumber (Nat.succ n) ≤ squareNumber root :=
        squareNumber_mono succLeRoot
      have upperGap : pronicNumber n < squareNumber (Nat.succ n) :=
        pronic_lt_next_square n
      have impossible : squareNumber root < squareNumber root := by
        calc
          squareNumber root = pronicNumber n := squareEq.symm
          _ < squareNumber (Nat.succ n) := upperGap
          _ ≤ squareNumber root := nextSquareLe
      exact Nat.lt_irrefl (squareNumber root) impossible

theorem pronic_not_perfect_square_of_pos (n : Nat) :
    0 < n -> IsPerfectSquare (pronicNumber n) -> False := by
  intro nPos squareWitness
  cases squareWitness with
  | intro root squareEq =>
      exact pronic_not_square_of_pos n root nPos squareEq

theorem pronicFn_natToUnary (n : Nat) :
    pronicFn (natToUnary n) = natToUnary (pronicNumber n) := by
  unfold pronicFn
  rw [natToUnary_length]

theorem PronicNumberUp_constructive_export :
    (∀ n : Nat, pronicNumber n = n * Nat.succ n) ∧
      (∀ n : Nat, pronicNumber n = 2 * triangularNumber n) ∧
      (∀ n : Nat, pronicNumber n = squareNumber n + n) ∧
      (∀ n : Nat, squareNumber (Nat.succ n) = pronicNumber n + Nat.succ n) ∧
      (∀ n : Nat, pronicPrefixSum (Nat.succ n) = pronicPrefixSum n + pronicNumber n) ∧
      (∀ n : Nat,
        pronicPrefixSum (Nat.succ n) =
          pronicPrefixSum n + 2 * triangularNumber n) ∧
      (∀ n : Nat,
        pronicPrefixSum (Nat.succ n) = 2 * triangularPrefix n) ∧
      (∀ n : Nat,
        pronicPrefixSum (Nat.succ n) = 2 * tetrahedralNumber n) ∧
      (∀ n : Nat, 0 < n -> IsPerfectSquare (pronicNumber n) -> False) := by
  constructor
  · intro n
    exact pronicNumber_formula n
  · constructor
    · intro n
      exact pronic_eq_two_mul_triangular n
    · constructor
      · intro n
        exact pronic_eq_square_add_self n
      · constructor
        · intro n
          exact square_succ_eq_pronic_add_succ n
        · constructor
          · intro n
            exact pronicPrefixSum_succ n
          · constructor
            · intro n
              exact pronicPrefixSum_succ_triangular_step n
            · constructor
              · intro n
                exact pronicPrefixSum_succ_eq_two_triangularPrefix n
              · constructor
                · intro n
                  exact pronicPrefixSum_succ_eq_two_tetrahedral n
                · intro n
                  exact pronic_not_perfect_square_of_pos n

end BEDC.Derived.PronicNumberUp
