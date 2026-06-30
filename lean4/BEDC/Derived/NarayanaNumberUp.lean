import BEDC.Derived.CatalanConvolutionUp
import BEDC.Derived.NarayanaUp
import BEDC.Real.RatNumLogEnclosure

namespace BEDC.Derived.NarayanaNumberUp

abbrev C (n k : Nat) : Nat :=
  BEDC.Derived.BinomialIdentitiesUp.C n k

abbrev finiteNatSum (f : Nat -> Nat) : Nat -> Nat :=
  BEDC.Derived.BinomialIdentitiesUp.finiteFoldNatSum f

abbrev Rat : Type :=
  BEDC.Real.RatNumKernel.Rat

abbrev RatEq : Rat -> Rat -> Prop :=
  BEDC.Derived.RationalUp.RatEq

abbrev ratNat (n : Nat) : Rat :=
  BEDC.Real.RatNumKernel.ratNat n

abbrev ratAdd (x y : Rat) : Rat :=
  BEDC.Derived.RationalUp.ratAdd x y

abbrev ratDivApart (x y : Rat) (hy : BEDC.Derived.RationalUp.ratApart0 y) : Rat :=
  BEDC.Derived.RationalOrderArithUp.ratDivApart x y hy

def narayanaNumerator (n k : Nat) : Nat :=
  C n k * C n (k - 1)

def narayanaNumber (n k : Nat) : Nat :=
  BEDC.Derived.NarayanaUp.narayanaNumber n k

def narayanaRowSum (n : Nat) : Nat :=
  BEDC.Derived.NarayanaUp.narayanaRowSum n

def narayanaNumeratorRowSum : Nat -> Nat
  | 0 => 0
  | Nat.succ n =>
      finiteNatSum (fun k => narayanaNumerator (Nat.succ n) (Nat.succ k)) n

def catalanAdjacentDivision : Nat -> Nat
  | 0 => 1
  | Nat.succ n => C (Nat.succ n + Nat.succ n) n / Nat.succ n

def ratFiniteSum (f : Nat -> Rat) : Nat -> Rat
  | 0 => f 0
  | Nat.succ n => ratAdd (ratFiniteSum f n) (f (Nat.succ n))

def narayanaRatTerm : Nat -> Nat -> Rat
  | 0, _ => BEDC.Derived.RationalUp.ratZero
  | Nat.succ _, 0 => BEDC.Derived.RationalUp.ratZero
  | Nat.succ n, Nat.succ k =>
      ratDivApart
        (ratNat (narayanaNumerator (Nat.succ n) (Nat.succ k)))
        (ratNat (Nat.succ n))
        (BEDC.Real.RatNumLogEnclosure.ratNat_apart0_of_pos (Nat.succ_pos n))

def narayanaRatRowSum : Nat -> Rat
  | 0 => BEDC.Derived.RationalUp.ratZero
  | Nat.succ n => ratFiniteSum (fun k => narayanaRatTerm (Nat.succ n) (Nat.succ k)) n

def catalanAdjacentRatDivision : Nat -> Rat
  | 0 => ratNat 1
  | Nat.succ n =>
      ratDivApart
        (ratNat (C (Nat.succ n + Nat.succ n) n))
        (ratNat (Nat.succ n))
        (BEDC.Real.RatNumLogEnclosure.ratNat_apart0_of_pos (Nat.succ_pos n))

theorem narayana_number_formula_zero (k : Nat) :
    narayanaNumber 0 k = 0 := by
  exact BEDC.Derived.NarayanaUp.narayana_zero_left k

theorem narayana_number_formula_left_boundary (n : Nat) :
    narayanaNumber (Nat.succ n) 0 = 0 := by
  exact BEDC.Derived.NarayanaUp.narayana_left_boundary n

theorem narayana_number_formula_positive (n k : Nat) :
    narayanaNumber (Nat.succ n) (Nat.succ k) =
      C (Nat.succ n) (Nat.succ k) * C (Nat.succ n) k / Nat.succ n := by
  exact BEDC.Derived.NarayanaUp.narayana_succ_formula n k

theorem narayana_number_symmetry (k l : Nat) :
    narayanaNumber (Nat.succ (k + l)) (Nat.succ k) =
      narayanaNumber (Nat.succ (k + l)) (Nat.succ l) := by
  exact BEDC.Derived.NarayanaUp.narayana_complement_symmetry k l

private theorem nat_add_sub_cancel_right_pure (a b : Nat) :
    a + b - b = a := by
  induction b with
  | zero =>
      rw [Nat.sub_zero, Nat.add_zero]
  | succ b ih =>
      rw [Nat.add_succ]
      rw [Nat.succ_sub_succ_eq_sub]
      exact ih

theorem narayana_symmetric {n k : Nat} (h : k <= n) :
    narayanaNumber (Nat.succ n) (Nat.succ k) =
      narayanaNumber (Nat.succ n) (Nat.succ (n - k)) := by
  obtain ⟨l, hl⟩ := Nat.le.dest h
  have nShape : n = k + l := hl.symm
  have nShapeComm : n = l + k := nShape.trans (Nat.add_comm k l)
  have complement : n - k = l := by
    rw [nShapeComm]
    exact nat_add_sub_cancel_right_pure l k
  rw [complement]
  rw [nShape]
  exact narayana_number_symmetry k l

theorem narayana_number_one_one :
    narayanaNumber 1 1 = 1 := by
  exact BEDC.Derived.NarayanaUp.narayana_one_one

theorem narayana_number_two_row :
    narayanaNumber 2 1 = 1 ∧ narayanaNumber 2 2 = 1 := by
  exact BEDC.Derived.NarayanaUp.narayana_two_row

theorem narayana_number_three_row :
    narayanaNumber 3 1 = 1 ∧ narayanaNumber 3 2 = 3 ∧
      narayanaNumber 3 3 = 1 := by
  exact BEDC.Derived.NarayanaUp.narayana_three_row

private theorem finiteNatSum_ext_le (f g : Nat -> Nat) :
    ∀ n : Nat, (∀ k : Nat, k <= n -> f k = g k) ->
      finiteNatSum f n = finiteNatSum g n
  | 0, same => same 0 (Nat.le_refl 0)
  | Nat.succ n, same => by
      change finiteNatSum f n + f (Nat.succ n) =
        finiteNatSum g n + g (Nat.succ n)
      rw [finiteNatSum_ext_le f g n
        (fun k hk => same k (Nat.le_trans hk (Nat.le_succ n)))]
      rw [same (Nat.succ n) (Nat.le_refl (Nat.succ n))]

private theorem finiteNatSum_succ_decomp (f : Nat -> Nat) :
    ∀ n : Nat,
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

private theorem finiteNatSum_ext (f g : Nat -> Nat)
    (same : ∀ k : Nat, f k = g k) :
    ∀ n : Nat, finiteNatSum f n = finiteNatSum g n
  | 0 => same 0
  | Nat.succ n => by
      change finiteNatSum f n + f (Nat.succ n) =
        finiteNatSum g n + g (Nat.succ n)
      rw [finiteNatSum_ext f g same n]
      rw [same (Nat.succ n)]

private theorem finiteNatSum_reverse (f : Nat -> Nat) :
    ∀ n : Nat, finiteNatSum f n = finiteNatSum (fun k => f (n - k)) n
  | 0 => by
      rfl
  | Nat.succ n => by
      change finiteNatSum f n + f (Nat.succ n) =
        finiteNatSum (fun k => f (Nat.succ n - k)) (Nat.succ n)
      rw [finiteNatSum_succ_decomp (fun k => f (Nat.succ n - k)) n]
      change finiteNatSum f n + f (Nat.succ n) =
        f (Nat.succ n - 0) +
          finiteNatSum (fun k => f (Nat.succ n - Nat.succ k)) n
      rw [Nat.sub_zero]
      have tail :
          finiteNatSum (fun k => f (Nat.succ n - Nat.succ k)) n =
            finiteNatSum (fun k => f (n - k)) n := by
        apply finiteNatSum_ext
        intro k
        rw [Nat.succ_sub_succ_eq_sub]
      rw [tail]
      rw [← finiteNatSum_reverse f n]
      exact Nat.add_comm (finiteNatSum f n) (f (Nat.succ n))

private theorem nat_sub_add_cancel_of_le {a b : Nat} :
    b <= a -> a - b + b = a := by
  intro h
  induction b generalizing a with
  | zero =>
      rw [Nat.sub_zero, Nat.add_zero]
  | succ b ih =>
      cases a with
      | zero =>
          cases h
      | succ a =>
          rw [Nat.succ_sub_succ_eq_sub]
          have hb : b <= a := Nat.le_of_succ_le_succ h
          exact congrArg Nat.succ (ih hb)

private theorem succ_sub_add_of_le {k n : Nat} (h : k <= n) :
    Nat.succ (n - k) + k = Nat.succ n := by
  rw [Nat.succ_add]
  rw [nat_sub_add_cancel_of_le h]

private theorem adjacent_binomial_complement {k n : Nat} (h : k <= n) :
    C (Nat.succ n) (Nat.succ (n - k)) = C (Nat.succ n) k := by
  have raw := BEDC.Derived.NarayanaUp.binomial_complement_symmetry
    (Nat.succ (n - k)) k
  rw [succ_sub_add_of_le h] at raw
  exact raw

private theorem narayanaNumerator_reverse_to_vandermonde_term (n : Nat) :
    finiteNatSum
        (fun k => narayanaNumerator (Nat.succ n) (Nat.succ k)) n =
      finiteNatSum
        (fun k => C (Nat.succ n) k * C (Nat.succ n) (n - k)) n := by
  rw [finiteNatSum_reverse
    (fun k => narayanaNumerator (Nat.succ n) (Nat.succ k)) n]
  apply finiteNatSum_ext_le
  intro k hk
  unfold narayanaNumerator
  change
    C (Nat.succ n) (Nat.succ (n - k)) *
        C (Nat.succ n) (Nat.succ (n - k) - 1) =
      C (Nat.succ n) k * C (Nat.succ n) (n - k)
  rw [adjacent_binomial_complement hk]
  change C (Nat.succ n) k * C (Nat.succ n) (n - k) =
    C (Nat.succ n) k * C (Nat.succ n) (n - k)
  rfl

private theorem finiteNatSum_vandermondeDiagonal (n offset : Nat) :
    ∀ width : Nat,
      finiteNatSum
          (fun k => C n (offset + k) * C n (width - k)) width =
        BEDC.Derived.BinomialIdentitiesUp.vandermondeDiagonalSum n n offset width
  | 0 => by
      change C n (offset + 0) * C n (0 - 0) =
        C n offset * C n 0
      rw [Nat.add_zero]
  | Nat.succ width => by
      rw [finiteNatSum_succ_decomp
        (fun k => C n (offset + k) * C n (Nat.succ width - k)) width]
      change
        C n (offset + 0) * C n (Nat.succ width - 0) +
          finiteNatSum
            (fun k =>
              C n (offset + Nat.succ k) *
                C n (Nat.succ width - Nat.succ k))
            width =
        C n offset * C n (Nat.succ width) +
          BEDC.Derived.BinomialIdentitiesUp.vandermondeDiagonalSum
            n n (Nat.succ offset) width
      rw [Nat.add_zero]
      rw [Nat.sub_zero]
      have tail :
          finiteNatSum
              (fun k =>
                C n (offset + Nat.succ k) *
                  C n (Nat.succ width - Nat.succ k))
              width =
            finiteNatSum
              (fun k => C n (Nat.succ offset + k) * C n (width - k))
              width := by
        apply finiteNatSum_ext
        intro k
        rw [Nat.add_succ]
        rw [Nat.succ_add]
        rw [Nat.succ_sub_succ_eq_sub]
      rw [tail]
      rw [finiteNatSum_vandermondeDiagonal n (Nat.succ offset) width]

theorem narayana_numerator_row_sum_vandermonde (n : Nat) :
    narayanaNumeratorRowSum (Nat.succ n) =
      C (Nat.succ n + Nat.succ n) n := by
  unfold narayanaNumeratorRowSum
  change finiteNatSum (fun k => narayanaNumerator (Nat.succ n) (Nat.succ k)) n =
    C (Nat.succ n + Nat.succ n) n
  rw [narayanaNumerator_reverse_to_vandermonde_term n]
  have diag := finiteNatSum_vandermondeDiagonal (Nat.succ n) 0 n
  have zeroOffset :
      finiteNatSum (fun k => C (Nat.succ n) k * C (Nat.succ n) (n - k)) n =
        finiteNatSum (fun k => C (Nat.succ n) (0 + k) * C (Nat.succ n) (n - k)) n := by
    apply finiteNatSum_ext
    intro k
    rw [Nat.zero_add]
  rw [zeroOffset]
  rw [diag]
  exact (BEDC.Derived.BinomialIdentitiesUp.binomial_vandermonde
    (Nat.succ n) (Nat.succ n) n).symm

theorem narayana_numerator_row_division_eq_adjacent_catalan (n : Nat) :
    narayanaNumeratorRowSum (Nat.succ n) / Nat.succ n =
      catalanAdjacentDivision (Nat.succ n) := by
  rw [narayana_numerator_row_sum_vandermonde n]
  rfl

private theorem ratDivApart_ratNat_sum_common_den (d : Nat) :
    ∀ n : Nat, ∀ f : Nat -> Nat,
      RatEq
        (ratFiniteSum
          (fun k =>
            ratDivApart (ratNat (f k)) (ratNat (Nat.succ d))
              (BEDC.Real.RatNumLogEnclosure.ratNat_apart0_of_pos (Nat.succ_pos d)))
          n)
        (ratDivApart (ratNat (finiteNatSum f n)) (ratNat (Nat.succ d))
          (BEDC.Real.RatNumLogEnclosure.ratNat_apart0_of_pos (Nat.succ_pos d)))
  | 0, _f => BEDC.Derived.RationalUp.RatEq_refl _
  | Nat.succ n, f => by
      let denom := ratNat (Nat.succ d)
      let hden := BEDC.Real.RatNumLogEnclosure.ratNat_apart0_of_pos (Nat.succ_pos d)
      have ih :
          RatEq
            (ratFiniteSum
              (fun k => ratDivApart (ratNat (f k)) denom hden) n)
            (ratDivApart (ratNat (finiteNatSum f n)) denom hden) :=
        ratDivApart_ratNat_sum_common_den d n f
      have addDiv :
          RatEq
            (ratAdd
              (ratDivApart (ratNat (finiteNatSum f n)) denom hden)
              (ratDivApart (ratNat (f (Nat.succ n))) denom hden))
            (ratDivApart
              (ratAdd (ratNat (finiteNatSum f n))
                (ratNat (f (Nat.succ n))))
              denom hden) := by
        unfold ratDivApart BEDC.Derived.RationalOrderArithUp.ratDivApart
        exact BEDC.Derived.RationalUp.RatEq_symm
          (BEDC.Real.RatNumKernel.ratMul_add_right
            (ratNat (finiteNatSum f n))
            (ratNat (f (Nat.succ n)))
            (BEDC.Derived.RationalUp.ratInvApart denom hden))
      exact BEDC.Derived.RationalUp.RatEq_trans _ _ _
        (BEDC.Derived.RationalUp.ratAdd_respects ih
          (BEDC.Derived.RationalUp.RatEq_refl _))
        (BEDC.Derived.RationalUp.RatEq_trans _ _ _ addDiv
          (BEDC.Derived.RationalUp.ratMul_respects
            (BEDC.Real.RatNumLogEnclosure.ratNat_add
              (finiteNatSum f n) (f (Nat.succ n)))
            (BEDC.Derived.RationalUp.RatEq_refl _)))

theorem narayana_rat_row_sum_eq_adjacent_catalan_division (n : Nat) :
    RatEq (narayanaRatRowSum (Nat.succ n))
      (catalanAdjacentRatDivision (Nat.succ n)) := by
  unfold narayanaRatRowSum catalanAdjacentRatDivision narayanaRatTerm
  exact BEDC.Derived.RationalUp.RatEq_trans _ _ _
    (ratDivApart_ratNat_sum_common_den n n
      (fun k => narayanaNumerator (Nat.succ n) (Nat.succ k)))
    (BEDC.Derived.RationalUp.ratMul_respects
      (by
        change RatEq
          (ratNat (narayanaNumeratorRowSum (Nat.succ n)))
          (ratNat (C (Nat.succ n + Nat.succ n) n))
        rw [narayana_numerator_row_sum_vandermonde n]
        exact BEDC.Derived.RationalUp.RatEq_refl _)
      (BEDC.Derived.RationalUp.RatEq_refl _))

theorem catalan_adjacent_small_values :
    catalanAdjacentDivision 0 = 1 ∧ catalanAdjacentDivision 1 = 1 ∧
      catalanAdjacentDivision 2 = 2 ∧ catalanAdjacentDivision 3 = 5 ∧
        catalanAdjacentDivision 4 = 14 := by
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · constructor
        · rfl
        · rfl

theorem NarayanaNumberUp_constructive_export :
    (∀ n k : Nat, narayanaNumber (Nat.succ n) (Nat.succ k) =
      C (Nat.succ n) (Nat.succ k) * C (Nat.succ n) k / Nat.succ n) ∧
      (∀ k l : Nat, narayanaNumber (Nat.succ (k + l)) (Nat.succ k) =
        narayanaNumber (Nat.succ (k + l)) (Nat.succ l)) ∧
      (∀ n k : Nat, k <= n ->
        narayanaNumber (Nat.succ n) (Nat.succ k) =
          narayanaNumber (Nat.succ n) (Nat.succ (n - k))) ∧
      (∀ n : Nat,
        narayanaNumeratorRowSum (Nat.succ n) =
          C (Nat.succ n + Nat.succ n) n) ∧
      (∀ n : Nat,
        narayanaNumeratorRowSum (Nat.succ n) / Nat.succ n =
          catalanAdjacentDivision (Nat.succ n)) ∧
      (∀ n : Nat,
        RatEq (narayanaRatRowSum (Nat.succ n))
          (catalanAdjacentRatDivision (Nat.succ n))) ∧
      catalanAdjacentDivision 4 = 14 ∧
        narayanaNumber 3 1 = 1 ∧ narayanaNumber 3 2 = 3 ∧
          narayanaNumber 3 3 = 1 := by
  constructor
  · intro n k
    exact narayana_number_formula_positive n k
  · constructor
    · intro k l
      exact narayana_number_symmetry k l
    · constructor
      · intro n k h
        exact narayana_symmetric h
      · constructor
        · intro n
          exact narayana_numerator_row_sum_vandermonde n
        · constructor
          · intro n
            exact narayana_numerator_row_division_eq_adjacent_catalan n
          · constructor
            · intro n
              exact narayana_rat_row_sum_eq_adjacent_catalan_division n
            · constructor
              · exact catalan_adjacent_small_values.right.right.right.right
              · constructor
                · exact narayana_number_three_row.left
                · constructor
                  · exact narayana_number_three_row.right.left
                  · exact narayana_number_three_row.right.right

end BEDC.Derived.NarayanaNumberUp
