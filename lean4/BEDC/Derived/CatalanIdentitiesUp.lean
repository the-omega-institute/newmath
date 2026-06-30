import BEDC.Algebra.FiniteFold
import BEDC.Derived.CatalanConvolutionUp

namespace BEDC.Derived.CatalanIdentitiesUp

abbrev C (n k : Nat) : Nat :=
  BEDC.Derived.BinomialIdentitiesUp.C n k

abbrev cat (n : Nat) : Nat :=
  BEDC.Derived.CatalanConvolutionUp.catalanNumber n

abbrev finiteNatSum (f : Nat -> Nat) : Nat -> Nat :=
  BEDC.Derived.BinomialIdentitiesUp.finiteFoldNatSum f

def catalanConvolutionFold (n : Nat) : Nat :=
  finiteNatSum (fun i => cat i * cat (n - i)) n

theorem listNatSum_append :
    ∀ xs ys : List Nat,
      BEDC.Derived.CatalanConvolutionUp.listNatSum (xs ++ ys) =
        BEDC.Derived.CatalanConvolutionUp.listNatSum xs +
          BEDC.Derived.CatalanConvolutionUp.listNatSum ys
  | [], ys => by
      rw [List.nil_append]
      exact (Nat.zero_add
        (BEDC.Derived.CatalanConvolutionUp.listNatSum ys)).symm
  | x :: xs, ys => by
      change x + BEDC.Derived.CatalanConvolutionUp.listNatSum (xs ++ ys) =
        x + BEDC.Derived.CatalanConvolutionUp.listNatSum xs +
          BEDC.Derived.CatalanConvolutionUp.listNatSum ys
      rw [listNatSum_append xs ys]
      exact (Nat.add_assoc x
        (BEDC.Derived.CatalanConvolutionUp.listNatSum xs)
        (BEDC.Derived.CatalanConvolutionUp.listNatSum ys)).symm

theorem listNatSum_singleton (x : Nat) :
    BEDC.Derived.CatalanConvolutionUp.listNatSum [x] = x := by
  exact Nat.add_zero x

theorem listMap_append_clean {A B : Type} (f : A -> B) :
    ∀ xs ys : List A, List.map f (xs ++ ys) = List.map f xs ++ List.map f ys
  | [], _ys => by
      rfl
  | x :: xs, ys => by
      exact congrArg (List.cons (f x)) (listMap_append_clean f xs ys)

theorem listNatSum_natRange_map_finiteNatSum (f : Nat -> Nat) :
    ∀ n : Nat,
      BEDC.Derived.CatalanConvolutionUp.listNatSum
          ((BEDC.Derived.CatalanConvolutionUp.natRange n).map f) =
        finiteNatSum f n
  | 0 => by
      change f 0 + 0 = f 0
      exact Nat.add_zero (f 0)
  | Nat.succ n => by
      change
        BEDC.Derived.CatalanConvolutionUp.listNatSum
            (((BEDC.Derived.CatalanConvolutionUp.natRange n) ++ [Nat.succ n]).map f) =
          finiteNatSum f n + f (Nat.succ n)
      rw [listMap_append_clean]
      rw [listNatSum_append]
      rw [listNatSum_natRange_map_finiteNatSum f n]
      change finiteNatSum f n +
          BEDC.Derived.CatalanConvolutionUp.listNatSum [f (Nat.succ n)] =
        finiteNatSum f n + f (Nat.succ n)
      rw [listNatSum_singleton]

private theorem listNthD_append_left_of_lt_listLen :
    ∀ xs ys : List Nat, ∀ i : Nat,
      i < BEDC.Derived.CatalanConvolutionUp.listLen xs ->
        BEDC.Derived.CatalanConvolutionUp.listNthD (xs ++ ys) i =
          BEDC.Derived.CatalanConvolutionUp.listNthD xs i
  | [], _ys, _i, h => by
      cases h
  | _x :: _xs, _ys, 0, _h => by
      rfl
  | _x :: xs, ys, Nat.succ i, h => by
      exact listNthD_append_left_of_lt_listLen xs ys i
        (Nat.lt_of_succ_lt_succ h)

private theorem nat_le_add_right_self (i extra : Nat) :
    i <= i + extra := by
  induction extra with
  | zero =>
      rw [Nat.add_zero]
      exact Nat.le_refl i
  | succ extra ih =>
      rw [Nat.add_succ]
      exact Nat.le_trans ih (Nat.le_succ (i + extra))

private theorem lt_succ_add_right (i extra : Nat) :
    i < Nat.succ (i + extra) := by
  exact Nat.succ_le_succ (nat_le_add_right_self i extra)

theorem catalanPrefix_nth_stable_add (i extra : Nat) :
    BEDC.Derived.CatalanConvolutionUp.listNthD
        (BEDC.Derived.CatalanConvolutionUp.catalanPrefix (i + extra)) i =
      cat i := by
  induction extra with
  | zero =>
      rw [Nat.add_zero]
      rfl
  | succ extra ih =>
      rw [Nat.add_succ]
      change
        BEDC.Derived.CatalanConvolutionUp.listNthD
            (BEDC.Derived.CatalanConvolutionUp.catalanPrefix (Nat.succ (i + extra))) i =
          cat i
      change
        BEDC.Derived.CatalanConvolutionUp.listNthD
            (BEDC.Derived.CatalanConvolutionUp.catalanPrefix (i + extra) ++
              [BEDC.Derived.CatalanConvolutionUp.catalanPrefixConvolution
                (BEDC.Derived.CatalanConvolutionUp.catalanPrefix (i + extra))
                (i + extra)]) i =
          cat i
      rw [listNthD_append_left_of_lt_listLen
        (BEDC.Derived.CatalanConvolutionUp.catalanPrefix (i + extra))
        [BEDC.Derived.CatalanConvolutionUp.catalanPrefixConvolution
          (BEDC.Derived.CatalanConvolutionUp.catalanPrefix (i + extra))
          (i + extra)]
        i]
      · exact ih
      · rw [BEDC.Derived.CatalanConvolutionUp.catalanPrefix_listLen]
        exact lt_succ_add_right i extra

private theorem le_to_add_tail {i n : Nat} :
    i <= n -> ∃ extra : Nat, n = i + extra := by
  intro h
  obtain ⟨extra, hEq⟩ := Nat.le.dest h
  exact ⟨extra, hEq.symm⟩

theorem catalanPrefix_nth_stable_of_le {i n : Nat} (h : i <= n) :
    BEDC.Derived.CatalanConvolutionUp.listNthD
        (BEDC.Derived.CatalanConvolutionUp.catalanPrefix n) i =
      cat i := by
  obtain ⟨extra, hEq⟩ := le_to_add_tail h
  rw [hEq]
  exact catalanPrefix_nth_stable_add i extra

private theorem product_from_prefix_eq_cat_product {n i : Nat} (h : i <= n) :
    BEDC.Derived.CatalanConvolutionUp.listNthD
        (BEDC.Derived.CatalanConvolutionUp.catalanPrefix n) i *
      BEDC.Derived.CatalanConvolutionUp.listNthD
        (BEDC.Derived.CatalanConvolutionUp.catalanPrefix n) (n - i) =
      cat i * cat (n - i) := by
  have leftStable := catalanPrefix_nth_stable_of_le h
  have rightLe : n - i <= n := by
    exact Nat.sub_le n i
  have rightStable := catalanPrefix_nth_stable_of_le rightLe
  rw [leftStable, rightStable]

private theorem finiteNatSum_congr_le (f g : Nat -> Nat) :
    ∀ n : Nat, (∀ i : Nat, i <= n -> f i = g i) ->
      finiteNatSum f n = finiteNatSum g n
  | 0, h => by
      exact h 0 (Nat.le_refl 0)
  | Nat.succ n, h => by
      change finiteNatSum f n + f (Nat.succ n) =
        finiteNatSum g n + g (Nat.succ n)
      rw [finiteNatSum_congr_le f g n
        (fun i hi => h i (Nat.le_trans hi (Nat.le_succ n)))]
      rw [h (Nat.succ n) (Nat.le_refl (Nat.succ n))]

theorem catalanConvolutionSum_eq_finiteNatSum (n : Nat) :
    BEDC.Derived.CatalanConvolutionUp.catalanConvolutionSum n =
      catalanConvolutionFold n := by
  unfold BEDC.Derived.CatalanConvolutionUp.catalanConvolutionSum
  unfold BEDC.Derived.CatalanConvolutionUp.catalanPrefixConvolution
  unfold catalanConvolutionFold
  rw [listNatSum_natRange_map_finiteNatSum]
  exact finiteNatSum_congr_le
    (fun i =>
      BEDC.Derived.CatalanConvolutionUp.listNthD
          (BEDC.Derived.CatalanConvolutionUp.catalanPrefix n) i *
        BEDC.Derived.CatalanConvolutionUp.listNthD
          (BEDC.Derived.CatalanConvolutionUp.catalanPrefix n) (n - i))
    (fun i => cat i * cat (n - i))
    n
    (fun i hi => product_from_prefix_eq_cat_product hi)

theorem catalan_succ_convolution_identity (n : Nat) :
    cat (Nat.succ n) = catalanConvolutionFold n := by
  unfold cat
  rw [BEDC.Derived.CatalanConvolutionUp.catalan_succ_segner n]
  exact catalanConvolutionSum_eq_finiteNatSum n

theorem catalan_succ_convolution_identity_strong (n : Nat) :
    cat (Nat.succ n) = catalanConvolutionFold n := by
  exact Nat.strongRecOn n
    (motive := fun k => cat (Nat.succ k) = catalanConvolutionFold k)
    (fun k _ih => catalan_succ_convolution_identity k)

theorem catalan_binomial_difference_identity (n : Nat) :
    BEDC.Derived.CatalanConvolutionUp.catalanBinomialDifference n =
      C (n + n) n - C (n + n) (Nat.succ n) := by
  exact BEDC.Derived.CatalanConvolutionUp.catalan_binomial_difference_surface n

theorem catalan_binomial_difference_lobb_identity (n : Nat) :
    BEDC.Derived.CatalanConvolutionUp.catalanBinomialDifference n =
      BEDC.Derived.LobbUp.catalanNat n := by
  exact BEDC.Derived.CatalanConvolutionUp.catalan_difference_matches_lobb n

theorem catalan_binomial_difference_agrees_small_values :
    cat 0 = BEDC.Derived.CatalanConvolutionUp.catalanBinomialDifference 0 ∧
      cat 1 = BEDC.Derived.CatalanConvolutionUp.catalanBinomialDifference 1 ∧
        cat 2 = BEDC.Derived.CatalanConvolutionUp.catalanBinomialDifference 2 ∧
          cat 3 = BEDC.Derived.CatalanConvolutionUp.catalanBinomialDifference 3 ∧
            cat 4 = BEDC.Derived.CatalanConvolutionUp.catalanBinomialDifference 4 := by
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · constructor
        · rfl
        · rfl

theorem segner_recursion_identity (n : Nat) :
    cat (Nat.succ n) = catalanConvolutionFold n := by
  exact catalan_succ_convolution_identity_strong n

theorem CatalanIdentitiesUp_constructive_export :
    (∀ n : Nat, cat (Nat.succ n) = catalanConvolutionFold n) ∧
      (∀ n : Nat,
        BEDC.Derived.CatalanConvolutionUp.catalanBinomialDifference n =
          C (n + n) n - C (n + n) (Nat.succ n)) ∧
      (∀ n : Nat,
        BEDC.Derived.CatalanConvolutionUp.catalanBinomialDifference n =
          BEDC.Derived.LobbUp.catalanNat n) := by
  constructor
  · intro n
    exact catalan_succ_convolution_identity_strong n
  · constructor
    · intro n
      exact catalan_binomial_difference_identity n
    · intro n
      exact catalan_binomial_difference_lobb_identity n

end BEDC.Derived.CatalanIdentitiesUp
