import Mathlib.Data.Nat.Fib.Zeckendorf
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Bounded Zeckendorf words

The initial interval `[0, fib (n + 2))` is exactly the set of naturals whose
Zeckendorf support is bounded by the index cutoff `n + 2`.
-/

namespace UnifiedTheory

/-- Natural-list membership gives a lower bound on the list sum. -/
private theorem nat_le_sum_of_mem {a : ℕ} {l : List ℕ} (ha : a ∈ l) : a ≤ l.sum := by
  induction l with
  | nil =>
      cases ha
  | cons b t ih =>
      rw [List.sum_cons]
      rcases List.mem_cons.mp ha with rfl | ha
      · exact Nat.le_add_right _ _
      · exact (ih ha).trans (Nat.le_add_left _ _)

/-- A present Fibonacci summand is bounded by the full Fibonacci sum. -/
private theorem fib_le_sum_of_mem {k : ℕ} {l : List ℕ} (hk : k ∈ l) :
    Nat.fib k ≤ (l.map Nat.fib).sum := by
  exact nat_le_sum_of_mem (List.mem_map.2 ⟨k, hk, rfl⟩)

/-- Zeckendorf words whose indices are bounded by `n + 2`. -/
def ZeckPrefix (n : ℕ) : Type :=
  {l : List ℕ // l.IsZeckendorfRep ∧ ∀ k ∈ l, k < n + 2}

/-- **Key lemma**: a legal Zeckendorf word has fib sum below `fib (n + 2)` iff
all its indices are below `n + 2`. -/
theorem zeck_sum_lt_fib_iff_bounded {n : ℕ} {l : List ℕ} (hl : l.IsZeckendorfRep) :
    (l.map Nat.fib).sum < Nat.fib (n + 2) ↔ ∀ k ∈ l, k < n + 2 := by
  constructor
  · intro hsum k hk
    by_contra hnot
    have hnk : n + 2 ≤ k := not_lt.mp hnot
    have hfib : Nat.fib (n + 2) ≤ Nat.fib k := Nat.fib_mono hnk
    have hterm : Nat.fib k ≤ (l.map Nat.fib).sum := fib_le_sum_of_mem hk
    exact (not_lt_of_ge (hfib.trans hterm)) hsum
  · intro hb
    apply List.IsZeckendorfRep.sum_fib_lt hl
    intro a ha
    cases l with
    | nil =>
        simp only [List.nil_append, List.head?_cons, Option.mem_def] at ha
        injection ha with ha
        subst a
        simp
    | cons b t =>
        simp only [List.cons_append, List.head?_cons, Option.mem_def] at ha
        injection ha with ha
        subst a
        exact hb b List.mem_cons_self

/-- Bounded Zeckendorf words are equivalent to `Fin (fib (n + 2))`. -/
noncomputable def zeckPrefixEquivFin (n : ℕ) : ZeckPrefix n ≃ Fin (Nat.fib (n + 2)) where
  toFun := fun l =>
    ⟨(l.1.map Nat.fib).sum, (zeck_sum_lt_fib_iff_bounded l.2.1).2 l.2.2⟩
  invFun := fun m =>
    ⟨(Nat.zeckendorfEquiv m.1).1,
      (Nat.zeckendorfEquiv m.1).2,
      (zeck_sum_lt_fib_iff_bounded (Nat.zeckendorfEquiv m.1).2).1
        (by
          have hsum : ((Nat.zeckendorfEquiv m.1).1.map Nat.fib).sum = m.1 :=
            Nat.zeckendorfEquiv.symm_apply_apply m.1
          simp [hsum, m.2])⟩
  left_inv := fun l => by
    apply Subtype.ext
    change Nat.zeckendorf ((l.1.map Nat.fib).sum) = l.1
    exact Nat.zeckendorf_sum_fib l.2.1
  right_inv := fun m => by
    apply Fin.ext
    change ((Nat.zeckendorfEquiv m.1).1.map Nat.fib).sum = m.1
    exact Nat.zeckendorfEquiv.symm_apply_apply m.1

/-- **Fibonacci cardinality of the bounded Zeckendorf language**: there are exactly
`fib (n + 2)` Zeckendorf words whose indices are below `n + 2`. Equivalently,
the initial interval `[0, fib (n + 2))` is exactly the set of natural numbers
whose Zeckendorf support is bounded by the index cutoff `n + 2`. -/
theorem card_zeckPrefix (n : ℕ) : Nat.card (ZeckPrefix n) = Nat.fib (n + 2) := by
  rw [Nat.card_congr (zeckPrefixEquivFin n), Nat.card_eq_fintype_card, Fintype.card_fin]

end UnifiedTheory
