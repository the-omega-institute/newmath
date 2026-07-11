import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Prime logarithm independence

Finite integer relations among logarithms of distinct primes are trivial.  The proof
turns the relation into equality of two natural prime-power products and reads off
prime exponents by unique factorization.
-/

open scoped BigOperators

namespace UnifiedTheory

private theorem factorization_primePow_prod_apply {s : Finset ℕ}
    (hs : ∀ q ∈ s, Nat.Prime q) {p : ℕ} (hp : p ∈ s) (e : ℕ → ℕ) :
    (∏ q ∈ s, q ^ e q).factorization p = e p := by
  rw [Nat.factorization_prod_apply]
  · rw [Finset.sum_eq_single_of_mem p hp]
    · exact Nat.factorization_pow_self (hs p hp)
    · intro q hq hqp
      have hfac := Nat.Prime.factorization_pow (hs q hq) (k := e q)
      have happ := congrArg (fun f : ℕ →₀ ℕ => f p) hfac
      simpa [Finsupp.single_eq_of_ne (Ne.symm hqp)] using happ
  · intro q hq
    exact pow_ne_zero _ (hs q hq).ne_zero

private theorem log_primePow_prod {s : Finset ℕ} (hs : ∀ p ∈ s, Nat.Prime p)
    (e : ℕ → ℕ) :
    Real.log ((∏ p ∈ s, p ^ e p : ℕ) : ℝ) =
      ∑ p ∈ s, (e p : ℝ) * Real.log (p : ℝ) := by
  calc
    Real.log ((∏ p ∈ s, p ^ e p : ℕ) : ℝ)
        = Real.log (∏ p ∈ s, (p : ℝ) ^ e p) := by simp
    _ = ∑ p ∈ s, Real.log ((p : ℝ) ^ e p) := by
        rw [Real.log_prod]
        intro p hp
        exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (hs p hp).ne_zero)
    _ = ∑ p ∈ s, (e p : ℝ) * Real.log (p : ℝ) := by
        refine Finset.sum_congr rfl ?_
        intro p _hp
        rw [Real.log_pow]

private theorem primePow_prod_pos {s : Finset ℕ} (hs : ∀ p ∈ s, Nat.Prime p)
    (e : ℕ → ℕ) :
    0 < ((∏ p ∈ s, p ^ e p : ℕ) : ℝ) := by
  rw [Nat.cast_prod]
  exact Finset.prod_pos fun p hp => by
    rw [Nat.cast_pow]
    exact pow_pos (Nat.cast_pos.mpr (hs p hp).pos) _

private theorem primePow_prod_eq_of_log_eq {s : Finset ℕ}
    (hs : ∀ p ∈ s, Nat.Prime p) {e f : ℕ → ℕ}
    (hlog : Real.log ((∏ p ∈ s, p ^ e p : ℕ) : ℝ) =
      Real.log ((∏ p ∈ s, p ^ f p : ℕ) : ℝ)) :
    (∏ p ∈ s, p ^ e p : ℕ) = (∏ p ∈ s, p ^ f p : ℕ) := by
  apply Nat.cast_injective (R := ℝ)
  exact Real.log_injOn_pos (Set.mem_Ioi.mpr (primePow_prod_pos hs e))
    (Set.mem_Ioi.mpr (primePow_prod_pos hs f)) hlog

/-- 素数对数 ℚ-线性无关(整数关系 Σ k_p log p = 0 ⟹ k=0)——唯一分解的 Brillouin/log 化身(Thm 25.13 核);zeta 相位线稠密缠绕之算术根据。 -/
theorem prime_log_linearIndependent {s : Finset ℕ} (hs : ∀ p ∈ s, Nat.Prime p)
    (k : ℕ → ℤ) (h : ∑ p ∈ s, (k p : ℝ) * Real.log (p : ℝ) = 0) :
    ∀ p ∈ s, k p = 0 := by
  let epos : ℕ → ℕ := fun p => (k p).toNat
  let eneg : ℕ → ℕ := fun p => (-k p).toNat
  have hsplit :
      (∑ p ∈ s, (epos p : ℝ) * Real.log (p : ℝ)) -
        (∑ p ∈ s, (eneg p : ℝ) * Real.log (p : ℝ)) =
          ∑ p ∈ s, (k p : ℝ) * Real.log (p : ℝ) := by
    simp_rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro p _hp
    dsimp [epos, eneg]
    have hkreal :
        ((k p).toNat : ℝ) - (((-k p).toNat : ℕ) : ℝ) = (k p : ℝ) := by
      exact_mod_cast Int.toNat_sub_toNat_neg (k p)
    calc
      ((k p).toNat : ℝ) * Real.log (p : ℝ) -
          (((-k p).toNat : ℕ) : ℝ) * Real.log (p : ℝ)
          = (((k p).toNat : ℝ) - (((-k p).toNat : ℕ) : ℝ)) *
              Real.log (p : ℝ) := by ring
      _ = (k p : ℝ) * Real.log (p : ℝ) := by rw [hkreal]
  have hlogeq :
      Real.log ((∏ p ∈ s, p ^ epos p : ℕ) : ℝ) =
        Real.log ((∏ p ∈ s, p ^ eneg p : ℕ) : ℝ) := by
    rw [log_primePow_prod hs epos, log_primePow_prod hs eneg]
    have hsum :
        (∑ p ∈ s, (epos p : ℝ) * Real.log (p : ℝ)) -
          (∑ p ∈ s, (eneg p : ℝ) * Real.log (p : ℝ)) = 0 := by
      rw [hsplit, h]
    linarith
  have hprod :
      (∏ p ∈ s, p ^ epos p : ℕ) = (∏ p ∈ s, p ^ eneg p : ℕ) :=
    primePow_prod_eq_of_log_eq hs hlogeq
  intro p hp
  have hfac :
      (∏ q ∈ s, q ^ epos q).factorization p =
        (∏ q ∈ s, q ^ eneg q).factorization p := by
    simpa using congrArg (fun n : ℕ => n.factorization p) hprod
  rw [factorization_primePow_prod_apply hs hp epos,
    factorization_primePow_prod_apply hs hp eneg] at hfac
  have hnat : (k p).toNat = (-k p).toNat := hfac
  have hint : ((k p).toNat : ℤ) = (((-k p).toNat : ℕ) : ℤ) := by
    exact_mod_cast hnat
  have hdiff : (k p : ℤ) = 0 := by
    calc
      k p = ((k p).toNat : ℤ) - (((-k p).toNat : ℕ) : ℤ) :=
        (Int.toNat_sub_toNat_neg (k p)).symm
      _ = 0 := by rw [hint, sub_self]
  simpa using hdiff

end UnifiedTheory
