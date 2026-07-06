import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Nat.Squarefree

namespace UnifiedTheory

variable (p : ℕ → ℕ)

/-- Squarefree Gödel code over a chosen prime axis. -/
def AxisCode (A : Finset ℕ) : ℕ := ∏ i ∈ A, p i

/-- Zeckendorf-admissible finite index sets. -/
def ZeckSet (A : Finset ℕ) : Prop := (∀ i ∈ A, 2 ≤ i) ∧ (∀ i ∈ A, i + 1 ∉ A)

variable (hp : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p)

include hp hinj

/-- The prime factors of an axis code are exactly the selected prime-axis entries. -/
theorem primeFactors_axisCode (A : Finset ℕ) :
    (AxisCode p A).primeFactors = A.image p := by
  unfold AxisCode
  rw [← Finset.prod_image (s := A) (g := p) (f := fun q : ℕ => q)]
  · exact Nat.primeFactors_prod (s := A.image p) (by
      intro q hq
      rcases Finset.mem_image.mp hq with ⟨i, _hi, rfl⟩
      exact hp i)
  · intro x _hx y _hy hxy
    exact hinj hxy

/-- Axis coding is injective on finite index sets. -/
theorem axisCode_injective : Function.Injective (AxisCode p) := by
  intro A B h
  have hFactors := congrArg Nat.primeFactors h
  rw [primeFactors_axisCode p hp hinj, primeFactors_axisCode p hp hinj] at hFactors
  exact Finset.image_injective hinj hFactors

/-- Axis codes are squarefree products of distinct primes. -/
theorem axisCode_squarefree (A : Finset ℕ) : Squarefree (AxisCode p A) := by
  unfold AxisCode
  refine Finset.squarefree_prod_of_pairwise_isCoprime (s := A) (f := p) ?_ ?_
  · intro i _hi j _hj hij
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (hp i) (hp j)).2 (fun hpij => hij (hinj hpij)))
  · intro i _hi
    exact Irreducible.squarefree (hp i)

/-- Divisibility by an axis prime reads membership in the encoded finite set. -/
theorem axisPrime_dvd_axisCode_iff_mem (A : Finset ℕ) (i : ℕ) :
    p i ∣ AxisCode p A ↔ i ∈ A := by
  have hne : AxisCode p A ≠ 0 := by
    unfold AxisCode
    exact Finset.prod_ne_zero_iff.2 (by
      intro j _hj
      exact (hp j).ne_zero)
  have hmem_dvd : p i ∈ (AxisCode p A).primeFactors ↔ p i ∣ AxisCode p A := by
    rw [Nat.mem_primeFactors_of_ne_zero hne]
    exact and_iff_right (hp i)
  rw [← hmem_dvd, primeFactors_axisCode p hp hinj]
  constructor
  · intro hmem
    rcases Finset.mem_image.mp hmem with ⟨j, hj, hji⟩
    exact (hinj hji.symm) ▸ hj
  · intro hi
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩

omit hp hinj in
theorem axisCode_zeck_iff (A : Finset ℕ) :
    ZeckSet A ↔ (∀ i ∈ A, 2 ≤ i) ∧ (∀ i ∈ A, i + 1 ∉ A) := by
  rfl

/-- Zeckendorf admissibility expressed through divisibility of the squarefree axis code. -/
theorem axisCode_zeck_dvd_iff (A : Finset ℕ) :
    ZeckSet A ↔ Squarefree (AxisCode p A) ∧
      (∀ i, p i ∣ AxisCode p A → 2 ≤ i) ∧
      (∀ i, p i ∣ AxisCode p A → ¬ p (i + 1) ∣ AxisCode p A) := by
  constructor
  · intro hZ
    refine ⟨axisCode_squarefree p hp hinj A, ?_, ?_⟩
    · intro i hdiv
      exact hZ.1 i ((axisPrime_dvd_axisCode_iff_mem p hp hinj A i).1 hdiv)
    · intro i hdiv hnext
      exact hZ.2 i
        ((axisPrime_dvd_axisCode_iff_mem p hp hinj A i).1 hdiv)
        ((axisPrime_dvd_axisCode_iff_mem p hp hinj A (i + 1)).1 hnext)
  · intro h
    exact ⟨
      fun i hi => h.2.1 i ((axisPrime_dvd_axisCode_iff_mem p hp hinj A i).2 hi),
      fun i hi hnext => h.2.2 i
        ((axisPrime_dvd_axisCode_iff_mem p hp hinj A i).2 hi)
        ((axisPrime_dvd_axisCode_iff_mem p hp hinj A (i + 1)).2 hnext)⟩

end UnifiedTheory
