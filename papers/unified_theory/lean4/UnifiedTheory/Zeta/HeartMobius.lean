import Mathlib

namespace UnifiedTheory

open scoped BigOperators

/-- **窗化 Möbius 和**(源 §1,残余谱恒等式之算术左侧):`S_g(N,δ) = Σ_{k<N} μ(k+1)·g((k+1)δ)`。 -/
noncomputable def heartMobiusSum (g : ℝ → ℝ) (N : ℕ) (δ : ℝ) : ℝ :=
  ∑ k ∈ Finset.range N,
    ((ArithmeticFunction.moebius (k + 1) : ℤ) : ℝ) * g (((k + 1 : ℕ) : ℝ) * δ)

/-- 窗化 Möbius 和对 `g` 可加。 -/
theorem heartMobiusSum_add (g h : ℝ → ℝ) (N : ℕ) (δ : ℝ) :
    heartMobiusSum (fun t => g t + h t) N δ
      = heartMobiusSum g N δ + heartMobiusSum h N δ := by
  simp only [heartMobiusSum, mul_add, Finset.sum_add_distrib]

/-- 窗化 Möbius 和对 `g` 齐次(标量)。 -/
theorem heartMobiusSum_smul (c : ℝ) (g : ℝ → ℝ) (N : ℕ) (δ : ℝ) :
    heartMobiusSum (fun t => c * g t) N δ = c * heartMobiusSum g N δ := by
  simp only [heartMobiusSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

end UnifiedTheory
