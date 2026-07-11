import UnifiedTheory.Golden.GoldenWeightLSeries
import Mathlib

namespace UnifiedTheory

/-- **跨层金标签**:Weil 素数幂频率 `p^{k+1}` 携带金权 `S(k+1)`(两层在素数幂上相遇)。 -/
theorem primePower_frequency_goldLabel (p : Nat.Primes) (k : ℕ) :
    goldWeight ((Nat.Primes.prodNatEquiv (p, k) : {n : ℕ // IsPrimePow n}) : ℕ) = S (k + 1) := by
  rw [Nat.Primes.coe_prodNatEquiv_apply, goldWeight_prime_pow p.2]

/-- **频率无碰撞**:`(p,k) ↦ (k+1)·log p` 单射——不同素数幂数据给出不同 Weil 频率。 -/
theorem weilFreq_injective :
    Function.Injective
      (fun i : Nat.Primes × ℕ => ((i.2 : ℝ) + 1) * Real.log (i.1 : ℝ)) := by
  rintro ⟨p, k⟩ ⟨p', k'⟩ h
  simp only at h
  have e1 : ((k : ℝ) + 1) * Real.log (p : ℝ) = Real.log ((p : ℝ) ^ (k + 1)) := by
    rw [Real.log_pow]
    push_cast
    ring
  have e2 : ((k' : ℝ) + 1) * Real.log (p' : ℝ) = Real.log ((p' : ℝ) ^ (k' + 1)) := by
    rw [Real.log_pow]
    push_cast
    ring
  rw [e1, e2] at h
  have hp_pos : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast p.2.pos
  have hp'_pos : (0 : ℝ) < (p' : ℝ) := by
    exact_mod_cast p'.2.pos
  have hxpos : (0 : ℝ) < (p : ℝ) ^ (k + 1) := by
    positivity
  have hypos : (0 : ℝ) < (p' : ℝ) ^ (k' + 1) := by
    positivity
  have hpow : (p : ℝ) ^ (k + 1) = (p' : ℝ) ^ (k' + 1) :=
    Real.log_injOn_pos (Set.mem_Ioi.mpr hxpos) (Set.mem_Ioi.mpr hypos) h
  have hnat : (p : ℕ) ^ (k + 1) = (p' : ℕ) ^ (k' + 1) := by
    exact_mod_cast hpow
  have hpe : Nat.Primes.prodNatEquiv (p, k) = Nat.Primes.prodNatEquiv (p', k') := by
    apply Subtype.ext
    rw [Nat.Primes.coe_prodNatEquiv_apply, Nat.Primes.coe_prodNatEquiv_apply]
    exact_mod_cast hnat
  have := Nat.Primes.prodNatEquiv.injective hpe
  simpa using this

end UnifiedTheory
