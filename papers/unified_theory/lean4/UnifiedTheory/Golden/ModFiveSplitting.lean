import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic

/-!
# The mod-five residue core for the golden coordinate ring

This file proves the elementary quadratic-residue criterion behind the
discriminant-five behavior of the golden coordinate ring.
-/

namespace UnifiedTheory

private theorem isSquare_zmod_five_iff_mod (n : ℕ) :
    IsSquare (n : ZMod 5) ↔ n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 4 := by
  have hn : (n : ZMod 5) = (n % 5 : ℕ) := by
    rw [ZMod.natCast_eq_natCast_iff']
    simp
  rw [hn]
  have hcases : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
    have hlt : n % 5 < 5 := Nat.mod_lt n (by norm_num)
    omega
  rcases hcases with h0 | h1 | h2 | h3 | h4
  · simp [h0]
  · simp [h1]
  · simp [h2]
    decide
  · simp [h3]
    decide
  · simp [h4]
    exact ⟨2, by norm_num⟩

private theorem prime_mod_five_ne_zero {p : ℕ} (hp : p.Prime) (hp5 : p ≠ 5) :
    p % 5 ≠ 0 := by
  intro h0
  have hdiv : 5 ∣ p := by
    rw [← Nat.modEq_zero_iff_dvd]
    exact h0
  have h5p : 5 = p := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp hdiv
  exact hp5 h5p.symm

/-- For an odd prime `p ≠ 5`, the discriminant `5` is a square modulo `p`
exactly at the residue classes `±1 mod 5`. -/
theorem five_isSquare_iff {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    IsSquare (5 : ZMod p) ↔ p % 5 = 1 ∨ p % 5 = 4 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := 5) (q := p)
    (by norm_num) hp2).symm.trans ?_
  rw [isSquare_zmod_five_iff_mod p]
  constructor
  · intro h
    rcases h with h0 | h1 | h4
    · exact False.elim (prime_mod_five_ne_zero (Fact.out : p.Prime) hp5 h0)
    · exact Or.inl h1
    · exact Or.inr h4
  · intro h
    rcases h with h1 | h4
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h4)

end UnifiedTheory
