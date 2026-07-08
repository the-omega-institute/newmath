import Mathlib

namespace UnifiedTheory

open Finset

/-- **阶乘配对(源 9.5 之工具)**:奇素数 `p`、`m = (p-1)/2` 时
`(p-1)! ≡ (-1)^m (m!)²` 于 `ZMod p`。将 `{1,…,p-1}` 上半区 `k ↦ p-k` 反射到下半区,
`(p-k) = -k` 抽出 `(-1)^m`。 -/
theorem factorial_pairing (p : ℕ) [Fact p.Prime] (hodd : Odd p) :
    ((p - 1).factorial : ZMod p)
      = (-1) ^ ((p - 1) / 2) * (((p - 1) / 2).factorial : ZMod p) ^ 2 := by
  set m := (p - 1) / 2 with hm
  have hp1 : 1 ≤ p := (Fact.out (p := p.Prime)).one_lt.le
  have hpm : p = 2 * m + 1 := by
    obtain ⟨k, hk⟩ := hodd; omega
  have hfac : ((p - 1).factorial : ZMod p) = ∏ k ∈ Ico 1 p, (k : ZMod p) := by
    have hpe : ((p - 1) + 1) = p := by omega
    rw [← Finset.prod_Ico_id_eq_factorial, hpe]
    push_cast
    rfl
  have hsplit : ∏ k ∈ Ico 1 p, (k : ZMod p)
      = (∏ k ∈ Ico 1 (m + 1), (k : ZMod p)) * ∏ k ∈ Ico (m + 1) p, (k : ZMod p) := by
    rw [← Finset.prod_Ico_consecutive _ (by omega : 1 ≤ m + 1) (by omega : m + 1 ≤ p)]
  have hlow : ∏ k ∈ Ico 1 (m + 1), (k : ZMod p) = (m.factorial : ZMod p) := by
    rw [← Finset.prod_Ico_id_eq_factorial]; push_cast; rfl
  have hup : ∏ k ∈ Ico (m + 1) p, (k : ZMod p)
      = (-1) ^ m * (m.factorial : ZMod p) := by
    have hbij : ∏ k ∈ Ico (m + 1) p, (k : ZMod p)
        = ∏ j ∈ Ico 1 (m + 1), ((p - j : ℕ) : ZMod p) := by
      apply Finset.prod_bij' (fun k _ => p - k) (fun j _ => p - j)
      · intro k hk; simp only [Finset.mem_Ico] at *; omega
      · intro j hj; simp only [Finset.mem_Ico] at *; omega
      · intro k hk; simp only [Finset.mem_Ico] at hk; omega
      · intro j hj; simp only [Finset.mem_Ico] at hj; omega
      · intro k hk; simp only [Finset.mem_Ico] at hk
        congr 1; omega
    rw [hbij]
    have hcast : ∀ j ∈ Ico 1 (m + 1), ((p - j : ℕ) : ZMod p) = -(j : ZMod p) := by
      intro j hj; simp only [Finset.mem_Ico] at hj
      have hjp : j ≤ p := by omega
      rw [Nat.cast_sub hjp, ZMod.natCast_self, zero_sub]
    rw [Finset.prod_congr rfl hcast]
    rw [Finset.prod_neg]
    rw [hlow]
    congr 1
    · congr 1; rw [Nat.card_Ico]; omega
  rw [hfac, hsplit, hlow, hup]
  ring

/-- **构造性 √(-1) 证书(源 9.5)**:`p ≡ 1 (mod 4)` 时 `((p-1)/2)!` 于 `ZMod p` 平方为 `-1`
——即 `m!` 是 `-1` 的显式平方根证书(强于存在性;经阶乘配对 + Wilson,`m` 偶)。 -/
theorem neg_one_sq_witness (p : ℕ) [Fact p.Prime] (hp : p % 4 = 1) :
    (((p - 1) / 2).factorial : ZMod p) ^ 2 = -1 := by
  have hodd : Odd p := by
    rw [Nat.odd_iff]; omega
  have hpair := factorial_pairing p hodd
  have hwil : ((p - 1).factorial : ZMod p) = -1 := ZMod.wilsons_lemma p
  have hmeven : Even ((p - 1) / 2) := by
    rw [Nat.even_iff]; omega
  rw [hwil] at hpair
  rw [hmeven.neg_one_pow, one_mul] at hpair
  exact hpair.symm

end UnifiedTheory
