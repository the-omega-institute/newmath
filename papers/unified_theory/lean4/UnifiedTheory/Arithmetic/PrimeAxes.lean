import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.PNat.Basic

/-!
# ch4 素数轴与唯一分解(定理 4.4)

文档在核内证明唯一分解,使素数轴成为定理。这里落到 mathlib 的 `Nat.factorizationEquiv`:
正自然数 `ℕ+` 与"素数支撑的指数向量" `PrimeExp` 之间的等价 —— 即
`(ℕ₊, ×)` 为素数轴上的自由交换幺半群(定理 4.4 自由性),且指数读数 `v_p` 对乘法加性。
-/

namespace UnifiedTheory

/-- 素数指数向量:有限支撑、支撑上全为素数的 `ℕ →₀ ℕ`。素数轴上的自由交换幺半群。 -/
abbrev PrimeExp := {f : ℕ →₀ ℕ // ∀ p ∈ f.support, Nat.Prime p}

namespace PrimeExp

/-- 定理 4.4(自由性):`ℕ+ ≃ PrimeExp`,唯一分解的等价形式。 -/
def equivPNat : ℕ+ ≃ PrimeExp := Nat.factorizationEquiv

end PrimeExp

/-- 指数读数 `v_p`:正自然数在素数 `p` 上的分解指数。 -/
def vp (p : ℕ) (n : ℕ+) : ℕ := (n : ℕ).factorization p

/-- 定理 4.4(加性):`v_p` 对乘法逐轴相加。 -/
theorem vp_mul (p : ℕ) (m n : ℕ+) : vp p (m * n) = vp p m + vp p n := by
  unfold vp
  rw [PNat.mul_coe, Nat.factorization_mul m.pos.ne' n.pos.ne', Finsupp.add_apply]

end UnifiedTheory
