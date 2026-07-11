import UnifiedTheory.Arithmetic.PrimeAxes
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/-!
# ch22.3 Euler 乘积:素数轴自由幺半群的解析化身

对接 mathlib:`Re s > 1` 时 `ζ(s) = ∏_p (1 − p^{-s})^{-1}`。这是内核素数轴结构(第四章
`PrimeExp`:`ℕ⁺ ≃` 素数指数向量,素数轴上的自由交换幺半群)在解析侧的化身:每条素数轴贡献一个
Euler 因子 `(1 − p^{-s})^{-1} = ∑_{e≥0} p^{-e s}`(该轴指数的几何和),全体轴的乘积即 `ζ`。
热迹有 Euler 因子 ⟺ 幺半群自由于原子(定理 22.2)在 `ℕ⁺` 上的实现即此。
-/

namespace UnifiedTheory

open Complex

/-- **定理 22.3(Euler 乘积,〔closed·Lean〕)**:`Re s > 1` 时
`∏'_p (1 − p^{-s})^{-1} = ζ(s)`。素数轴自由幺半群(`PrimeExp`,定理 4.4)的解析化身。 -/
theorem zeta_eulerProduct {s : ℂ} (hs : 1 < s.re) :
    ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹ = riemannZeta s :=
  riemannZeta_eulerProduct_tprod hs

end UnifiedTheory
