import UnifiedTheory.Zeta.RHBridge
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# ch23/26 ζ 无零线与投影零点的临界带约束

对接 mathlib 的深解析事实:`ζ` 在闭半平面 `Re s ≥ 1` 上不为零(含边界 `Re=1`,与素数定理
等价;Loeffler–Stoll)。这是拉回线定理(命题 6.32)与"素数定理清道夫"(第二十六章)的解析
输入。据此把零点账本的支撑收紧:非平凡 `ζ` 零点必落在 `Re s < 1`——RH 即"再收紧到中线
`Re=½`"的问题(与函数方程反射合观则零点困于临界带)。
-/

namespace UnifiedTheory

open Complex

/-- **ζ 无零线(〔closed·Lean〕)**:`Re s ≥ 1 ⟹ ζ(s) ≠ 0`(含边界,PNT-等价深解析事实)。 -/
theorem zeta_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re hs

/-- **投影零点在临界线左侧**:非平凡 `ζ` 零点必有 `Re s < 1`(无零线反证)。
把零点账本(`ProjectedZero`)的支撑收紧到临界带右界之内。 -/
theorem projectedZero_re_lt_one {s : ℂ} (h : ProjectedZero s) : s.re < 1 := by
  by_contra hge
  push_neg at hge
  exact zeta_ne_zero_of_one_le_re hge h.1

/-- 结合函数方程零点反射(`completed_zero_reflect`):临界带右界约束的镜像形态记在此,
作为 RH 中线问题的定界——非平凡零点困于 `Re s < 1`,RH 断言其进一步落在 `Re s = ½`。 -/
theorem projectedZero_re_ne_one {s : ℂ} (h : ProjectedZero s) : s.re ≠ 1 :=
  ne_of_lt (projectedZero_re_lt_one h)

end UnifiedTheory
