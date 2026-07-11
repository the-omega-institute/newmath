import UnifiedTheory.Golden.ShiftedZeckendorf
import UnifiedTheory.Golden.MinusWindowSigned

/-!
# ch6.44 位移 Zeckendorf–Beatty 桥(无条件)

`MinusWindow` 已无条件成立(`minusWindow_holds`),故位移 Zeckendorf 桥
`shiftedZeckendorf_of_minusWindow` 的假设被卸除:Beatty 位移读数 `S v` 恰等于
`v` 的 Zeckendorf 词位移和 `Σ_{i∈encode v} fib(i+1)`,不再依赖任何 front-line 假设。
全项目至此零条件桥。
-/

namespace UnifiedTheory

/-- **位移 Zeckendorf–Beatty 桥(无条件)**:`S v = Σ_{i∈encode v} fib(i+1)`。 -/
theorem S_eq_shifted_zeck (v : ℕ) :
    S v = ((AxisWord.encode v).1.map fun i => (Nat.fib (i + 1) : ℤ)).sum :=
  shiftedZeckendorf_of_minusWindow minusWindow_holds v

end UnifiedTheory
