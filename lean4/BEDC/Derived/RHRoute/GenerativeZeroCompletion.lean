import BEDC.Derived.RHRoute.ZetaZeroLocated
import BEDC.Derived.RHRoute.ZeroGenerationInitiality
import BEDC.Derived.RHRoute.ConstructiveRHStatement
import BEDC.Derived.RHRoute.FunctionalEquationSymmetry

/-
生成侧 ζ-零点完备性桥 (generative completeness bridge).

已有事实 (0-axiom, 已证, 复用不重造):
  `ZeroGenerationInitiality.generatedFixedHalf_criticalLine` — 只要 readback
  `epsilon` 是 fixed-half-closed, 每个 *generated* 零点 `epsilon z` 落在
  critical line 上. 这是 "legal generation ⟹ on-line / ℓ=0" 的 forward
  (source-side) 方向: 由生成塔构造得到, 不消费 ζ, 也不 backward-from-answer.

本模块补上缺失的连接: 从 generation-side 的 on-line 结论 *反推* 到
`ConstructiveRH`. 结构上把 RH 的难度诚实隔离成两条 obligation, 二者都无法在
不接入 located-ζ / located-real 基础的情况下 discharge:

  (1) `GenerativeZeroCompletion.generatesAllZeros` — completeness / binding.
      每个 located nontrivial ζ 零点都被某 generated 元素 realize
      (`ComplexEq (epsilon z) (functionalSymmetryPointOfRatComplex s)`).
      这就是 "BEDC 能生成 ζ 的所有点" 的形式化, located-ζ evaluator 所在;
      非 vacuous, 也不等于结论 (它是 realize 对应, 非 on-line 断言).

  (2) `LocatedReadbackBridge` — located ↔ rational-readback 边界, 即
      `ConstructiveRHStatement` 顶部注释已声明的共享 located-real 工作.

被证部分 (0-axiom, propext-free, 纯 `RatEq` 等价关系):
  * `reEqHalf_congr` / `criticalLine_congr` — on-line 沿 `ComplexEq` 传递;
  * `symmetryReadbackRH_of_completion` — generativity ⟹ RH (symmetry-readback 形式);
  * `constructiveRH_of_completion` — 完整反推到 `ConstructiveRH`, conditional
    on (1)+(2).

anti-circularity: generation dynamics (fixed-half closure) 独立于 ζ 定义;
ζ 只在 completeness 一侧作为 realize 的对象出现. forward 的 dynamics recursor
即已有的 `ZeroGenerationInitiality.generatedFixedHalfRecursor`.
-/

namespace BEDC.Derived.RHRoute.GenerativeZeroCompletion

open BEDC.Derived.RationalUp
open BEDC.Derived.RHRoute.ZetaBoxEvaluator
open BEDC.Derived.RHRoute.ZetaZeroLocated
open BEDC.Derived.RHRoute.ConstructiveRHStatement
open BEDC.Derived.RHRoute.ZeroGenerationInitiality
open BEDC.Derived.RHRoute.FunctionalEquationSymmetry

/-- On-line (`ReEqHalf`) 沿 `ComplexEq` 传递: 若 `a`, `b` 复相等且 `a` on-line,
则 `b` on-line. 纯 `RatEq` 对称+传递, propext-free. -/
theorem reEqHalf_congr {a b : RationalComplex}
    (hab : ComplexEq a b) (ha : ReEqHalf a) : ReEqHalf b := by
  have h1 : RatEq b.reAboveHalf a.reAboveHalf := RatEq_symm hab.left
  have h2 : RatEq a.reAboveHalf b.reBelowHalf :=
    RatEq_trans a.reAboveHalf a.reBelowHalf b.reBelowHalf ha hab.right.left
  exact RatEq_trans b.reAboveHalf a.reAboveHalf b.reBelowHalf h1 h2

/-- Critical-line 谓词沿 `ComplexEq` 传递. -/
theorem criticalLine_congr {a b : RationalComplex}
    (hab : ComplexEq a b) (ha : CriticalLine a) : CriticalLine b :=
  reEqHalf_congr hab ha

/-- 生成侧 ζ-零点完备性数据. `epsilon` 是 generated 零点到 source 点的 readback,
`closed` 保证 readback fixed-half-closed (⟹ 每个 generated 点 on-line),
`generatesAllZeros` 是 completeness / binding obligation
("BEDC 生成所有 ζ 零点", located-ζ evaluator 所在). -/
structure GenerativeZeroCompletion (signature : RHFreeZeroSignature) where
  epsilon : GeneratedZero signature -> SourceZeroPoint
  closed : FixedHalfClosedZeroSignature epsilon
  generatesAllZeros :
    ∀ s : ZetaBoxEvaluator.RatComplex, NontrivialZetaZero s ->
      ∃ z : GeneratedZero signature,
        ComplexEq (epsilon z) (functionalSymmetryPointOfRatComplex s)

/-- Generativity ⟹ RH (symmetry-readback 形式), 完全被证. 每个 nontrivial
ζ 零点 `s` 被某 generated `z` realize (completeness), `z` 的 readback on-line
(`generatedFixedHalf_criticalLine`), 沿 `ComplexEq` 传到 `funSymPoint s`. -/
theorem symmetryReadbackRH_of_completion
    {signature : RHFreeZeroSignature}
    (C : GenerativeZeroCompletion signature) :
    ∀ s : ZetaBoxEvaluator.RatComplex,
      NontrivialZetaZero s -> OnCriticalLineSymmetryReadback s := by
  intro s hs
  obtain ⟨z, hz⟩ := C.generatesAllZeros s hs
  have hcl : CriticalLine (C.epsilon z) :=
    generatedFixedHalf_criticalLine C.closed z
  exact criticalLine_congr hz hcl

/-- located ↔ rational-readback 边界 (共享 located-real 工作). -/
def LocatedReadbackBridge : Prop :=
  ∀ s : ZetaBoxEvaluator.RatComplex,
    OnCriticalLineSymmetryReadback s -> OnCriticalLine s

/-- 完整反推: BEDC 生成所有 ζ 零点 (+ located readback 边界) ⟹ `ConstructiveRH`. -/
theorem constructiveRH_of_completion
    {signature : RHFreeZeroSignature}
    (C : GenerativeZeroCompletion signature)
    (bridge : LocatedReadbackBridge) :
    ConstructiveRH := by
  intro s hs
  exact bridge s (symmetryReadbackRH_of_completion C s hs)

end BEDC.Derived.RHRoute.GenerativeZeroCompletion
