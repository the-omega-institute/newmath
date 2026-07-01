import BEDC.Foundations.TriRealization
import BEDC.Foundations.TriAxisCoverage

/-!
`TriAxisRealized` 把三角绑定从"贴 code 标签"升级为"对象被三角构造器真实现 +
覆盖需求轴"。这是 round 3 的强制接口: 单纯的 `TriAxisProjected` 只要求一个 code +
covers 证明, code 可与对象无关地乱贴; `TriAxisRealized` 额外要求一个 `witness` 元素
和一条 `realizes` 证明, 把 witness 钉死在 code 的代数解释上 (`witness = algebra.interp
code`), 从而 code 不能是与对象脱节的自由标签。任何 `TriAxisRealized` 实例自动给出一个
`TriAxisProjected` 实例, 所以它是严格加强。
-/

namespace BEDC.Foundations.TriAxisRealized

open BEDC.Foundations.TriangleGenerationSystem
open BEDC.Foundations.TriRealization
open BEDC.Foundations.TriAxisCoverage

/-- 三角实现型: 提供三角代数、见证元素、code、见证被 code 真实现的证明, 以及 code
    覆盖需求轴的证明。realizes 把 witness 钉在 code 的解释上, 堵住裸 code 造假。 -/
class TriAxisRealized (α : Type u) where
  algebra : TriAlgebra α
  witness : α
  code : TriAxisObjCode
  realizes : TriRealizes algebra code witness
  demanded_axes : AxisDemand
  covers : AxisDemand.Covers demanded_axes code

/-- 实现型的三轴 profile (经 code 的强制唯一投影)。 -/
def TriAxisRealized.profile (α : Type u) [TriAxisRealized α] : TriAxisProfile :=
  triAxisProjection (TriAxisRealized.code (α := α))

/-- 加强: 任何 TriAxisRealized 型自动是 TriAxisProjected 型 (同 code + 同 covers)。 -/
instance triAxisRealized_toProjected (α : Type u) [TriAxisRealized α] :
    TriAxisProjected α where
  code := TriAxisRealized.code (α := α)
  projection_forced := triAxisProjection_forced_unique _
  demanded_axes := TriAxisRealized.demanded_axes (α := α)
  covers_some := TriAxisRealized.covers (α := α)

/-- 反 vacuity 内容显式化: 实现型的 witness 恰是其代数对 code 的解释。 -/
theorem TriAxisRealized.witness_eq_interp (α : Type u) [TriAxisRealized α] :
    TriAxisRealized.witness (α := α)
      = (TriAxisRealized.algebra (α := α)).interp (TriAxisRealized.code (α := α)) :=
  TriAxisRealized.realizes (α := α)

/-- Nat 是三角实现型: 纯 time 代数, 见证 1 = succ 0 被 timeGen base 真实现, 覆盖 time 轴。 -/
instance : TriAxisRealized Nat where
  algebra := natAlgebra
  witness := 1
  code := TriAxisObjCode.timeGen TriAxisObjCode.base
  realizes := rfl
  demanded_axes := AxisDemand.timeOnly
  covers := CoversTime.here TriAxisObjCode.base

end BEDC.Foundations.TriAxisRealized
