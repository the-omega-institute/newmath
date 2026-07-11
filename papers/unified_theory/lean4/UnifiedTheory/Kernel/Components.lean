import UnifiedTheory.Foundation.Mark
import UnifiedTheory.Foundation.History
import UnifiedTheory.Foundation.Rewriting
import UnifiedTheory.Arithmetic.PrimeAxes
import UnifiedTheory.PZG.Decode
import UnifiedTheory.PZG.Normalize
import UnifiedTheory.Golden.Lambda
import UnifiedTheory.Kernel.LedgerStatus

/-!
# 第〇章 内核总对象 𝒦 的分量别名(thin aggregate)

ch0 定义 `𝒦 = (𝖧, 𝖦, σ, 𝒜, 𝒯, 𝖹, 𝖣, 𝖭, …, 𝖫, …)`。这里**不建巨型闭合 record**,只给
每个已形式化 slot 一个稳定别名,并在注释里指向承载它的定理,供上层(Part III–IX)按稳定名引用。
各分量的"载荷"由本仓库对应定理建立:𝖹≃ℕ+(定理 5.5)、𝖭=乘法(定理 5.6)、单位性(定理 3.2)、
自由性(定理 4.4)、亏空整性(定理 6.22)。
-/

namespace UnifiedTheory.Kernel

/-- 生成历史 𝖧(标记层):`inductive MarkHist`,append 幺半群(命题 2.4)。 -/
abbrev History := MarkHist

/-- 最小二分交换 σ 的载体:`Mark`(定义 1.1/1.2,`sigma_involutive`)。 -/
abbrev Marks := Mark

/-- 素数指数状态空间 𝒜(自由交换幺半群,定理 4.4):`PrimeExp`。 -/
abbrev ExponentState := PrimeExp

/-- PZG 编码寄存器 𝖹:`PZGTable`(定理 5.5:`decode : PZGTable ≃ ℕ+`)。 -/
abbrev CodeRegister := PZGTable

/-- 四状态账本 𝖫 的状态词:`LedgerStatus`。 -/
abbrev Ledger := LedgerStatus

/-- 解码器 𝖣:PZG 位表到正自然数的双射(定理 5.5)。 -/
noncomputable abbrev decode : CodeRegister ≃ ℕ+ := PZGTable.decode

/-- 归一化器 𝖭:位表 PZG 加法后归一化 = 乘法(定理 5.6)。 -/
noncomputable abbrev normalize : CodeRegister → CodeRegister → CodeRegister := PZGTable.normAdd

/-- 双面长度读数 λ₊/λ₋(定义 6.4)。 -/
noncomputable abbrev lengthPlus : CodeRegister → ℝ := PZGTable.lambdaPlus
noncomputable abbrev lengthMinus : CodeRegister → ℝ := PZGTable.lambdaMinus

end UnifiedTheory.Kernel
