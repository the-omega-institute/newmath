import UnifiedTheory.Arithmetic.PrimeAxes
import UnifiedTheory.Arithmetic.Zeckendorf
import Mathlib.Data.Finsupp.Basic

/-!
# ch5 PZG 位表 carrier(定理 5.5 的轴层)

PZG 位表:每根素数轴挂一个 Zeckendorf 词(`AxisWord`),有限支撑、支撑全为素数。
**carrier 保留逐轴 Zeckendorf 位表结构,绝不塌成 exponent vector**(否则是 name-coincidence,
抹掉 Zeckendorf 位表)。逐轴 Zeckendorf 解码给出 `PZGTable ≃ PrimeExp`,与素数分解合成即
`PZGTable ≃ ℕ+`(定理 5.5,见 `PZG/Decode.lean`)。
-/

namespace UnifiedTheory

namespace AxisWord

/-- 空 Zeckendorf 词作为零。 -/
instance : Zero AxisWord := ⟨⟨[], List.IsZeckendorfRep_nil⟩⟩

@[simp] theorem decode_zero : decode (0 : AxisWord) = 0 := rfl

@[simp] theorem symm_zero : equivNat.symm (0 : AxisWord) = 0 := rfl

end AxisWord

/-- PZG 位表:素数支撑的、逐轴 Zeckendorf 词的有限支撑映射。保留字面位表结构。 -/
abbrev PZGTable := {axis : ℕ →₀ AxisWord // ∀ p ∈ axis.support, Nat.Prime p}

namespace PZGTable

/-- 字面位表读数 `z_{p,k}`:测试 Fibonacci 指标 `k+1` 是否出现在素数轴 `p` 的 Zeckendorf 词里。 -/
def bit (z : PZGTable) (p k : ℕ) : Bool := decide ((k + 1) ∈ (z.1 p).1)

/-- 逐轴 Zeckendorf 解码,把 `ℕ→₀AxisWord` 等价到 `ℕ→₀ℕ`。 -/
noncomputable def axisEquiv : (ℕ →₀ AxisWord) ≃ (ℕ →₀ ℕ) :=
  Finsupp.mapRange.equiv AxisWord.equivNat.symm AxisWord.symm_zero

theorem axisEquiv_support (axis : ℕ →₀ AxisWord) :
    (axisEquiv axis).support = axis.support := by
  simpa [axisEquiv] using
    Finsupp.support_mapRange_of_injective AxisWord.symm_zero axis
      AxisWord.equivNat.symm.injective

/-- 定理 5.5 的轴层:`PZGTable ≃ PrimeExp`,保素数支撑。 -/
noncomputable def equivPrimeExp : PZGTable ≃ PrimeExp :=
  axisEquiv.subtypeEquiv (fun axis => by rw [axisEquiv_support])

end PZGTable

end UnifiedTheory
