import UnifiedTheory.Dynamics.TraceStepReversible

namespace UnifiedTheory

variable {R : Type*} [CommRing R]

/-- 偶符号翻转: `(a,b,c) ↦ (-a,-b,c)`。 -/
def flipAB (v : R × R × R) : R × R × R := (-v.1, -v.2.1, v.2.2)

/-- 偶符号翻转: `(a,b,c) ↦ (-a,b,-c)`。 -/
def flipAC (v : R × R × R) : R × R × R := (-v.1, v.2.1, -v.2.2)

/-- 偶符号翻转: `(a,b,c) ↦ (a,-b,-c)`。 -/
def flipBC (v : R × R × R) : R × R × R := (v.1, -v.2.1, -v.2.2)

/-- **迹映射循环置换三个偶符号翻转**: `T∘flipAB = flipAC∘T`, `T∘flipAC = flipBC∘T`,
`T∘flipBC = flipAB∘T` (逐项 ring 验证)。 -/
theorem traceMap_evenSign_cycle :
    (∀ x : R × R × R, TraceStep (flipAB x) = flipAC (TraceStep x)) ∧
    (∀ x : R × R × R, TraceStep (flipAC x) = flipBC (TraceStep x)) ∧
    (∀ x : R × R × R, TraceStep (flipBC x) = flipAB (TraceStep x)) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · rintro ⟨a, b, c⟩
    simp only [TraceStep, flipAB, flipAC, flipBC]
    ext <;> simp [sub_eq_add_neg, add_comm]

/-- `T^3` 与 flipAB 交换 (三次循环回到自身)。 -/
theorem traceMap_iterate_three_comm_flipAB :
    ∀ x : R × R × R, (TraceStep^[3]) (flipAB x) = flipAB ((TraceStep^[3]) x) := by
  intro x
  rcases traceMap_evenSign_cycle (R := R) with ⟨hAB, hAC, hBC⟩
  calc
    (TraceStep^[3]) (flipAB x)
        = TraceStep (TraceStep (TraceStep (flipAB x))) := by rfl
    _ = TraceStep (TraceStep (flipAC (TraceStep x))) := by rw [hAB x]
    _ = TraceStep (flipBC (TraceStep (TraceStep x))) := by rw [hAC (TraceStep x)]
    _ = flipAB (TraceStep (TraceStep (TraceStep x))) := by rw [hBC (TraceStep (TraceStep x))]
    _ = flipAB ((TraceStep^[3]) x) := by rfl

/-- `T^3` 与 flipAC 交换。 -/
theorem traceMap_iterate_three_comm_flipAC :
    ∀ x : R × R × R, (TraceStep^[3]) (flipAC x) = flipAC ((TraceStep^[3]) x) := by
  intro x
  rcases traceMap_evenSign_cycle (R := R) with ⟨hAB, hAC, hBC⟩
  calc
    (TraceStep^[3]) (flipAC x)
        = TraceStep (TraceStep (TraceStep (flipAC x))) := by rfl
    _ = TraceStep (TraceStep (flipBC (TraceStep x))) := by rw [hAC x]
    _ = TraceStep (flipAB (TraceStep (TraceStep x))) := by rw [hBC (TraceStep x)]
    _ = flipAC (TraceStep (TraceStep (TraceStep x))) := by rw [hAB (TraceStep (TraceStep x))]
    _ = flipAC ((TraceStep^[3]) x) := by rfl

/-- `T^3` 与 flipBC 交换。 -/
theorem traceMap_iterate_three_comm_flipBC :
    ∀ x : R × R × R, (TraceStep^[3]) (flipBC x) = flipBC ((TraceStep^[3]) x) := by
  intro x
  rcases traceMap_evenSign_cycle (R := R) with ⟨hAB, hAC, hBC⟩
  calc
    (TraceStep^[3]) (flipBC x)
        = TraceStep (TraceStep (TraceStep (flipBC x))) := by rfl
    _ = TraceStep (TraceStep (flipAB (TraceStep x))) := by rw [hBC x]
    _ = TraceStep (flipAC (TraceStep (TraceStep x))) := by rw [hAB (TraceStep x)]
    _ = flipBC (TraceStep (TraceStep (TraceStep x))) := by rw [hAC (TraceStep (TraceStep x))]
    _ = flipBC ((TraceStep^[3]) x) := by rfl

end UnifiedTheory
