import UnifiedTheory.Golden.Lambda

/-!
# ch6 归一化亏空:整性(定理 6.22)与三值(定理 6.25,statement-only)

归一化亏空 `deficitPhi v w := β(v)+β(w)−β(v+w)`(β 取 Zeckendorf 双面 φ 读数)。
**定理 6.22(整性)本文件完整证明**:双面差 `betaPhi_gap` 给出亏空 φ 分量 = √5(v+w−(v+w))/√5 = 0,
故亏空共轭不动、即整数。

**定理 6.25(三值 `∈{−1,0,1}`)登记为 statement-only**:其证明还差收缩面窗口界
`−1/φ² < betaMinusReal(encode n) < 1/φ`(合法 Zeckendorf 词上的几何/奇偶界),与整性相交即得。
该窗口界属前沿,此处**不 fake、不用有限 scan 冒充全称**(遵循忠实优先)。
-/

namespace UnifiedTheory

namespace PhiInt
@[simp] theorem sub_a (x y : PhiInt) : (x - y).a = x.a - y.a := rfl
@[simp] theorem sub_b (x y : PhiInt) : (x - y).b = x.b - y.b := rfl
end PhiInt

/-- 归一化亏空(PhiInt 值):`β(v)+β(w)−β(v+w)`。 -/
noncomputable def deficitPhi (v w : ℕ) : PhiInt :=
  AxisWord.betaPhi (AxisWord.encode v) + AxisWord.betaPhi (AxisWord.encode w)
    - AxisWord.betaPhi (AxisWord.encode (v + w))

/-- 定理 6.22 核心:亏空的 φ 分量为零(两面之差 √5·(v+w−(v+w)) = 0)。 -/
@[simp] theorem deficitPhi_b (v w : ℕ) : (deficitPhi v w).b = 0 := by
  simp only [deficitPhi, PhiInt.add_b, PhiInt.sub_b, AxisWord.betaPhi_b,
    AxisWord.decode_encode]
  push_cast; ring

/-- **定理 6.22**:归一化亏空是整数(φ 分量为零 ⟹ 共轭不动 ⟹ 整数)。 -/
theorem deficitPhi_integer (v w : ℕ) : ∃ k : ℤ, deficitPhi v w = PhiInt.ofInt k := by
  refine ⟨(deficitPhi v w).a, ?_⟩
  rw [PhiInt.ext_iff, PhiInt.ofInt_a, PhiInt.ofInt_b]
  exact ⟨rfl, deficitPhi_b v w⟩

/-- 亏空共轭不动(整性的等价形式,定理 6.22)。 -/
theorem deficitPhi_conj_fixed (v w : ℕ) : (deficitPhi v w).conj = deficitPhi v w :=
  (PhiInt.fixed_conj_iff _).2 (deficitPhi_b v w)

/-- 亏空的整数值(由定理 6.22 良定义)。 -/
noncomputable def deficitInt (v w : ℕ) : ℤ := (deficitPhi v w).a

/-- **定理 6.25(亏空三值)** —— statement-only。待证余项为收缩面窗口界
    `−1/φ² < betaMinusReal(encode n) < 1/φ`;与整性(定理 6.22,已证)相交即得
    `deficitInt ∈ {−1,0,1}`。窗口界属前沿,此处不证、不 fake。 -/
def DeficitTrichotomy : Prop :=
  ∀ v w : ℕ, deficitInt v w = -1 ∨ deficitInt v w = 0 ∨ deficitInt v w = 1

end UnifiedTheory
