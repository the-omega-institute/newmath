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

/-- 收缩面对加法线性。 -/
theorem toRealMinus_add (x y : PhiInt) :
    toRealMinus (x + y) = toRealMinus x + toRealMinus y := by
  simp only [toRealMinus, add_a, add_b]; push_cast; ring

/-- 收缩面对减法线性。 -/
theorem toRealMinus_sub (x y : PhiInt) :
    toRealMinus (x - y) = toRealMinus x - toRealMinus y := by
  simp only [toRealMinus, sub_a, sub_b]; push_cast; ring
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

/-- **定理 6.25(亏空三值)** 目标命题:`deficitInt ∈ {−1,0,1}`。 -/
def DeficitTrichotomy : Prop :=
  ∀ v w : ℕ, deficitInt v w = -1 ∨ deficitInt v w = 0 ∨ deficitInt v w = 1

/-- 亏空的实值 = 三处收缩面读数的账:`k = μ(v)+μ(w)−μ(v+w)`,其中
`μ(n)=betaMinusReal(encode n)`。由 `toRealMinus` 线性 + 亏空 φ 分量为零(定理 6.22)得出。 -/
theorem deficit_real_eq (v w : ℕ) :
    (deficitInt v w : ℝ) =
      AxisWord.betaMinusReal (AxisWord.encode v)
        + AxisWord.betaMinusReal (AxisWord.encode w)
        - AxisWord.betaMinusReal (AxisWord.encode (v + w)) := by
  have h1 : PhiInt.toRealMinus (deficitPhi v w) = (deficitInt v w : ℝ) := by
    unfold PhiInt.toRealMinus deficitInt
    rw [deficitPhi_b]; push_cast; ring
  have h2 : PhiInt.toRealMinus (deficitPhi v w) =
      AxisWord.betaMinusReal (AxisWord.encode v)
        + AxisWord.betaMinusReal (AxisWord.encode w)
        - AxisWord.betaMinusReal (AxisWord.encode (v + w)) := by
    unfold deficitPhi AxisWord.betaMinusReal
    rw [PhiInt.toRealMinus_sub, PhiInt.toRealMinus_add]
  rw [← h1, h2]

/-- **收缩面窗口界**(定理 6.7 的形式化目标 / 6.25 三值证明的唯一 front-line 余项):
对所有 `n`,`β₋(encode n) ∈ (−1/φ², 1/φ)`。合法 Zeckendorf 词(非相邻指标)上收缩面读数
受交错几何级数控制。 -/
def MinusWindow : Prop :=
  ∀ n : ℕ, -(1 / Real.goldenRatio ^ 2) < AxisWord.betaMinusReal (AxisWord.encode n)
    ∧ AxisWord.betaMinusReal (AxisWord.encode n) < 1 / Real.goldenRatio

/-- **定理 6.25(三值),conditional 形式**:收缩面窗口界 ⟹ 亏空三值。**机器验证的约化**——
把 6.25 精确归约到唯一 front-line 引理 `MinusWindow`:三处读数各落窗口 `(−1/φ², 1/φ)`,故
`k = μ(v)+μ(w)−μ(v+w) ∈ (φ−3, φ) ⊂ (−2, 2)`,与整性(定理 6.22)相交即得 `k∈{−1,0,1}`。
不 fake、不用有限 scan 冒充全称。 -/
theorem deficitTrichotomy_of_window (hwin : MinusWindow) : DeficitTrichotomy := by
  intro v w
  have hreal := deficit_real_eq v w
  obtain ⟨lv, uv⟩ := hwin v
  obtain ⟨lw, uw⟩ := hwin w
  obtain ⟨ls, us⟩ := hwin (v + w)
  have hφpos : (0 : ℝ) < Real.goldenRatio := Real.goldenRatio_pos
  have hsq : Real.goldenRatio ^ 2 = Real.goldenRatio + 1 := Real.goldenRatio_sq
  have hφ1 : (1 : ℝ) < Real.goldenRatio := Real.one_lt_goldenRatio
  have hφ2 : Real.goldenRatio < 2 := Real.goldenRatio_lt_two
  have hinvφ : 1 / Real.goldenRatio = Real.goldenRatio - 1 := by
    rw [div_eq_iff (ne_of_gt hφpos)]; linear_combination -hsq
  have hinvφ2 : 1 / Real.goldenRatio ^ 2 = 2 - Real.goldenRatio := by
    rw [div_eq_iff (by positivity)]; linear_combination (Real.goldenRatio - 1) * hsq
  rw [hinvφ] at uv uw us
  rw [hinvφ2] at lv lw ls
  have hup : (deficitInt v w : ℝ) < 2 := by rw [hreal]; linarith
  have hlo : (-2 : ℝ) < (deficitInt v w : ℝ) := by rw [hreal]; linarith
  have hup' : deficitInt v w < 2 := by exact_mod_cast hup
  have hlo' : -2 < deficitInt v w := by exact_mod_cast hlo
  omega

end UnifiedTheory
