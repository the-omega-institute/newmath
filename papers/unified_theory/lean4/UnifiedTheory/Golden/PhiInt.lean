import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

/-!
# ch6 精确 `ℤ[φ]`(双面亏空代数的载体)

`PhiInt` 用整数对 `⟨a, b⟩` 表示 `a + bφ`(φ²=φ+1),**绕开 `Zsqrtd` 的半整问题**
(φ=(1+√5)/2)。带 Galois 共轭 `a+bφ ↦ a+bψ = (a+b) - bφ`(ψ=1-φ)与两个实嵌入
`toRealPlus`(膨胀面 φ)、`toRealMinus`(收缩面 ψ)。整性论证(定理 6.22)靠"共轭不动 ⟺ b=0"。
-/

namespace UnifiedTheory

/-- `ℤ[φ]` 的元素 `a + bφ`(φ²=φ+1)。 -/
structure PhiInt where
  a : ℤ
  b : ℤ
deriving DecidableEq, Repr

namespace PhiInt

instance : Zero PhiInt := ⟨⟨0, 0⟩⟩
instance : One PhiInt := ⟨⟨1, 0⟩⟩
instance : Add PhiInt := ⟨fun x y => ⟨x.a + y.a, x.b + y.b⟩⟩
instance : Neg PhiInt := ⟨fun x => ⟨-x.a, -x.b⟩⟩
instance : Sub PhiInt := ⟨fun x y => ⟨x.a - y.a, x.b - y.b⟩⟩
/-- `(a+bφ)(c+dφ) = (ac+bd) + (ad+bc+bd)φ`(用 φ²=φ+1)。 -/
instance : Mul PhiInt := ⟨fun x y => ⟨x.a * y.a + x.b * y.b, x.a * y.b + x.b * y.a + x.b * y.b⟩⟩

/-- 单位 φ = 0 + 1·φ。 -/
def phi : PhiInt := ⟨0, 1⟩
/-- 整数嵌入。 -/
def ofInt (n : ℤ) : PhiInt := ⟨n, 0⟩
/-- Galois 共轭 `a+bφ ↦ (a+b) - bφ`。 -/
def conj (x : PhiInt) : PhiInt := ⟨x.a + x.b, -x.b⟩
/-- φ 的幂。 -/
def phiPow : ℕ → PhiInt
  | 0 => 1
  | n + 1 => phiPow n * phi

/-- 膨胀面实嵌入 `a + bφ`。 -/
noncomputable def toRealPlus (x : PhiInt) : ℝ := (x.a : ℝ) + (x.b : ℝ) * Real.goldenRatio
/-- 收缩面实嵌入 `a + bψ`。 -/
noncomputable def toRealMinus (x : PhiInt) : ℝ := (x.a : ℝ) + (x.b : ℝ) * Real.goldenConj

@[simp] theorem zero_a : (0 : PhiInt).a = 0 := rfl
@[simp] theorem zero_b : (0 : PhiInt).b = 0 := rfl
@[simp] theorem one_a : (1 : PhiInt).a = 1 := rfl
@[simp] theorem one_b : (1 : PhiInt).b = 0 := rfl
@[simp] theorem phi_a : phi.a = 0 := rfl
@[simp] theorem phi_b : phi.b = 1 := rfl
@[simp] theorem add_a (x y : PhiInt) : (x + y).a = x.a + y.a := rfl
@[simp] theorem add_b (x y : PhiInt) : (x + y).b = x.b + y.b := rfl
@[simp] theorem mul_a (x y : PhiInt) : (x * y).a = x.a * y.a + x.b * y.b := rfl
@[simp] theorem mul_b (x y : PhiInt) : (x * y).b = x.a * y.b + x.b * y.a + x.b * y.b := rfl
@[simp] theorem conj_a (x : PhiInt) : (conj x).a = x.a + x.b := rfl
@[simp] theorem conj_b (x : PhiInt) : (conj x).b = -x.b := rfl
@[simp] theorem ofInt_a (n : ℤ) : (ofInt n).a = n := rfl
@[simp] theorem ofInt_b (n : ℤ) : (ofInt n).b = 0 := rfl

theorem ext_iff {x y : PhiInt} : x = y ↔ x.a = y.a ∧ x.b = y.b := by
  cases x; cases y; simp [PhiInt.mk.injEq]

/-- 共轭对合。 -/
@[simp] theorem conj_conj (x : PhiInt) : conj (conj x) = x := by
  simp only [ext_iff, conj_a, conj_b]; omega

/-- 定理 6.22 核心引理:共轭不动 ⟺ φ 分量为零(即为整数)。 -/
theorem fixed_conj_iff (x : PhiInt) : conj x = x ↔ x.b = 0 := by
  simp only [ext_iff, conj_a, conj_b]; omega

/-- 收缩面 = 膨胀面 ∘ 共轭(ψ=1-φ)。 -/
theorem toRealMinus_eq_toRealPlus_conj (x : PhiInt) :
    toRealMinus x = toRealPlus (conj x) := by
  have hψ : Real.goldenConj = 1 - Real.goldenRatio := by
    have := Real.goldenRatio_add_goldenConj; linarith
  simp only [toRealMinus, toRealPlus, conj_a, conj_b]
  push_cast
  rw [hψ]; ring

@[simp] theorem toRealPlus_ofInt (n : ℤ) : toRealPlus (ofInt n) = (n : ℝ) := by
  simp [toRealPlus]

@[simp] theorem toRealPlus_phi : toRealPlus phi = Real.goldenRatio := by
  simp [toRealPlus]

theorem toRealPlus_add (x y : PhiInt) :
    toRealPlus (x + y) = toRealPlus x + toRealPlus y := by
  simp only [toRealPlus, add_a, add_b]; push_cast; ring

/-- 膨胀面是环同态(乘法):用 φ²=φ+1。 -/
theorem toRealPlus_mul (x y : PhiInt) :
    toRealPlus (x * y) = toRealPlus x * toRealPlus y := by
  simp only [toRealPlus, mul_a, mul_b]
  push_cast
  linear_combination (-(x.b : ℝ) * (y.b : ℝ)) * Real.goldenRatio_sq

@[simp] theorem toRealPlus_phiPow (n : ℕ) :
    toRealPlus (phiPow n) = Real.goldenRatio ^ n := by
  induction n with
  | zero => simp [phiPow, toRealPlus]
  | succ k ih => rw [phiPow, toRealPlus_mul, ih, toRealPlus_phi, pow_succ]

@[simp] theorem toRealMinus_add (x y : PhiInt) :
    toRealMinus (x + y) = toRealMinus x + toRealMinus y := by
  simp only [toRealMinus, add_a, add_b]; push_cast; ring

theorem toRealMinus_sub (x y : PhiInt) :
    toRealMinus (x - y) = toRealMinus x - toRealMinus y := by
  simp only [toRealMinus]
  have ha : (x - y).a = x.a - y.a := rfl
  have hb : (x - y).b = x.b - y.b := rfl
  rw [ha, hb]; push_cast; ring

@[simp] theorem toRealMinus_phi : toRealMinus phi = Real.goldenConj := by
  simp [toRealMinus]

/-- 收缩面是环同态(乘法):用 ψ²=ψ+1。 -/
theorem toRealMinus_mul (x y : PhiInt) :
    toRealMinus (x * y) = toRealMinus x * toRealMinus y := by
  simp only [toRealMinus, mul_a, mul_b]
  push_cast
  linear_combination (-(x.b : ℝ) * (y.b : ℝ)) * Real.goldenConj_sq

@[simp] theorem toRealMinus_phiPow (n : ℕ) :
    toRealMinus (phiPow n) = Real.goldenConj ^ n := by
  induction n with
  | zero => simp [phiPow, toRealMinus]
  | succ k ih => rw [phiPow, toRealMinus_mul, ih, toRealMinus_phi, pow_succ]

end PhiInt

end UnifiedTheory
