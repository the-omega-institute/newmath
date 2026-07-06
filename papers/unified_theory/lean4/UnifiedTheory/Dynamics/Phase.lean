import UnifiedTheory.Dynamics.Length
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# ch19 相位、缩放账与酉性线 + ch23.8/24.4/24.8 反射与本体零点

相位读数 `Φ_s(a)=exp(-s·L(a))`;半密度归一化后的逐项模由**缩放账**
`Λ_s(a)=(Re s−½)·L(a)`(定义 19.2)控制。核心事实(定理 19.3):在非平凡态上
`Re s=½ ⟺ Λ_s(a)=0 ⟺ 归一化逐项模=1`。反射 `J(s)=1−conj s` 的不动线恰为 `Re s=½`
(命题 23.8),缩放账镜像反号 `Λ_{J s}=−Λ_s`(定理 24.4),据此**本体零点(局部净账为零)
必落在中线**(定理 24.8)——**完全无条件,不预设 RH**:临界线由相位/反射代数涌现。
-/

namespace UnifiedTheory

open Complex

/-- 相位读数 `Φ_s(a)=exp(-s·L(a))`(定义 19.1)。 -/
noncomputable def phase (s : ℂ) (a : PrimeExp) : ℂ := Complex.exp (-s * (L a : ℂ))

/-- 相位模长 `|Φ_s(a)| = exp(−Re s · L(a))`;纯虚 `s`(Re s=0)时模长 1。 -/
theorem norm_phase (s : ℂ) (a : PrimeExp) : ‖phase s a‖ = Real.exp (-s.re * L a) := by
  rw [phase, Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]

/-- 缩放账 `Λ_s(a)=(Re s − ½)·L(a)`(定义 19.2)。半密度归一化后逐项模的对数负值。 -/
noncomputable def Lambda (s : ℂ) (a : PrimeExp) : ℝ := (s.re - 1 / 2) * L a

/-- 半密度归一化逐项模 `exp(−Λ_s(a))`。 -/
noncomputable def normModulus (s : ℂ) (a : PrimeExp) : ℝ := Real.exp (- Lambda s a)

theorem normModulus_eq_one_iff (s : ℂ) (a : PrimeExp) :
    normModulus s a = 1 ↔ Lambda s a = 0 := by
  rw [normModulus, Real.exp_eq_one_iff, neg_eq_zero]

/-- **定理 19.3(缩放账判据)**:非平凡态上缩放账为零 ⟺ `Re s = ½`。 -/
theorem Lambda_eq_zero_iff (s : ℂ) (a : PrimeExp) (h : a.val ≠ 0) :
    Lambda s a = 0 ↔ s.re = 1 / 2 := by
  rw [Lambda, mul_eq_zero]
  have hL : L a ≠ 0 := ne_of_gt (L_pos a h)
  constructor
  · rintro (h1 | h2)
    · exact sub_eq_zero.mp h1
    · exact absurd h2 hL
  · intro h1; left; rw [h1]; ring

/-- **定理 19.3(酉性线)**:非平凡态上 `Re s = ½ ⟺ 归一化逐项模 = 1`。 -/
theorem unitarity_line_iff (s : ℂ) (a : PrimeExp) (h : a.val ≠ 0) :
    s.re = 1 / 2 ↔ normModulus s a = 1 := by
  rw [normModulus_eq_one_iff, Lambda_eq_zero_iff s a h]

/-- 反射 `J(s)=1−conj s`(ch23)。 -/
def J (s : ℂ) : ℂ := 1 - (starRingEnd ℂ) s

/-- **生成式定理(反射对合)**:`J` 是对合 `J (J s) = s`。反射 `s ↦ 1 − conj s` 复合自身
还原——这与零点四元组 `{s, 1−s, conj s, 1−conj s}` 的对称群结构一致(源文档未单列此对合性)。 -/
theorem J_involutive (s : ℂ) : J (J s) = s := by
  simp only [J, map_sub, map_one, Complex.conj_conj]; ring

/-- **命题 23.8**:反射 `J` 的不动线恰为 `Re s = ½`(纯几何,不涉 zeta)。 -/
theorem J_fixed_iff (s : ℂ) : J s = s ↔ s.re = 1 / 2 := by
  rw [J, Complex.ext_iff]
  constructor
  · rintro ⟨hre, _⟩
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at hre
    linarith
  · intro h
    refine ⟨?_, ?_⟩
    · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]; linarith
    · simp only [Complex.sub_im, Complex.one_im, Complex.conj_im]; ring

/-- **定理 24.4(镜像反号)**:缩放账在反射下反号 `Λ_{J s}=−Λ_s`。 -/
theorem Lambda_mirror (s : ℂ) (a : PrimeExp) : Lambda (J s) a = - Lambda s a := by
  simp only [Lambda, J, Complex.sub_re, Complex.one_re, Complex.conj_re]
  ring

/-- **定理 19.5**:反射不动线与酉性线重合。 -/
theorem reflection_fixed_eq_unitarity (s : ℂ) (a : PrimeExp) (h : a.val ≠ 0) :
    J s = s ↔ normModulus s a = 1 := by
  rw [J_fixed_iff, unitarity_line_iff s a h]

/-- **定理 24.8(本体零点必在中线)**:若某非平凡态上局部净缩放账为零,则 `Re s = ½`。
这是 19.3 的定义展开,**无条件**——本体零点的中线性不依赖 RH。 -/
theorem ontic_balance_on_critical_line (s : ℂ) (a : PrimeExp) (h : a.val ≠ 0)
    (hbal : Lambda s a = 0) : s.re = 1 / 2 :=
  (Lambda_eq_zero_iff s a h).mp hbal

/-- 典范非平凡态 `e₂ = (2 ↦ 1)`:单素轴 `2`,见证判据非空、`L` 严格正。 -/
noncomputable def e2 : PrimeExp := ⟨Finsupp.single 2 1, by
  intro p hp
  rw [Finsupp.support_single_ne_zero 2 one_ne_zero, Finset.mem_singleton] at hp
  subst hp
  exact Nat.prime_two⟩

theorem e2_ne : e2.val ≠ 0 := Finsupp.single_ne_zero.mpr one_ne_zero

/-- 非平凡态存在(24.8 的非空见证:中线判据不是空洞的)。 -/
theorem exists_nontrivial_state : ∃ a : PrimeExp, a.val ≠ 0 := ⟨e2, e2_ne⟩

/-- **生成式定理(缩放账符号 = 临界线侧,19.4)**:非平凡态上缩放账严格正当且仅当
`Re s > ½`(对称地严格负 ⟺ `Re s < ½`)。缩放账的符号逐点记录 `s` 落在临界线的哪一侧。 -/
theorem Lambda_pos_iff (s : ℂ) (a : PrimeExp) (h : a.val ≠ 0) :
    0 < Lambda s a ↔ 1 / 2 < s.re := by
  have hL : 0 < L a := L_pos a h
  rw [Lambda, mul_pos_iff_of_pos_right hL]
  constructor <;> intro <;> linarith

theorem Lambda_neg_iff (s : ℂ) (a : PrimeExp) (h : a.val ≠ 0) :
    Lambda s a < 0 ↔ s.re < 1 / 2 := by
  have hL : 0 < L a := L_pos a h
  rw [Lambda]
  constructor
  · intro hn; nlinarith [hL, hn]
  · intro hre; nlinarith [hL, hre]

end UnifiedTheory
