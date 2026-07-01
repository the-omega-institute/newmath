import BEDC.Real.RatNumKernel

set_option maxHeartbeats 2000000

/-!
# Two-driver metric nondegeneracy (honest constructive companion)

`BackreactionMetricDegeneracy.lean` 记录的是诚实**负结果**: 单驱动 (一个相对相位差
$\Delta$) 的 schematic backreaction 度规 $g_{\mu\nu} = w\,\Delta_\mu \Delta_\nu$ 取 rank-1
外积形式, 2×2 行列式恒为 $0$ (退化 ⇒ 无逆 ⇒ 无曲率 ⇒ 生成不了几何)。

本文件是那条负结果的**建设性补**。若有**两个独立驱动** $\Delta_1 = (a_1, a_2)$,
$\Delta_2 = (b_1, b_2)$ (两个独立的 relative-holonomy 相位向量), 带各自权重 $w_1, w_2$,
度规取两个 rank-1 外积之和

$$g = w_1\,\Delta_1 \otimes \Delta_1 + w_2\,\Delta_2 \otimes \Delta_2,$$

即分量

$$g_{xx} = w_1 a_1 a_1 + w_2 b_1 b_1,\quad
  g_{xy} = w_1 a_1 a_2 + w_2 b_1 b_2,$$
$$g_{yx} = w_1 a_2 a_1 + w_2 b_2 b_1,\quad
  g_{yy} = w_1 a_2 a_2 + w_2 b_2 b_2.$$

此时行列式**不再恒为零**, 而是 Cauchy–Binet 给出的加权 wedge (叉积) 平方:

$$\det g = g_{xx} g_{yy} - g_{xy} g_{yx}
        = w_1 w_2\,(a_1 b_2 - a_2 b_1)^2
        = w_1 w_2\,(\Delta_1 \wedge \Delta_2)^2.$$

因此 $\det g \neq 0$ **当且仅当** $w_1 w_2 \neq 0$ 且 $\Delta_1 \wedge \Delta_2 \neq 0$,
即两驱动**线性无关**。这说明: 要让 schematic backreaction 给出**非退化**的 emergent
geometry, **至少需要 2 个独立的 relative-holonomy 驱动** —— 单驱动必退化
(见 `backreaction_metric_det_zero`), 两独立驱动才可能非退化。

**范围声明**: 本文件形式化的是纯代数恒等式 $\det g = w_1 w_2\,(a_1 b_2 - a_2 b_1)^2$
(2×2 行列式的 Cauchy–Binet 展开), 用真实 `RatNum` ring lemma 真证。$w_i / a_i / b_i$
都是 schematic、非物理的占位量; 这里没有任何物理统一定理, 也不声称物理度规的存在性。
形式化捕获的只是"两独立驱动 ⇒ 行列式 = 加权 wedge²"这一代数骨架, 与单驱动退化负结果
形成建设性对照。-/

namespace BEDC.Derived.Visions

open BEDC.Derived.RationalUp
open BEDC.Real.RatNumKernel (ratMul_add_left ratMul_add_right)
open BEDC.Derived.LocatedReal
  (ratAdd_assoc_local ratNeg_add_dist_local ratNeg_neg_local ratAdd_neg_local)

/-! 权重 $w_1, w_2$ 与两个 2-向量分量 $a_1, a_2, b_1, b_2$ (即 $\Delta_1 = (a_1, a_2)$,
$\Delta_2 = (b_1, b_2)$) 都取 BEDC 的 `RatNum`。这些是 schematic 占位量, 不是物理测量值。 -/

/-- $g_{xx} = w_1 a_1 a_1 + w_2 b_1 b_1$ (两 rank-1 外积之和的 $xx$ 分量)。签名统一取六参,
$a_2, b_2$ 在此分量不出现。 -/
def twoDriverGXX (w1 w2 a1 _a2 b1 _b2 : RatNum) : RatNum :=
  ratAdd (ratMul (ratMul w1 a1) a1) (ratMul (ratMul w2 b1) b1)

/-- $g_{xy} = w_1 a_1 a_2 + w_2 b_1 b_2$。 -/
def twoDriverGXY (w1 w2 a1 a2 b1 b2 : RatNum) : RatNum :=
  ratAdd (ratMul (ratMul w1 a1) a2) (ratMul (ratMul w2 b1) b2)

/-- $g_{yx} = w_1 a_2 a_1 + w_2 b_2 b_1$。 -/
def twoDriverGYX (w1 w2 a1 a2 b1 b2 : RatNum) : RatNum :=
  ratAdd (ratMul (ratMul w1 a2) a1) (ratMul (ratMul w2 b2) b1)

/-- $g_{yy} = w_1 a_2 a_2 + w_2 b_2 b_2$。签名统一取六参, $a_1, b_1$ 在此分量不出现。 -/
def twoDriverGYY (w1 w2 _a1 a2 _b1 b2 : RatNum) : RatNum :=
  ratAdd (ratMul (ratMul w1 a2) a2) (ratMul (ratMul w2 b2) b2)

/-- 2×2 行列式 $\det g = g_{xx} g_{yy} - g_{xy} g_{yx}$。 -/
def twoDriverMetricDet (w1 w2 a1 a2 b1 b2 : RatNum) : RatNum :=
  ratSub
    (ratMul (twoDriverGXX w1 w2 a1 a2 b1 b2) (twoDriverGYY w1 w2 a1 a2 b1 b2))
    (ratMul (twoDriverGXY w1 w2 a1 a2 b1 b2) (twoDriverGYX w1 w2 a1 a2 b1 b2))

/-- 两驱动的 wedge (叉积) $\Delta_1 \wedge \Delta_2 = a_1 b_2 - a_2 b_1$。 -/
def wedge (a1 a2 b1 b2 : RatNum) : RatNum :=
  ratSub (ratMul a1 b2) (ratMul a2 b1)

/-! ## 环运算 helper (neg / sub 与乘法交互)

以下 private helper 复用 BEDC RatNum 的公开 ring lemma (`ratMul_add_left/right`,
`ratMul_comm`, `ratMul_assoc`, `ratEq_of_num_den_intEq`, `IntegerUp_mul_neg`),
全 0-axiom, 无 fake refl。 -/

/-- $x \cdot (-y) = -(x y)$。 -/
private theorem ratMul_neg_right (x y : RatNum) :
    RatEq (ratMul x (ratNeg y)) (ratNeg (ratMul x y)) := by
  apply ratEq_of_num_den_intEq
  · unfold ratMul ratNeg
    exact BEDC.Algebra.Rel.IntegerUp_mul_neg x.num y.num
  · unfold ratMul ratNeg ratDenInt
    exact IntEq_refl _

/-- `ratSub` 对两侧的 congruence。 -/
private theorem ratSub_congr {x x' y y' : RatNum} :
    RatEq x x' -> RatEq y y' -> RatEq (ratSub x y) (ratSub x' y') := by
  intro hx hy
  unfold ratSub
  exact ratAdd_respects hx (ratNeg_respects hy)

/-- 左侧对 `ratSub` 的分配: $a (b - c) = a b - a c$。 -/
private theorem ratMul_sub_left (a b c : RatNum) :
    RatEq (ratMul a (ratSub b c)) (ratSub (ratMul a b) (ratMul a c)) := by
  unfold ratSub
  exact RatEq_trans _ _ _
    (ratMul_add_left a b (ratNeg c))
    (ratAdd_respects (RatEq_refl (ratMul a b)) (ratMul_neg_right a c))

/-- 右侧对 `ratSub` 的分配: $(a - b) c = a c - b c$。 -/
private theorem ratMul_sub_right (a b c : RatNum) :
    RatEq (ratMul (ratSub a b) c) (ratSub (ratMul a c) (ratMul b c)) := by
  exact RatEq_trans _ _ _
    (ratMul_comm (ratSub a b) c)
    (RatEq_trans _ _ _
      (ratMul_sub_left c a b)
      (ratSub_congr (ratMul_comm c a) (ratMul_comm c b)))

/-! ## 单项规范化

把任意 6-因子左结合乘积归一到规范键序 `w1 · w2 · a? · a? · b? · b?` 的邻位换位工具。
每个 g 分量的每个加项都是形如 `((w · p) · q)` 的 3-因子, 两两相乘得 6-因子。 -/

/-- 反结合: `RatEq (a * (b * c)) ((a * b) * c)`。 -/
private theorem ratMul_assoc_symm (a b c : RatNum) :
    RatEq (ratMul a (ratMul b c)) (ratMul (ratMul a b) c) :=
  RatEq_symm (ratMul_assoc a b c)

/-- 右邻位换位: `RatEq ((a * b) * c) ((a * c) * b)`。 -/
private theorem ratMul_right_comm (a b c : RatNum) :
    RatEq (ratMul (ratMul a b) c) (ratMul (ratMul a c) b) := by
  refine RatEq_trans _ (ratMul a (ratMul b c)) _ (ratMul_assoc a b c) ?_
  refine RatEq_trans _ (ratMul a (ratMul c b)) _
    (ratMul_respects_right (ratMul_comm b c)) ?_
  exact ratMul_assoc_symm a c b

/-- 3-因子左结合乘积 $((f_1 f_2) f_3)$。每个 rank-1 外积加项都是这个形状 (权重 · 分量 · 分量)。 -/
private def mono3 (f1 f2 f3 : RatNum) : RatNum :=
  ratMul (ratMul f1 f2) f3

/-- 6-因子左结合规范乘积 $(((((f_1 f_2) f_3) f_4) f_5) f_6)$。两个 `mono3` 相乘的规范形。 -/
private def mono6 (f1 f2 f3 f4 f5 f6 : RatNum) : RatNum :=
  ratMul (ratMul (ratMul (ratMul (ratMul f1 f2) f3) f4) f5) f6

/-- 把两个 `mono3` 的乘积展平并把两个权重靠拢, 归一到规范形
`mono6 w w' p q r s`。这是所有 8 个单项共用的规范化引擎。 -/
private theorem mul_mono3_mono3 (w p q w' r s : RatNum) :
    RatEq (ratMul (mono3 w p q) (mono3 w' r s)) (mono6 w w' p q r s) := by
  unfold mono3 mono6
  -- A := ((w*p)*q).  展平: A * ((w'*r)*s) ≃ (((A*w')*r)*s)
  refine RatEq_trans _
    (ratMul (ratMul (ratMul (ratMul (ratMul w p) q) w') r) s) _ ?_ ?_
  · -- A * ((w'*r)*s) ≃ (A*(w'*r))*s ≃ ((A*w')*r)*s
    refine RatEq_trans _
      (ratMul (ratMul (ratMul (ratMul w p) q) (ratMul w' r)) s) _ ?_ ?_
    · exact ratMul_assoc_symm (ratMul (ratMul w p) q) (ratMul w' r) s
    · refine ratMul_respects_left ?_
      exact ratMul_assoc_symm (ratMul (ratMul w p) q) w' r
  · -- 现: 左结合链 [w p q w' r s] → 目标 [w w' p q r s]
    -- swap pos3,4 (q,w'): [w p w' q r s]
    refine RatEq_trans _
      (ratMul (ratMul (ratMul (ratMul (ratMul w p) w') q) r) s) _ ?_ ?_
    · refine ratMul_respects_left ?_
      refine ratMul_respects_left ?_
      exact ratMul_right_comm (ratMul w p) q w'
    -- swap pos2,3 (p,w'): [w w' p q r s]
    refine ratMul_respects_left ?_
    refine ratMul_respects_left ?_
    refine ratMul_respects_left ?_
    exact ratMul_right_comm w p w'

/-! ## 双二项式展开

$(A_1 + A_2)(B_1 + B_2) \simeq (A_1 B_1 + A_1 B_2) + (A_2 B_1 + A_2 B_2)$。用两次分配律。 -/

/-- 两个二项式乘积展成四项和 (保持左/右分配的括号结构)。 -/
private theorem mul_binom_binom (a1 a2 b1 b2 : RatNum) :
    RatEq (ratMul (ratAdd a1 a2) (ratAdd b1 b2))
      (ratAdd (ratAdd (ratMul a1 b1) (ratMul a1 b2))
        (ratAdd (ratMul a2 b1) (ratMul a2 b2))) := by
  -- (a1+a2)*(b1+b2) ≃ a1*(b1+b2) + a2*(b1+b2)
  refine RatEq_trans _
    (ratAdd (ratMul a1 (ratAdd b1 b2)) (ratMul a2 (ratAdd b1 b2))) _
    (ratMul_add_right a1 a2 (ratAdd b1 b2)) ?_
  -- 各自 left-distrib
  exact ratAdd_respects (ratMul_add_left a1 b1 b2) (ratMul_add_left a2 b1 b2)

/-! ## `mono6` 邻位换位

`mono6 f1 f2 f3 f4 f5 f6 = (((((f1 f2) f3) f4) f5) f6)`。以下 5 个引理各交换一对相邻因子,
组合即可把任意 `mono6` 冒泡排序到规范因子序。 -/

/-- 交换 `mono6` 的第 5、6 位。 -/
private theorem mono6_swap56 (f1 f2 f3 f4 f5 f6 : RatNum) :
    RatEq (mono6 f1 f2 f3 f4 f5 f6) (mono6 f1 f2 f3 f4 f6 f5) := by
  unfold mono6
  exact ratMul_right_comm (ratMul (ratMul (ratMul f1 f2) f3) f4) f5 f6

/-- 交换 `mono6` 的第 4、5 位。 -/
private theorem mono6_swap45 (f1 f2 f3 f4 f5 f6 : RatNum) :
    RatEq (mono6 f1 f2 f3 f4 f5 f6) (mono6 f1 f2 f3 f5 f4 f6) := by
  unfold mono6
  refine ratMul_respects_left ?_
  exact ratMul_right_comm (ratMul (ratMul f1 f2) f3) f4 f5

/-- 交换 `mono6` 的第 3、4 位。 -/
private theorem mono6_swap34 (f1 f2 f3 f4 f5 f6 : RatNum) :
    RatEq (mono6 f1 f2 f3 f4 f5 f6) (mono6 f1 f2 f4 f3 f5 f6) := by
  unfold mono6
  refine ratMul_respects_left ?_
  refine ratMul_respects_left ?_
  exact ratMul_right_comm (ratMul f1 f2) f3 f4

/-- 交换 `mono6` 的第 2、3 位。 -/
private theorem mono6_swap23 (f1 f2 f3 f4 f5 f6 : RatNum) :
    RatEq (mono6 f1 f2 f3 f4 f5 f6) (mono6 f1 f3 f2 f4 f5 f6) := by
  unfold mono6
  refine ratMul_respects_left ?_
  refine ratMul_respects_left ?_
  refine ratMul_respects_left ?_
  exact ratMul_right_comm f1 f2 f3

/-- 交换 `mono6` 的第 1、2 位。 -/
private theorem mono6_swap12 (f1 f2 f3 f4 f5 f6 : RatNum) :
    RatEq (mono6 f1 f2 f3 f4 f5 f6) (mono6 f2 f1 f3 f4 f5 f6) := by
  unfold mono6
  refine ratMul_respects_left ?_
  refine ratMul_respects_left ?_
  refine ratMul_respects_left ?_
  refine ratMul_respects_left ?_
  exact ratMul_comm f1 f2

/-! ## 对角积与反对角积的规范展开

把 `gXX*gYY` 与 `gXY*gYX` 各展成 4 个规范 `mono6` 之和。 -/

/-- `gXX*gYY` 展成四个规范单项之和。四项键分别为
`w1w1a1a1a2a2`, `w1w2a1a1b2b2`, `w2w1b1b1a2a2`, `w2w2b1b1b2b2`。 -/
private theorem gXXgYY_expand (w1 w2 a1 a2 b1 b2 : RatNum) :
    RatEq (ratMul (twoDriverGXX w1 w2 a1 a2 b1 b2) (twoDriverGYY w1 w2 a1 a2 b1 b2))
      (ratAdd
        (ratAdd (mono6 w1 w1 a1 a1 a2 a2) (mono6 w1 w2 a1 a1 b2 b2))
        (ratAdd (mono6 w2 w1 b1 b1 a2 a2) (mono6 w2 w2 b1 b1 b2 b2))) := by
  unfold twoDriverGXX twoDriverGYY
  refine RatEq_trans _
    (ratAdd
      (ratAdd
        (ratMul (mono3 w1 a1 a1) (mono3 w1 a2 a2))
        (ratMul (mono3 w1 a1 a1) (mono3 w2 b2 b2)))
      (ratAdd
        (ratMul (mono3 w2 b1 b1) (mono3 w1 a2 a2))
        (ratMul (mono3 w2 b1 b1) (mono3 w2 b2 b2)))) _
    (mul_binom_binom (mono3 w1 a1 a1) (mono3 w2 b1 b1)
      (mono3 w1 a2 a2) (mono3 w2 b2 b2)) ?_
  exact ratAdd_respects
    (ratAdd_respects (mul_mono3_mono3 w1 a1 a1 w1 a2 a2)
      (mul_mono3_mono3 w1 a1 a1 w2 b2 b2))
    (ratAdd_respects (mul_mono3_mono3 w2 b1 b1 w1 a2 a2)
      (mul_mono3_mono3 w2 b1 b1 w2 b2 b2))

/-- `gXY*gYX` 展成四个规范单项之和。四项键分别为
`w1w1a1a2a2a1`, `w1w2a1a2b2b1`, `w2w1b1b2a2a1`, `w2w2b1b2b2b1`。 -/
private theorem gXYgYX_expand (w1 w2 a1 a2 b1 b2 : RatNum) :
    RatEq (ratMul (twoDriverGXY w1 w2 a1 a2 b1 b2) (twoDriverGYX w1 w2 a1 a2 b1 b2))
      (ratAdd
        (ratAdd (mono6 w1 w1 a1 a2 a2 a1) (mono6 w1 w2 a1 a2 b2 b1))
        (ratAdd (mono6 w2 w1 b1 b2 a2 a1) (mono6 w2 w2 b1 b2 b2 b1))) := by
  unfold twoDriverGXY twoDriverGYX
  refine RatEq_trans _
    (ratAdd
      (ratAdd
        (ratMul (mono3 w1 a1 a2) (mono3 w1 a2 a1))
        (ratMul (mono3 w1 a1 a2) (mono3 w2 b2 b1)))
      (ratAdd
        (ratMul (mono3 w2 b1 b2) (mono3 w1 a2 a1))
        (ratMul (mono3 w2 b1 b2) (mono3 w2 b2 b1)))) _
    (mul_binom_binom (mono3 w1 a1 a2) (mono3 w2 b1 b2)
      (mono3 w1 a2 a1) (mono3 w2 b2 b1)) ?_
  exact ratAdd_respects
    (ratAdd_respects (mul_mono3_mono3 w1 a1 a2 w1 a2 a1)
      (mul_mono3_mono3 w1 a1 a2 w2 b2 b1))
    (ratAdd_respects (mul_mono3_mono3 w2 b1 b2 w1 a2 a1)
      (mul_mono3_mono3 w2 b1 b2 w2 b2 b1))

/-- 把 `(((w1 w2)(p q))(r s))` 展平到规范 `mono6 w1 w2 p q r s`。RHS `w1 w2 wedge²`
展开后每个单项都是这个形状 (`W = w1 w2`, 两个 `wedge` 因子各是一对乘积)。 -/
private theorem mul_W_pair_pair (w1 w2 p q r s : RatNum) :
    RatEq
      (ratMul (ratMul (ratMul w1 w2) (ratMul p q)) (ratMul r s))
      (mono6 w1 w2 p q r s) := by
  unfold mono6
  -- X := ((w1 w2)(p q)). X * (r s) ≃ (X * r) * s
  refine RatEq_trans _
    (ratMul (ratMul (ratMul (ratMul w1 w2) (ratMul p q)) r) s) _
    (ratMul_assoc_symm (ratMul (ratMul w1 w2) (ratMul p q)) r s) ?_
  -- 内层 (w1 w2)(p q) ≃ (((w1 w2) p) q)
  refine ratMul_respects_left ?_
  refine ratMul_respects_left ?_
  exact ratMul_assoc_symm (ratMul w1 w2) p q

/-! ## 把 8 个单项排序到规范因子序

规范序 $w_1 < w_2 < a_1 < a_2 < b_1 < b_2$。同因子多重集的 `mono6` 排序后相等,
`gXX*gYY` 与 `gXY*gYX` 里各有一对高次项 (纯 $w_1$/纯 $w_2$) 排序后逐一相等而抵消。 -/

/-- 反对角 `S1 = w1 w1 a1 a2 a2 a1` 排序到对角 `T1 = w1 w1 a1 a1 a2 a2` 的规范形。 -/
private theorem s1_norm (w1 a1 a2 : RatNum) :
    RatEq (mono6 w1 w1 a1 a2 a2 a1) (mono6 w1 w1 a1 a1 a2 a2) := by
  refine RatEq_trans _ (mono6 w1 w1 a1 a2 a1 a2) _
    (mono6_swap56 w1 w1 a1 a2 a2 a1) ?_
  exact mono6_swap45 w1 w1 a1 a2 a1 a2

/-- 反对角 `S4 = w2 w2 b1 b2 b2 b1` 排序到对角 `T4 = w2 w2 b1 b1 b2 b2` 的规范形。 -/
private theorem s4_norm (w2 b1 b2 : RatNum) :
    RatEq (mono6 w2 w2 b1 b2 b2 b1) (mono6 w2 w2 b1 b1 b2 b2) := by
  refine RatEq_trans _ (mono6 w2 w2 b1 b2 b1 b2) _
    (mono6_swap56 w2 w2 b1 b2 b2 b1) ?_
  exact mono6_swap45 w2 w2 b1 b2 b1 b2

/-- 对角残项 `T3 = w2 w1 b1 b1 a2 a2` 排序到规范 `w1 w2 a2 a2 b1 b1`。 -/
private theorem t3_norm (w1 w2 a2 b1 : RatNum) :
    RatEq (mono6 w2 w1 b1 b1 a2 a2) (mono6 w1 w2 a2 a2 b1 b1) := by
  -- [w2 w1 b1 b1 a2 a2]
  refine RatEq_trans _ (mono6 w1 w2 b1 b1 a2 a2) _
    (mono6_swap12 w2 w1 b1 b1 a2 a2) ?_
  -- [w1 w2 b1 b1 a2 a2] → 把 a2 a2 移到 b1 b1 前
  -- swap45: [w1 w2 b1 a2 b1 a2]  (交换 pos4,5: b1,a2)
  refine RatEq_trans _ (mono6 w1 w2 b1 a2 b1 a2) _
    (mono6_swap45 w1 w2 b1 b1 a2 a2) ?_
  -- swap34: [w1 w2 a2 b1 b1 a2]
  refine RatEq_trans _ (mono6 w1 w2 a2 b1 b1 a2) _
    (mono6_swap34 w1 w2 b1 a2 b1 a2) ?_
  -- swap56: [w1 w2 a2 b1 a2 b1]
  refine RatEq_trans _ (mono6 w1 w2 a2 b1 a2 b1) _
    (mono6_swap56 w1 w2 a2 b1 b1 a2) ?_
  -- swap45: [w1 w2 a2 a2 b1 b1]
  exact mono6_swap45 w1 w2 a2 b1 a2 b1

/-- 反对角残项 `S2 = w1 w2 a1 a2 b2 b1` 排序到规范 `w1 w2 a1 a2 b1 b2`。 -/
private theorem s2_norm (w1 w2 a1 a2 b1 b2 : RatNum) :
    RatEq (mono6 w1 w2 a1 a2 b2 b1) (mono6 w1 w2 a1 a2 b1 b2) :=
  mono6_swap56 w1 w2 a1 a2 b2 b1

/-- 反对角残项 `S3 = w2 w1 b1 b2 a2 a1` 排序到规范 `w1 w2 a1 a2 b1 b2`。 -/
private theorem s3_norm (w1 w2 a1 a2 b1 b2 : RatNum) :
    RatEq (mono6 w2 w1 b1 b2 a2 a1) (mono6 w1 w2 a1 a2 b1 b2) := by
  -- [w2 w1 b1 b2 a2 a1]
  refine RatEq_trans _ (mono6 w1 w2 b1 b2 a2 a1) _
    (mono6_swap12 w2 w1 b1 b2 a2 a1) ?_
  -- 目标 [w1 w2 a1 a2 b1 b2]. 现 [w1 w2 b1 b2 a2 a1], 尾四位 [b1 b2 a2 a1] → [a1 a2 b1 b2]
  -- swap56: [w1 w2 b1 b2 a1 a2]
  refine RatEq_trans _ (mono6 w1 w2 b1 b2 a1 a2) _
    (mono6_swap56 w1 w2 b1 b2 a2 a1) ?_
  -- swap45: [w1 w2 b1 a1 b2 a2]
  refine RatEq_trans _ (mono6 w1 w2 b1 a1 b2 a2) _
    (mono6_swap45 w1 w2 b1 b2 a1 a2) ?_
  -- swap34: [w1 w2 a1 b1 b2 a2]
  refine RatEq_trans _ (mono6 w1 w2 a1 b1 b2 a2) _
    (mono6_swap34 w1 w2 b1 a1 b2 a2) ?_
  -- swap56: [w1 w2 a1 b1 a2 b2]
  refine RatEq_trans _ (mono6 w1 w2 a1 b1 a2 b2) _
    (mono6_swap56 w1 w2 a1 b1 b2 a2) ?_
  -- swap45: [w1 w2 a1 a2 b1 b2]
  exact mono6_swap45 w1 w2 a1 b1 a2 b2

/-! ## 加法群残项恒等式

对角展开 `(T1+T2)+(T3+T4)` 减去反对角展开 `(T1+E)+(E+T4)`, 其中 `T1, T4` 两两抵消,
残项恰为 `(T2-E)-(E-T3)`。这是 `(RatNum, +, -)` 上的纯加法群恒等式, 与乘法无关。 -/

/-- 四原子重排: `(x + n) + (n' + y) ≃ (x + y) + (n + n')`。 -/
private theorem add4_regroup (x n n' y : RatNum) :
    RatEq (ratAdd (ratAdd x n) (ratAdd n' y))
      (ratAdd (ratAdd x y) (ratAdd n n')) := by
  -- (x+n)+(n'+y) ≃ x+(n+(n'+y))
  refine RatEq_trans _ (ratAdd x (ratAdd n (ratAdd n' y))) _
    (ratAdd_assoc_local x n (ratAdd n' y)) ?_
  -- n+(n'+y) ≃ (n+n')+y ≃ (n'+n)+y ... 先 ≃ n+(n'+y); 目标凑 (x+y)+(n+n')
  -- x+(n+(n'+y)) ≃ x+((n+n')+y) ≃ x+((n+n')+y)
  refine RatEq_trans _ (ratAdd x (ratAdd (ratAdd n n') y)) _
    (ratAdd_respects (RatEq_refl x)
      (RatEq_symm (ratAdd_assoc_local n n' y))) ?_
  -- x+((n+n')+y) ≃ x+(y+(n+n'))
  refine RatEq_trans _ (ratAdd x (ratAdd y (ratAdd n n'))) _
    (ratAdd_respects (RatEq_refl x) (ratAdd_comm (ratAdd n n') y)) ?_
  -- x+(y+(n+n')) ≃ (x+y)+(n+n')
  exact RatEq_symm (ratAdd_assoc_local x y (ratAdd n n'))

/-- 四原子中位换位: `(x + m) + (m' + y) ≃ (x + m') + (m + y)`。 -/
private theorem add4_swap_mid (x m m' y : RatNum) :
    RatEq (ratAdd (ratAdd x m) (ratAdd m' y))
      (ratAdd (ratAdd x m') (ratAdd m y)) := by
  -- (x+m)+(m'+y) ≃ x+(m+(m'+y))
  refine RatEq_trans _ (ratAdd x (ratAdd m (ratAdd m' y))) _
    (ratAdd_assoc_local x m (ratAdd m' y)) ?_
  -- m+(m'+y) ≃ (m+m')+y ≃ (m'+m)+y ≃ m'+(m+y)
  refine RatEq_trans _ (ratAdd x (ratAdd m' (ratAdd m y))) _
    (ratAdd_respects (RatEq_refl x) ?_) ?_
  · refine RatEq_trans _ (ratAdd (ratAdd m m') y) _
      (RatEq_symm (ratAdd_assoc_local m m' y)) ?_
    refine RatEq_trans _ (ratAdd (ratAdd m' m) y) _
      (ratAdd_respects (ratAdd_comm m m') (RatEq_refl y)) ?_
    exact ratAdd_assoc_local m' m y
  -- x+(m'+(m+y)) ≃ (x+m')+(m+y)
  exact RatEq_symm (ratAdd_assoc_local x m' (ratAdd m y))

/-- 四原子交叉对消: `(a + b) + (-a + -b) ≃ 0`。 -/
private theorem add4_cross_cancel (a b : RatNum) :
    RatEq (ratAdd (ratAdd a b) (ratAdd (ratNeg a) (ratNeg b))) ratZero := by
  -- (a+b)+(-a+-b) ≃ a+(b+(-a+-b))
  refine RatEq_trans _ (ratAdd a (ratAdd b (ratAdd (ratNeg a) (ratNeg b)))) _
    (ratAdd_assoc_local a b (ratAdd (ratNeg a) (ratNeg b))) ?_
  -- b+(-a+-b) ≃ b+(-b+-a) ≃ (b+-b)+-a ≃ 0 + -a ≃ -a
  have hInner :
      RatEq (ratAdd b (ratAdd (ratNeg a) (ratNeg b))) (ratNeg a) := by
    refine RatEq_trans _ (ratAdd b (ratAdd (ratNeg b) (ratNeg a))) _
      (ratAdd_respects (RatEq_refl b) (ratAdd_comm (ratNeg a) (ratNeg b))) ?_
    refine RatEq_trans _ (ratAdd (ratAdd b (ratNeg b)) (ratNeg a)) _
      (RatEq_symm (ratAdd_assoc_local b (ratNeg b) (ratNeg a))) ?_
    refine RatEq_trans _ (ratAdd ratZero (ratNeg a)) _
      (ratAdd_respects (ratAdd_neg_local b) (RatEq_refl (ratNeg a))) ?_
    exact ratZero_add_left (ratNeg a)
  -- a + (-a) ≃ 0
  refine RatEq_trans _ (ratAdd a (ratNeg a)) _
    (ratAdd_respects (RatEq_refl a) hInner) ?_
  exact ratAdd_neg_local a

/-- 八原子对消: `((t1+t2)+(t3+t4)) + ((-t1 + n) + (n' + -t4)) ≃ (t2+t3)+(n+n')`。
`t1`/`t4` 与其相反数抵消, 只留下中间四项。 -/
private theorem add8_cancel_outer (t1 t2 t3 t4 n n' : RatNum) :
    RatEq
      (ratAdd (ratAdd (ratAdd t1 t2) (ratAdd t3 t4))
        (ratAdd (ratAdd (ratNeg t1) n) (ratAdd n' (ratNeg t4))))
      (ratAdd (ratAdd t2 t3) (ratAdd n n')) := by
  -- 先把两大块各自 add4_regroup:
  --   (t1+t2)+(t3+t4) ≃ (t1+t4)+(t2+t3)     [x=t1,n=t2,n'=t3,y=t4]
  --   (-t1+n)+(n'+-t4) ≃ (-t1+-t4)+(n+n')   [x=-t1,n=n,n'=n',y=-t4]
  refine RatEq_trans _
    (ratAdd (ratAdd (ratAdd t1 t4) (ratAdd t2 t3))
      (ratAdd (ratAdd (ratNeg t1) (ratNeg t4)) (ratAdd n n'))) _
    (ratAdd_respects (add4_regroup t1 t2 t3 t4)
      (add4_regroup (ratNeg t1) n n' (ratNeg t4))) ?_
  -- 记 A=(t1+t4), B=(t2+t3), C=(-t1+-t4), D=(n+n'). 目标 (A+B)+(C+D) ≃ B+D.
  -- add4_swap_mid A B C D: (A+B)+(C+D) ≃ (A+C)+(B+D)   [x=A,m=B,m'=C,y=D]
  refine RatEq_trans _
    (ratAdd (ratAdd (ratAdd t1 t4) (ratAdd (ratNeg t1) (ratNeg t4)))
      (ratAdd (ratAdd t2 t3) (ratAdd n n'))) _
    (add4_swap_mid (ratAdd t1 t4) (ratAdd t2 t3)
      (ratAdd (ratNeg t1) (ratNeg t4)) (ratAdd n n')) ?_
  -- (A+C) = (t1+t4)+(-t1+-t4) ≃ zero (add4_cross_cancel), 则 zero + (B+D) ≃ B+D.
  refine RatEq_trans _
    (ratAdd ratZero (ratAdd (ratAdd t2 t3) (ratAdd n n'))) _
    (ratAdd_respects (add4_cross_cancel t1 t4) (RatEq_refl _)) ?_
  exact ratZero_add_left _

/-- 核心加法群残项恒等式: 对角展开减反对角展开的 `t1`/`t4` 抵消后, 残项恰为
`(t2 - e) - (e - t3)`。 -/
private theorem residual_identity (t1 t2 t3 t4 e : RatNum) :
    RatEq
      (ratSub (ratAdd (ratAdd t1 t2) (ratAdd t3 t4))
        (ratAdd (ratAdd t1 e) (ratAdd e t4)))
      (ratSub (ratSub t2 e) (ratSub e t3)) := by
  -- 共同规范形 C := (t2+t3) + (-e + -e).
  -- 左侧: unfold ratSub, neg N ≃ (-t1 + -e)+(-e + -t4), 再 add8_cancel_outer.
  have hLeft :
      RatEq
        (ratSub (ratAdd (ratAdd t1 t2) (ratAdd t3 t4))
          (ratAdd (ratAdd t1 e) (ratAdd e t4)))
        (ratAdd (ratAdd t2 t3) (ratAdd (ratNeg e) (ratNeg e))) := by
    unfold ratSub
    have hnegN :
        RatEq (ratNeg (ratAdd (ratAdd t1 e) (ratAdd e t4)))
          (ratAdd (ratAdd (ratNeg t1) (ratNeg e))
            (ratAdd (ratNeg e) (ratNeg t4))) := by
      refine RatEq_trans _
        (ratAdd (ratNeg (ratAdd t1 e)) (ratNeg (ratAdd e t4))) _
        (ratNeg_add_dist_local (ratAdd t1 e) (ratAdd e t4)) ?_
      exact ratAdd_respects
        (ratNeg_add_dist_local t1 e) (ratNeg_add_dist_local e t4)
    refine RatEq_trans _
      (ratAdd (ratAdd (ratAdd t1 t2) (ratAdd t3 t4))
        (ratAdd (ratAdd (ratNeg t1) (ratNeg e))
          (ratAdd (ratNeg e) (ratNeg t4)))) _
      (ratAdd_respects (RatEq_refl _) hnegN) ?_
    exact add8_cancel_outer t1 t2 t3 t4 (ratNeg e) (ratNeg e)
  -- 右侧: (t2 + -e) + neg(e + -t3) ≃ (t2 + -e) + (-e + t3) ≃ (t2+t3)+(-e+-e).
  have hRight :
      RatEq
        (ratSub (ratSub t2 e) (ratSub e t3))
        (ratAdd (ratAdd t2 t3) (ratAdd (ratNeg e) (ratNeg e))) := by
    unfold ratSub
    -- neg(e + -t3) ≃ -e + -(-t3) ≃ -e + t3
    have hneg :
        RatEq (ratNeg (ratAdd e (ratNeg t3))) (ratAdd (ratNeg e) t3) := by
      refine RatEq_trans _ (ratAdd (ratNeg e) (ratNeg (ratNeg t3))) _
        (ratNeg_add_dist_local e (ratNeg t3)) ?_
      exact ratAdd_respects (RatEq_refl (ratNeg e)) (ratNeg_neg_local t3)
    refine RatEq_trans _
      (ratAdd (ratAdd t2 (ratNeg e)) (ratAdd (ratNeg e) t3)) _
      (ratAdd_respects (RatEq_refl _) hneg) ?_
    -- (t2 + -e) + (-e + t3) ≃ (t2+t3)+(-e+-e)  [add4_regroup t2 (-e) (-e) t3]
    exact add4_regroup t2 (ratNeg e) (ratNeg e) t3
  exact RatEq_trans _ _ _ hLeft (RatEq_symm hRight)

/-! ## RHS 展开: `w1 w2 wedge²` 归到规范残项 -/

/-- `WQ*P = ((w1 w2)(a2 b1))(a1 b2)` 归约的 raw `mono6 w1 w2 a2 b1 a1 b2` 排序到规范
`E = w1 w2 a1 a2 b1 b2`。 -/
private theorem wqp_norm (w1 w2 a1 a2 b1 b2 : RatNum) :
    RatEq (mono6 w1 w2 a2 b1 a1 b2) (mono6 w1 w2 a1 a2 b1 b2) := by
  -- [w1 w2 a2 b1 a1 b2]
  -- swap45 (b1,a1): [w1 w2 a2 a1 b1 b2]
  refine RatEq_trans _ (mono6 w1 w2 a2 a1 b1 b2) _
    (mono6_swap45 w1 w2 a2 b1 a1 b2) ?_
  -- swap34 (a2,a1): [w1 w2 a1 a2 b1 b2]
  exact mono6_swap34 w1 w2 a2 a1 b1 b2

/-- RHS `w1 w2 wedge wedge` 展成规范残项
`(T2 - E) - (E - T3c)`, 其中
`T2 = w1 w2 a1 a1 b2 b2`, `E = w1 w2 a1 a2 b1 b2`, `T3c = w1 w2 a2 a2 b1 b1`。 -/
private theorem rhs_expand (w1 w2 a1 a2 b1 b2 : RatNum) :
    RatEq
      (ratMul (ratMul (ratMul w1 w2) (wedge a1 a2 b1 b2)) (wedge a1 a2 b1 b2))
      (ratSub
        (ratSub (mono6 w1 w2 a1 a1 b2 b2) (mono6 w1 w2 a1 a2 b1 b2))
        (ratSub (mono6 w1 w2 a1 a2 b1 b2) (mono6 w1 w2 a2 a2 b1 b1))) := by
  unfold wedge
  -- 记 W = w1 w2, P = a1 b2, Q = a2 b1, wg = P - Q.
  -- 第一步: (W * (P-Q)) * (P-Q) ≃ ((W*P) - (W*Q)) * (P-Q)
  refine RatEq_trans _
    (ratMul
      (ratSub (ratMul (ratMul w1 w2) (ratMul a1 b2))
        (ratMul (ratMul w1 w2) (ratMul a2 b1)))
      (ratSub (ratMul a1 b2) (ratMul a2 b1))) _
    (ratMul_respects_left
      (ratMul_sub_left (ratMul w1 w2) (ratMul a1 b2) (ratMul a2 b1))) ?_
  -- 第二步: right-distrib over (P-Q): ≃ ((WP-WQ)*P) - ((WP-WQ)*Q)
  refine RatEq_trans _
    (ratSub
      (ratMul
        (ratSub (ratMul (ratMul w1 w2) (ratMul a1 b2))
          (ratMul (ratMul w1 w2) (ratMul a2 b1)))
        (ratMul a1 b2))
      (ratMul
        (ratSub (ratMul (ratMul w1 w2) (ratMul a1 b2))
          (ratMul (ratMul w1 w2) (ratMul a2 b1)))
        (ratMul a2 b1))) _
    (ratMul_sub_left
      (ratSub (ratMul (ratMul w1 w2) (ratMul a1 b2))
        (ratMul (ratMul w1 w2) (ratMul a2 b1)))
      (ratMul a1 b2) (ratMul a2 b1)) ?_
  -- 第三步: 每个 (WP-WQ)*R right-distrib 成 (WP*R - WQ*R)
  refine ratSub_congr ?_ ?_
  · -- ((WP-WQ)*P) ≃ (WP*P) - (WQ*P) ≃ T2 - E
    refine RatEq_trans _
      (ratSub
        (ratMul (ratMul (ratMul w1 w2) (ratMul a1 b2)) (ratMul a1 b2))
        (ratMul (ratMul (ratMul w1 w2) (ratMul a2 b1)) (ratMul a1 b2))) _
      (ratMul_sub_right (ratMul (ratMul w1 w2) (ratMul a1 b2))
        (ratMul (ratMul w1 w2) (ratMul a2 b1)) (ratMul a1 b2)) ?_
    refine ratSub_congr ?_ ?_
    · -- WP*P = ((w1w2)(a1b2))(a1b2) ≃ mono6 w1 w2 a1 b2 a1 b2 ≃ T2
      refine RatEq_trans _ (mono6 w1 w2 a1 b2 a1 b2) _
        (mul_W_pair_pair w1 w2 a1 b2 a1 b2) ?_
      exact mono6_swap45 w1 w2 a1 b2 a1 b2
    · -- WQ*P = ((w1w2)(a2b1))(a1b2) ≃ mono6 w1 w2 a2 b1 a1 b2 ≃ E
      refine RatEq_trans _ (mono6 w1 w2 a2 b1 a1 b2) _
        (mul_W_pair_pair w1 w2 a2 b1 a1 b2) ?_
      exact wqp_norm w1 w2 a1 a2 b1 b2
  · -- ((WP-WQ)*Q) ≃ (WP*Q) - (WQ*Q) ≃ E - T3c
    refine RatEq_trans _
      (ratSub
        (ratMul (ratMul (ratMul w1 w2) (ratMul a1 b2)) (ratMul a2 b1))
        (ratMul (ratMul (ratMul w1 w2) (ratMul a2 b1)) (ratMul a2 b1))) _
      (ratMul_sub_right (ratMul (ratMul w1 w2) (ratMul a1 b2))
        (ratMul (ratMul w1 w2) (ratMul a2 b1)) (ratMul a2 b1)) ?_
    refine ratSub_congr ?_ ?_
    · -- WP*Q = ((w1w2)(a1b2))(a2b1) ≃ mono6 w1 w2 a1 b2 a2 b1 ≃ E
      refine RatEq_trans _ (mono6 w1 w2 a1 b2 a2 b1) _
        (mul_W_pair_pair w1 w2 a1 b2 a2 b1) ?_
      -- [w1 w2 a1 b2 a2 b1]: swap45 (b2,a2)→[w1 w2 a1 a2 b2 b1], swap56→[w1 w2 a1 a2 b1 b2]
      refine RatEq_trans _ (mono6 w1 w2 a1 a2 b2 b1) _
        (mono6_swap45 w1 w2 a1 b2 a2 b1) ?_
      exact mono6_swap56 w1 w2 a1 a2 b2 b1
    · -- WQ*Q = ((w1w2)(a2b1))(a2b1) ≃ mono6 w1 w2 a2 b1 a2 b1 ≃ T3c
      refine RatEq_trans _ (mono6 w1 w2 a2 b1 a2 b1) _
        (mul_W_pair_pair w1 w2 a2 b1 a2 b1) ?_
      exact mono6_swap45 w1 w2 a2 b1 a2 b1

/-! ## 规范化后的对角/反对角展开

把残项排到规范序: `gXX*gYY ≃ (T1+T2)+(T3c+T4)`, `gXY*gYX ≃ (T1+E)+(E+T4)`。
`T1 = w1 w1 a1 a1 a2 a2`, `T2 = w1 w2 a1 a1 b2 b2`, `T3c = w1 w2 a2 a2 b1 b1`,
`T4 = w2 w2 b1 b1 b2 b2`, `E = w1 w2 a1 a2 b1 b2`。 -/

/-- `gXX*gYY` 归到规范残项 `(T1+T2)+(T3c+T4)`。 -/
private theorem gXXgYY_canon (w1 w2 a1 a2 b1 b2 : RatNum) :
    RatEq (ratMul (twoDriverGXX w1 w2 a1 a2 b1 b2) (twoDriverGYY w1 w2 a1 a2 b1 b2))
      (ratAdd
        (ratAdd (mono6 w1 w1 a1 a1 a2 a2) (mono6 w1 w2 a1 a1 b2 b2))
        (ratAdd (mono6 w1 w2 a2 a2 b1 b1) (mono6 w2 w2 b1 b1 b2 b2))) := by
  refine RatEq_trans _ _ _ (gXXgYY_expand w1 w2 a1 a2 b1 b2) ?_
  -- 只需把第三项 T3raw ≃ T3c, 其余不动。
  exact ratAdd_respects (RatEq_refl _)
    (ratAdd_respects (t3_norm w1 w2 a2 b1) (RatEq_refl _))

/-- `gXY*gYX` 归到规范残项 `(T1+E)+(E+T4)`。 -/
private theorem gXYgYX_canon (w1 w2 a1 a2 b1 b2 : RatNum) :
    RatEq (ratMul (twoDriverGXY w1 w2 a1 a2 b1 b2) (twoDriverGYX w1 w2 a1 a2 b1 b2))
      (ratAdd
        (ratAdd (mono6 w1 w1 a1 a1 a2 a2) (mono6 w1 w2 a1 a2 b1 b2))
        (ratAdd (mono6 w1 w2 a1 a2 b1 b2) (mono6 w2 w2 b1 b1 b2 b2))) := by
  refine RatEq_trans _ _ _ (gXYgYX_expand w1 w2 a1 a2 b1 b2) ?_
  -- S1≃T1, S2raw≃E, S3raw≃E, S4≃T4。
  exact ratAdd_respects
    (ratAdd_respects (s1_norm w1 a1 a2) (s2_norm w1 w2 a1 a2 b1 b2))
    (ratAdd_respects (s3_norm w1 w2 a1 a2 b1 b2) (s4_norm w2 b1 b2))

/-! ## 核心定理

$\det g = w_1 w_2 (\Delta_1 \wedge \Delta_2)^2$。两独立驱动的 backreaction 度规行列式等于
加权 wedge 平方 (Cauchy–Binet)。与单驱动 `backreaction_metric_det_zero` 的退化负结果对照:
两独立驱动 ($\Delta_1 \wedge \Delta_2 \neq 0$) 才可能给出非退化 emergent geometry。 -/

/-- **核心定理**: 两驱动 backreaction 度规的 2×2 行列式等于加权 wedge 平方
$$\det g = g_{xx} g_{yy} - g_{xy} g_{yx} = w_1 w_2\,(a_1 b_2 - a_2 b_1)^2.$$

因此 $\det g \neq 0 \iff w_1 w_2 \neq 0 \wedge \Delta_1 \wedge \Delta_2 \neq 0$ (两驱动线性无关)。
schematic 建设性结论: schematic backreaction 要给非退化 emergent geometry, 至少需 2 个独立
relative-holonomy 驱动 (单驱动必退化, 见 `backreaction_metric_det_zero`)。非物理定理。 -/
theorem two_driver_det_eq_weighted_wedge_sq (w1 w2 a1 a2 b1 b2 : RatNum) :
    RatEq (twoDriverMetricDet w1 w2 a1 a2 b1 b2)
      (ratMul (ratMul (ratMul w1 w2) (wedge a1 a2 b1 b2)) (wedge a1 a2 b1 b2)) := by
  unfold twoDriverMetricDet
  -- metricDet ≃ sub ((T1+T2)+(T3c+T4)) ((T1+E)+(E+T4))
  refine RatEq_trans _
    (ratSub
      (ratAdd
        (ratAdd (mono6 w1 w1 a1 a1 a2 a2) (mono6 w1 w2 a1 a1 b2 b2))
        (ratAdd (mono6 w1 w2 a2 a2 b1 b1) (mono6 w2 w2 b1 b1 b2 b2)))
      (ratAdd
        (ratAdd (mono6 w1 w1 a1 a1 a2 a2) (mono6 w1 w2 a1 a2 b1 b2))
        (ratAdd (mono6 w1 w2 a1 a2 b1 b2) (mono6 w2 w2 b1 b1 b2 b2)))) _
    (ratSub_congr (gXXgYY_canon w1 w2 a1 a2 b1 b2)
      (gXYgYX_canon w1 w2 a1 a2 b1 b2)) ?_
  -- 残项恒等式: t1=T1, t2=T2, t3=T3c, t4=T4, e=E → (T2-E)-(E-T3c)
  refine RatEq_trans _
    (ratSub
      (ratSub (mono6 w1 w2 a1 a1 b2 b2) (mono6 w1 w2 a1 a2 b1 b2))
      (ratSub (mono6 w1 w2 a1 a2 b1 b2) (mono6 w1 w2 a2 a2 b1 b1))) _
    (residual_identity (mono6 w1 w1 a1 a1 a2 a2) (mono6 w1 w2 a1 a1 b2 b2)
      (mono6 w1 w2 a2 a2 b1 b1) (mono6 w2 w2 b1 b1 b2 b2)
      (mono6 w1 w2 a1 a2 b1 b2)) ?_
  -- = RHS (rhs_expand 反向)
  exact RatEq_symm (rhs_expand w1 w2 a1 a2 b1 b2)

end BEDC.Derived.Visions

