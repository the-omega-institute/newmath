import BEDC.Derived.RationalUp.MetricOrder

/-!
# Backreaction metric degeneracy (honest negative result)

诚实的负结果: 在 T² 上对 twisted-holonomy backreaction 做诚实(schematic)对抗推理,
emergent metric 的分量取 rank-1 外积形式

$$g_{\mu\nu} = w_1 w_2 \, \Delta_\mu \Delta_\nu, \qquad \Delta = (\Delta x, \Delta y).$$

这是 2-向量 $\Delta$ (= $\kappa_1 - \kappa_2$ 的差) 与自身的外积, 乘上标量权重 $w_1 w_2$.
外积矩阵的秩恒为 1, 因此 2×2 行列式恒为 0:

$$\det g = g_{xx} g_{yy} - g_{xy} g_{yx}
        = (w_1 w_2)^2 (\Delta x\,\Delta x\,\Delta y\,\Delta y - \Delta x\,\Delta y\,\Delta y\,\Delta x)
        = 0.$$

退化 (det = 0) ⇒ 无逆 ⇒ 无曲率 ⇒ backreaction 产生不了物理几何. 即 twisted-holonomy /
solenoid 结构对生成物理度规**非必要**, 可用 U(1) flat bundle 替换. 这不是失败, 而是一个诚实、
可证伪的负结论: 一个 rank-1 外积永远无法充当非退化的 2D 度规.

**范围声明**: 本文件形式化的是纯代数事实 (rank-1 外积 2×2 行列式为 0). observation / κ / Δ /
权重都是 schematic、非物理的占位量; 这里没有任何物理统一定理, 也不声称物理度规的存在性.
形式化捕获的只是"外积退化"这一代数骨架, 用来记录上述负结论。-/

namespace BEDC.Derived.Visions

open BEDC.Derived.RationalUp

/-! 权重 $w_1, w_2$ 与位移向量分量 $\Delta x, \Delta y$ 都取 BEDC 的 `RatNum`。
这些是 schematic 占位量, 不是物理测量值。 -/

/-- $g_{xx} = w_1 w_2 \,\Delta x\,\Delta x$ (左结合乘积)。签名统一取四参, `dy` 在此分量不出现。 -/
def gXX (w1 w2 dx _dy : RatNum) : RatNum :=
  ratMul (ratMul (ratMul w1 w2) dx) dx

/-- $g_{xy} = w_1 w_2 \,\Delta x\,\Delta y$。 -/
def gXY (w1 w2 dx dy : RatNum) : RatNum :=
  ratMul (ratMul (ratMul w1 w2) dx) dy

/-- $g_{yx} = w_1 w_2 \,\Delta y\,\Delta x$。 -/
def gYX (w1 w2 dx dy : RatNum) : RatNum :=
  ratMul (ratMul (ratMul w1 w2) dy) dx

/-- $g_{yy} = w_1 w_2 \,\Delta y\,\Delta y$。签名统一取四参, `dx` 在此分量不出现。 -/
def gYY (w1 w2 _dx dy : RatNum) : RatNum :=
  ratMul (ratMul (ratMul w1 w2) dy) dy

/-- 2×2 行列式 $\det g = g_{xx} g_{yy} - g_{xy} g_{yx}$。 -/
def metricDet (w1 w2 dx dy : RatNum) : RatNum :=
  ratSub
    (ratMul (gXX w1 w2 dx dy) (gYY w1 w2 dx dy))
    (ratMul (gXY w1 w2 dx dy) (gYX w1 w2 dx dy))

/-! ## 乘法重排辅助引理

以下引理只用 `ratMul_comm` / `ratMul_assoc` / respects / trans / symm, 是纯代数, 无 axiom。 -/

/-- 右侧结合律的反方向: `RatEq (a * (b * c)) ((a * b) * c)`。 -/
private theorem ratMul_assoc_symm (a b c : RatNum) :
    RatEq (ratMul a (ratMul b c)) (ratMul (ratMul a b) c) :=
  RatEq_symm (ratMul_assoc a b c)

/-- 左内交换: `RatEq (a * (b * c)) (b * (a * c))`。 -/
private theorem ratMul_left_comm (a b c : RatNum) :
    RatEq (ratMul a (ratMul b c)) (ratMul b (ratMul a c)) := by
  refine RatEq_trans (ratMul a (ratMul b c))
    (ratMul (ratMul a b) c) (ratMul b (ratMul a c))
    (ratMul_assoc_symm a b c) ?_
  refine RatEq_trans (ratMul (ratMul a b) c)
    (ratMul (ratMul b a) c) (ratMul b (ratMul a c))
    (ratMul_respects_left (ratMul_comm a b)) ?_
  exact ratMul_assoc b a c

/-- 右内交换: `RatEq ((a * b) * c) ((a * c) * b)`。 -/
private theorem ratMul_right_comm (a b c : RatNum) :
    RatEq (ratMul (ratMul a b) c) (ratMul (ratMul a c) b) := by
  refine RatEq_trans (ratMul (ratMul a b) c)
    (ratMul a (ratMul b c)) (ratMul (ratMul a c) b)
    (ratMul_assoc a b c) ?_
  refine RatEq_trans (ratMul a (ratMul b c))
    (ratMul a (ratMul c b)) (ratMul (ratMul a c) b)
    (ratMul_respects_right (ratMul_comm b c)) ?_
  exact ratMul_assoc_symm a c b

/-! ## 核心: 两个 2×2 对角/反对角乘积相等

设 $W = (w_1 w_2)$。展开后

$$g_{xx} g_{yy} = (((W\,\Delta x)\,\Delta x)) \cdot (((W\,\Delta y)\,\Delta y)),$$
$$g_{xy} g_{yx} = (((W\,\Delta x)\,\Delta y)) \cdot (((W\,\Delta y)\,\Delta x)).$$

两者都是因子多重集 $\{W, W, \Delta x, \Delta x, \Delta y, \Delta y\}$ 的乘积, 仅排列不同, 故相等。 -/

/-- 完全左结合的 6-因子规范形 $((((W_a \cdot W_b) \cdot p) \cdot q) \cdot r) \cdot s$。 -/
private def prod6 (wa wb p q r s : RatNum) : RatNum :=
  ratMul (ratMul (ratMul (ratMul (ratMul wa wb) p) q) r) s

/-- `g_xx * g_yy` 归约到规范形 `prod6 W W dx dx dy dy`, 其中 `W = w1*w2`。 -/
private theorem gXXgYY_norm (w1 w2 dx dy : RatNum) :
    RatEq (ratMul (gXX w1 w2 dx dy) (gYY w1 w2 dx dy))
      (prod6 (ratMul w1 w2) (ratMul w1 w2) dx dx dy dy) := by
  unfold gXX gYY prod6
  -- 记 W := ratMul w1 w2
  -- 展平: (((W*dx)*dx) * ((W*dy)*dy)) ≃ 完全左结合 [W dx dx W dy dy]
  refine RatEq_trans _
    (ratMul (ratMul (ratMul (ratMul (ratMul (ratMul w1 w2) dx) dx) (ratMul w1 w2)) dy) dy)
    _ ?_ ?_
  · -- A * ((W*dy)*dy) ≃ ((A*(W*dy))*dy) ≃ (((A*W)*dy)*dy)
    refine RatEq_trans _
      (ratMul (ratMul (ratMul (ratMul (ratMul w1 w2) dx) dx) (ratMul (ratMul w1 w2) dy)) dy)
      _ ?_ ?_
    · exact ratMul_assoc_symm (ratMul (ratMul (ratMul w1 w2) dx) dx)
        (ratMul (ratMul w1 w2) dy) dy
    · refine ratMul_respects_left ?_
      exact ratMul_assoc_symm (ratMul (ratMul (ratMul w1 w2) dx) dx)
        (ratMul w1 w2) dy
  · -- 现在: 左结合链 [W dx dx W dy dy] → 目标 [W W dx dx dy dy]
    -- swap pos3,4 (dx,W): [W dx W dx dy dy]
    refine RatEq_trans _
      (ratMul (ratMul (ratMul (ratMul (ratMul (ratMul w1 w2) dx) (ratMul w1 w2)) dx) dy) dy)
      _ ?_ ?_
    · refine ratMul_respects_left ?_
      refine ratMul_respects_left ?_
      exact ratMul_right_comm (ratMul (ratMul w1 w2) dx) dx (ratMul w1 w2)
    -- swap pos2,3 (dx,W): [W W dx dx dy dy]
    refine ratMul_respects_left ?_
    refine ratMul_respects_left ?_
    refine ratMul_respects_left ?_
    exact ratMul_right_comm (ratMul w1 w2) dx (ratMul w1 w2)

/-- `g_xy * g_yx` 归约到同一规范形 `prod6 W W dx dx dy dy`。

先把 `ratMul A B` (A = (W*dx)*dy, B = (W*dy)*dx) 展平成完全左结合的 6-因子链
`[W, dx, dy, W, dy, dx]`, 再用相邻换位 (`ratMul_right_comm` + `ratMul_respects_left`)
把它冒泡排序成 `[W, W, dx, dx, dy, dy]`。 -/
private theorem gXYgYX_norm (w1 w2 dx dy : RatNum) :
    RatEq (ratMul (gXY w1 w2 dx dy) (gYX w1 w2 dx dy))
      (prod6 (ratMul w1 w2) (ratMul w1 w2) dx dx dy dy) := by
  unfold gXY gYX prod6
  -- 记 W := ratMul w1 w2
  -- 展平: (((W*dx)*dy) * ((W*dy)*dx)) ≃ 完全左结合 [W dx dy W dy dx]
  refine RatEq_trans _
    (ratMul (ratMul (ratMul (ratMul (ratMul (ratMul w1 w2) dx) dy) (ratMul w1 w2)) dy) dx)
    _ ?_ ?_
  · -- A * ((W*dy)*dx) ≃ ((A*(W*dy))*dx) ≃ (((A*W)*dy)*dx)
    refine RatEq_trans _
      (ratMul (ratMul (ratMul (ratMul (ratMul w1 w2) dx) dy) (ratMul (ratMul w1 w2) dy)) dx)
      _ ?_ ?_
    · exact ratMul_assoc_symm (ratMul (ratMul (ratMul w1 w2) dx) dy)
        (ratMul (ratMul w1 w2) dy) dx
    · refine ratMul_respects_left ?_
      exact ratMul_assoc_symm (ratMul (ratMul (ratMul w1 w2) dx) dy)
        (ratMul w1 w2) dy
  · -- 现在: 左结合链 [W dx dy W dy dx] → 目标 [W W dx dx dy dy]
    -- 冒泡换位序列 (对相邻高位因子做 right_comm, 用 respects_left 下沉到子链):
    -- [W dx dy W dy dx]
    --  swap pos3,4 (dy,W): [W dx W dy dy dx]
    refine RatEq_trans _
      (ratMul (ratMul (ratMul (ratMul (ratMul (ratMul w1 w2) dx) (ratMul w1 w2)) dy) dy) dx)
      _ ?_ ?_
    · refine ratMul_respects_left ?_
      refine ratMul_respects_left ?_
      exact ratMul_right_comm (ratMul (ratMul w1 w2) dx) dy (ratMul w1 w2)
    -- [W dx W dy dy dx] swap pos2,3 (dx,W): [W W dx dy dy dx]
    refine RatEq_trans _
      (ratMul (ratMul (ratMul (ratMul (ratMul (ratMul w1 w2) (ratMul w1 w2)) dx) dy) dy) dx)
      _ ?_ ?_
    · refine ratMul_respects_left ?_
      refine ratMul_respects_left ?_
      refine ratMul_respects_left ?_
      exact ratMul_right_comm (ratMul w1 w2) dx (ratMul w1 w2)
    -- [W W dx dy dy dx] swap pos5,6 (dy,dx): [W W dx dy dx dy]
    refine RatEq_trans _
      (ratMul (ratMul (ratMul (ratMul (ratMul (ratMul w1 w2) (ratMul w1 w2)) dx) dy) dx) dy)
      _ ?_ ?_
    · exact ratMul_right_comm
        (ratMul (ratMul (ratMul (ratMul w1 w2) (ratMul w1 w2)) dx) dy) dy dx
    -- [W W dx dy dx dy] swap pos4,5 (dy,dx): [W W dx dx dy dy]
    refine ratMul_respects_left ?_
    exact ratMul_right_comm
      (ratMul (ratMul (ratMul w1 w2) (ratMul w1 w2)) dx) dy dx

/-- 对角乘积等于反对角乘积: $g_{xx} g_{yy} = g_{xy} g_{yx}$。 -/
theorem backreaction_offdiag_eq_diag (w1 w2 dx dy : RatNum) :
    RatEq (ratMul (gXX w1 w2 dx dy) (gYY w1 w2 dx dy))
      (ratMul (gXY w1 w2 dx dy) (gYX w1 w2 dx dy)) :=
  RatEq_trans _ (prod6 (ratMul w1 w2) (ratMul w1 w2) dx dx dy dy) _
    (gXXgYY_norm w1 w2 dx dy)
    (RatEq_symm (gXYgYX_norm w1 w2 dx dy))

/-- **核心定理**: rank-1 backreaction 度规的 2×2 行列式恒为零。

$$\det g = g_{xx} g_{yy} - g_{xy} g_{yx} = 0.$$

这是 rank-1 外积矩阵退化的形式化。诚实负结论: 退化 ⇒ 无逆 ⇒ 无曲率 ⇒ backreaction /
twisted-holonomy / solenoid 生成不了物理几何 (solenoid 非必要)。schematic, 非物理定理。 -/
theorem backreaction_metric_det_zero (w1 w2 dx dy : RatNum) :
    RatEq (metricDet w1 w2 dx dy) ratZero := by
  unfold metricDet
  exact (ratSub_zero_iff
      (ratMul (gXX w1 w2 dx dy) (gYY w1 w2 dx dy))
      (ratMul (gXY w1 w2 dx dy) (gYX w1 w2 dx dy))).mpr
    (backreaction_offdiag_eq_diag w1 w2 dx dy)

end BEDC.Derived.Visions
