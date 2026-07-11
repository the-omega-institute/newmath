import UnifiedTheory.Golden.CoordinateAxes

/-!
GCS L2 depth 度量 `depth(x)=(deg_×,|Z|,‖G‖)` 之乘性轴公理:
`×φ` 梯律给出自相似增量 `degMul(φx)=degMul x+1`, 并记录绝对膨胀面的单调性。
几何轴 `‖G‖` 圆距全度量与三轴联合分离留 open, 接三距心脏与实分析。
-/

namespace UnifiedTheory
namespace PhiInt

/-- Multiplying by `φ` raises the multiplicative degree by one. -/
theorem degMul_phi_mul {x : PhiInt} (hx : toRealPlus x ≠ 0) :
    degMul (phi * x) = degMul x + 1 := by
  unfold degMul
  have hphi_ne : Real.goldenRatio ≠ 0 := Real.goldenRatio_pos.ne'
  have hlog :
      Real.logb Real.goldenRatio |toRealPlus (phi * x)|
        = (1 : ℝ) + Real.logb Real.goldenRatio |toRealPlus x| := by
    calc
      Real.logb Real.goldenRatio |toRealPlus (phi * x)|
          = Real.logb Real.goldenRatio |Real.goldenRatio * toRealPlus x| := by
              rw [toRealPlus_mul, toRealPlus_phi]
      _ = Real.logb Real.goldenRatio (Real.goldenRatio * |toRealPlus x|) := by
              rw [abs_mul, abs_of_pos Real.goldenRatio_pos]
      _ = Real.logb Real.goldenRatio Real.goldenRatio
            + Real.logb Real.goldenRatio |toRealPlus x| := by
              rw [Real.logb_mul hphi_ne (abs_ne_zero.mpr hx)]
      _ = (1 : ℝ) + Real.logb Real.goldenRatio |toRealPlus x| := by
              rw [Real.logb_self_eq_one Real.one_lt_goldenRatio]
  rw [hlog]
  rw [add_comm (1 : ℝ), Int.floor_add_one]

/-- The multiplicative degree is monotone in the absolute expanding embedding. -/
theorem degMul_mono {x y : PhiInt} (hx : toRealPlus x ≠ 0)
    (h : |toRealPlus x| ≤ |toRealPlus y|) : degMul x ≤ degMul y := by
  unfold degMul
  exact Int.floor_le_floor
    (Real.logb_le_logb_of_le Real.one_lt_goldenRatio (abs_pos.mpr hx) h)

/-- A Fibonacci number has a one-digit Zeckendorf word at its own index. -/
theorem zeckDigits_fib_length {k : ℕ} (hk : 2 ≤ k) :
    (zeckDigits (Nat.fib k)).1.length = 1 := by
  unfold zeckDigits AxisWord.encode
  change (Nat.zeckendorf (Nat.fib k)).length = 1
  have hrep : List.IsZeckendorfRep [k] := by
    simp [List.IsZeckendorfRep, hk]
  have hsum : ([k].map Nat.fib).sum = Nat.fib k := by
    simp
  rw [← hsum, Nat.zeckendorf_sum_fib hrep]
  simp

end PhiInt
end UnifiedTheory
