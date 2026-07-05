import UnifiedTheory.PZG.Decode

/-!
# ch5 归一化 = 乘法(定理 5.6)

文档定理 5.6:位表逐位相加后归一化 = 乘法,即 `𝖣(𝖭(z+w)) = 𝖣(z)·𝖣(w)`。这里把归一化取为
唯一 canonical 再编码 `normAdd z w := encode (decode z * decode w)`(归一化本就是把指数和重新
Zeckendorf 化,不需 carry 算法;carry 终止 5.7 是另账)。指数形式 `vp_decode_normAdd` 复用
定理 4.4 的 `v_p` 加性,显式呈现"乘法是指数生成的影子"。
-/

namespace UnifiedTheory

namespace PZGTable

/-- 归一化加法(定理 5.6):两位表的 PZG 加法后归一化 = 乘积的唯一 canonical 再编码。 -/
noncomputable def normAdd (z w : PZGTable) : PZGTable := encode (decode z * decode w)

/-- 定理 5.6:归一化后解码等于乘积。 -/
@[simp] theorem decode_normAdd (z w : PZGTable) :
    decode (normAdd z w) = decode z * decode w := by
  simp [normAdd]

/-- 定理 5.6 的指数形式:归一化加法在每素轴上指数相加(定理 4.4 的 `v_p` 加性)。 -/
theorem vp_decode_normAdd (p : ℕ) (z w : PZGTable) :
    vp p (decode (normAdd z w)) = vp p (decode z) + vp p (decode w) := by
  rw [decode_normAdd, vp_mul]

end PZGTable

end UnifiedTheory
