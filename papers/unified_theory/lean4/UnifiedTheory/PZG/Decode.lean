import UnifiedTheory.PZG.Carrier

/-!
# ch5 PZG 解码双射(定理 5.5)

`𝖣 : PZGTable ≃ ℕ+`:逐轴 Zeckendorf 解码(`equivPrimeExp`)与素数唯一分解
(`PrimeExp.equivPNat`)合成。这就是文档定理 5.5——PZG 位表与正自然数一一对应。
-/

namespace UnifiedTheory

namespace PZGTable

/-- 定理 5.5(PZG 双射):`𝖣 : PZGTable ≃ ℕ+`。 -/
noncomputable def decode : PZGTable ≃ ℕ+ :=
  equivPrimeExp.trans PrimeExp.equivPNat.symm

/-- 编码 `𝖹`:解码之逆。 -/
noncomputable def encode : ℕ+ ≃ PZGTable := decode.symm

@[simp] theorem decode_encode (n : ℕ+) : decode (encode n) = n :=
  decode.apply_symm_apply n

@[simp] theorem encode_decode (z : PZGTable) : encode (decode z) = z :=
  decode.symm_apply_apply z

end PZGTable

end UnifiedTheory
