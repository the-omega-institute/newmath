import Mathlib.Data.Nat.Fib.Zeckendorf

/-!
# ch5 Zeckendorf 尺度(定理 5.3)

文档定理 5.3:每个 `n ≥ 0` 唯一表示为无相邻 1 的 Fibonacci 和。这里直接落到 mathlib 的
`Nat.zeckendorfEquiv`,把"存在 + 唯一"打包成一个 `ℕ ≃ AxisWord` 等价。

`AxisWord` 是单素数轴上的 Zeckendorf 词(Fibonacci 指标列,满足无相邻条件
`List.IsZeckendorfRep`)。文档位指标 `k ≥ 1` 对应 mathlib Fibonacci 指标,解码用
`(l.map Nat.fib).sum`——这正是 `Nat.zeckendorfEquiv` 的逆向取值。
-/

namespace UnifiedTheory

/-- 单素数轴上的 Zeckendorf 词:满足无相邻条件的 Fibonacci 指标列。 -/
abbrev AxisWord := {l : List ℕ // l.IsZeckendorfRep}

namespace AxisWord

/-- 解码:Zeckendorf 词各指标处 Fibonacci 数之和(文档 §5 的读数)。 -/
def decode (w : AxisWord) : ℕ := (w.1.map Nat.fib).sum

/-- 编码:自然数到其唯一 Zeckendorf 词(mathlib 的贪心 `zeckendorf`)。 -/
def encode (n : ℕ) : AxisWord := Nat.zeckendorfEquiv n

/-- 定理 5.3(Zeckendorf 存在 + 唯一)= `ℕ ≃ AxisWord` 等价。 -/
def equivNat : ℕ ≃ AxisWord := Nat.zeckendorfEquiv

@[simp] theorem decode_encode (n : ℕ) : decode (encode n) = n :=
  Nat.zeckendorfEquiv.symm_apply_apply n

@[simp] theorem encode_decode (w : AxisWord) : encode (decode w) = w :=
  Nat.zeckendorfEquiv.apply_symm_apply w

end AxisWord

end UnifiedTheory
