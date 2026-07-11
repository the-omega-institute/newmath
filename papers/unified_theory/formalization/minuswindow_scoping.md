# `MinusWindow` scoping

本文只做源码与接口调研,并给出 `MinusWindow` 的证明骨架。没有运行 `lake build`。探针只使用
`lake env lean --stdin` 中的 `#print`、`#check`、`#eval`,以及 `rg` / `sed` 阅读本地源码。

`loogle` 在当前 shell 中不可用,所以相关检索以本地 `rg` 和 Lean `#check` 替代。

## 1. mathlib 的 Zeckendorf 形状

核心文件:

```text
papers/unified_theory/lean4/.lake/packages/mathlib/Mathlib/Data/Nat/Fib/Zeckendorf.lean
```

`#print List.IsZeckendorfRep` 给出的确切定义是:

```lean
def List.IsZeckendorfRep : List Nat -> Prop :=
fun l => List.IsChain (fun a b => b + 2 <= a) (l ++ [0])
```

因此 Lean 中的列表按从左到右读取时是**指标递减**的:

```text
[a0, a1, a2, ...]  satisfies  a1 + 2 <= a0, a2 + 2 <= a1, ...
```

尾部追加的 `[0]` 强制最后一个真实指标 `i` 满足 `0 + 2 <= i`,即所有出现的指标都至少为 `2`。空表合法。mathlib 文件头注释里说 "increasing sequence",但精确定义和 `#eval` 都表明实际 `List` 的头部是最大指标;如果需要升序处理,应显式使用 `reverse`。

示例探针:

```lean
#eval Nat.zeckendorf 0   -- []
#eval Nat.zeckendorf 1   -- [2]
#eval Nat.zeckendorf 2   -- [3]
#eval Nat.zeckendorf 3   -- [4]
#eval Nat.zeckendorf 4   -- [4, 2]
#eval Nat.zeckendorf 5   -- [5]
#eval Nat.zeckendorf 6   -- [5, 2]
#eval Nat.zeckendorf 7   -- [5, 3]
#eval Nat.zeckendorf 8   -- [6]
#eval Nat.zeckendorf 9   -- [6, 2]
#eval Nat.zeckendorf 10  -- [6, 3]
```

这也确认了 Fibonacci 指标约定是 mathlib 的 `Nat.fib 0 = 0`, `Nat.fib 1 = 1`, `Nat.fib 2 = 1`, `Nat.fib 3 = 2`,等等;Zeckendorf 表示避开 `0` 与 `1`,从 `2` 起用。

`UnifiedTheory.AxisWord.encode n` 当前定义为:

```lean
def AxisWord.encode (n : Nat) : AxisWord := Nat.zeckendorfEquiv n
```

所以:

```lean
(AxisWord.encode n).1 = Nat.zeckendorf n
(AxisWord.encode n).2 = Nat.isZeckendorfRep_zeckendorf n
```

## 2. 可直接引用的 mathlib 声明

Zeckendorf 侧:

| 声明 | 探针签名 / 作用 |
|---|---|
| `List.IsZeckendorfRep` | `(l : List Nat) : Prop`,定义为 `(l ++ [0]).IsChain (fun a b => b + 2 <= a)` |
| `List.IsZeckendorfRep_nil` | `[].IsZeckendorfRep` |
| `List.IsZeckendorfRep.sum_fib_lt` | `l.IsZeckendorfRep -> (forall a in (l ++ [0]).head?, a < n) -> (l.map Nat.fib).sum < Nat.fib n` |
| `Nat.greatestFib` | 贪心步:最大 `k` 使 `Nat.fib k <= n` |
| `Nat.fib_greatestFib_le` | `Nat.fib n.greatestFib <= n` |
| `Nat.greatestFib_mono` | `Monotone Nat.greatestFib` |
| `Nat.le_greatestFib` | `m <= n.greatestFib <-> Nat.fib m <= n` |
| `Nat.greatestFib_lt` | `m.greatestFib < n <-> m < Nat.fib n` |
| `Nat.lt_fib_greatestFib_add_one` | `n < Nat.fib (n.greatestFib + 1)` |
| `Nat.greatestFib_fib` | `n != 1 -> (Nat.fib n).greatestFib = n` |
| `Nat.greatestFib_eq_zero` | `n.greatestFib = 0 <-> n = 0` |
| `Nat.greatestFib_pos` | `0 < n.greatestFib <-> 0 < n` |
| `Nat.greatestFib_sub_fib_greatestFib_le_greatestFib` | 非零余数的下一贪心指标 `<= greatestFib n - 2` |
| `Nat.zeckendorf` | `Nat -> List Nat` |
| `Nat.zeckendorf_zero` | `Nat.zeckendorf 0 = []` |
| `Nat.zeckendorf_succ` | 正数递归方程,头为 `greatestFib` |
| `Nat.zeckendorf_of_pos` | `0 < n -> n.zeckendorf = n.greatestFib :: ...` |
| `Nat.isZeckendorfRep_zeckendorf` | `n.zeckendorf.IsZeckendorfRep` |
| `Nat.zeckendorf_sum_fib` | 合法表经 decode 再 encode 回到自身 |
| `Nat.sum_zeckendorf_fib` | `(n.zeckendorf.map Nat.fib).sum = n` |
| `Nat.zeckendorfEquiv` | `Nat ≃ {l // l.IsZeckendorfRep}` |

`List.IsChain` / `Pairwise` 侧:

| 声明 | 用途 |
|---|---|
| `List.isChain_iff_pairwise` | 在有 `Trans R R R` 实例时把 chain 转为 pairwise |
| `List.pairwise_cons` | 拆 `Pairwise R (a :: l)` |
| `List.IsChain.cons` | 构造 `IsChain R (x :: l)` |
| `List.isChain_cons` | 析构 / 构造 cons chain |
| `List.IsChain.tail` | 从 chain 取 tail |
| `List.IsChain.rel_head` | 从 `IsChain R (x :: y :: l)` 得 `R x y` |
| `List.IsChain.rel_head?` | 从 head 与 `head? tail` 得关系 |
| `List.IsChain.rel_cons` | 在有传递性时,头与任意 tail 元素有关系 |
| `List.IsChain.left_of_append` / `right_of_append` | 从 append chain 取左右部分 |
| `List.Pairwise.nodup` | pairwise 的不可自反关系推出 `Nodup` |
| `List.sortedGE_iff_isChain` | 如需要转为 `SortedGE` |

注意: mathlib 的 Zeckendorf 文件里有一个 local `IsTrans` 实例:

```lean
local instance : IsTrans Nat (fun a b => b + 2 <= a) := ...
```

这个实例是 local 的。若在项目文件中使用 `List.isChain_iff_pairwise` 或 `List.IsChain.rel_cons`,建议在证明块内显式放一个:

```lean
haveI : Trans (fun a b : Nat => b + 2 <= a) (fun a b => b + 2 <= a)
    (fun a b => b + 2 <= a) := by
  constructor
  intro a b c hba hcb
  omega
```

或直接对 list 做 induction,绕开全局 typeclass 搜索。

## 3. `AxisWord` 中指标的精确结构

对任意 `w : AxisWord`,令 `l := w.1`。由 `w.2 : l.IsZeckendorfRep` 可得到:

```lean
-- 方向:列表头部大,尾部小。
lemma zeckendorf_adjacent_gap
    {l : List Nat} (hl : l.IsZeckendorfRep) {j : Nat}
    (hj : j + 1 < l.length) :
    l[j + 1] + 2 <= l[j] := ...

-- 最小指标:
lemma zeckendorf_two_le_of_mem
    {l : List Nat} (hl : l.IsZeckendorfRep) {i : Nat}
    (hi : i ∈ l) : 2 <= i := ...

-- 无重复:
lemma zeckendorf_nodup
    {l : List Nat} (hl : l.IsZeckendorfRep) : l.Nodup := ...

-- 单调性:
lemma zeckendorf_sorted_desc
    {l : List Nat} (hl : l.IsZeckendorfRep) :
    l.Sorted (fun a b => b <= a) := ...
```

证明策略:

- `adjacent_gap`: 展开 `List.IsZeckendorfRep`,对 `(l ++ [0]).IsChain` 用 `List.isChain_iff_get` 或 `List.IsChain.rel_head`。
- `two_le_of_mem`: 对 `l` induction;或用 pairwise 取任意元素与最终追加的 `0` 的关系。
- `nodup`: 从 `b + 2 <= a` 推出 `a != b`,再用 `Pairwise.nodup`;或直接从 adjacent gap induction。
- `sorted_desc`: 用 `List.IsChain.imp` 把 `b + 2 <= a` 降为 `b <= a`,再接 `List.sortedGE_iff_isChain`。

`MinusWindow` 的几何估计实际上只需要:

1. 每个指标 `i` 满足 `2 <= i`;
2. 列表 `Nodup`;
3. 指标是有限表。

完整 gap `>= 2` 是 mathlib 合法性的真实结构,也是推出 `Nodup` 的来源。

## 4. 黄金共轭侧的可用接口

mathlib 中已存在:

| 声明 | 签名 |
|---|---|
| `Real.goldenRatio` | `Real` |
| `Real.goldenConj` | `Real` |
| `Real.inv_goldenRatio` | `Real.goldenRatio⁻¹ = -Real.goldenConj` |
| `Real.inv_goldenConj` | `Real.goldenConj⁻¹ = -Real.goldenRatio` |
| `Real.goldenRatio_mul_goldenConj` | `Real.goldenRatio * Real.goldenConj = -1` |
| `Real.goldenConj_mul_goldenRatio` | `Real.goldenConj * Real.goldenRatio = -1` |
| `Real.goldenRatio_add_goldenConj` | `Real.goldenRatio + Real.goldenConj = 1` |
| `Real.one_sub_goldenConj` | `1 - Real.goldenRatio = Real.goldenConj` |
| `Real.one_sub_goldenRatio` | `1 - Real.goldenConj = Real.goldenRatio` |
| `Real.goldenRatio_sub_goldenConj` | `Real.goldenRatio - Real.goldenConj = sqrt 5` |
| `Real.goldenRatio_sq` | `Real.goldenRatio ^ 2 = Real.goldenRatio + 1` |
| `Real.goldenConj_sq` | `Real.goldenConj ^ 2 = Real.goldenConj + 1` |
| `Real.goldenRatio_pos` | `0 < Real.goldenRatio` |
| `Real.goldenRatio_ne_zero` | `Real.goldenRatio != 0` |
| `Real.one_lt_goldenRatio` | `1 < Real.goldenRatio` |
| `Real.goldenRatio_lt_two` | `Real.goldenRatio < 2` |
| `Real.goldenConj_neg` | `Real.goldenConj < 0` |
| `Real.goldenConj_ne_zero` | `Real.goldenConj != 0` |
| `Real.neg_one_lt_goldenConj` | `-1 < Real.goldenConj` |
| `Real.coe_fib_eq` | Binet 公式 |
| `Real.fib_succ_sub_goldenRatio_mul_fib` | `Nat.fib (n+1) - phi * Nat.fib n = psi ^ n` |
| `Real.goldenConj_mul_fib_succ_add_fib` | `psi * Nat.fib (n+1) + Nat.fib n = psi ^ (n+1)` |

未找到直接可用的:

```lean
Real.abs_goldenConj
Real.goldenConj_abs
```

但可由 `Real.goldenConj_neg`, `Real.neg_one_lt_goldenConj`, `Real.inv_goldenRatio` 自建:

```lean
lemma goldenConj_eq_neg_inv :
    Real.goldenConj = - Real.goldenRatio⁻¹ := by
  linarith [Real.inv_goldenRatio]

lemma abs_goldenConj_eq_inv :
    |Real.goldenConj| = Real.goldenRatio⁻¹ := by
  rw [abs_of_neg Real.goldenConj_neg]
  linarith [Real.inv_goldenRatio]

lemma abs_goldenConj_lt_one :
    |Real.goldenConj| < 1 := by
  rw [abs_goldenConj_eq_inv]
  exact inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
```

## 5. `betaMinusReal` 要先化为 `sum psi^i`

当前项目已有:

```lean
def AxisWord.betaPhi (w : AxisWord) : PhiInt :=
  (w.1.map PhiInt.phiPow).foldr (· + ·) 0

noncomputable def AxisWord.betaMinusReal (w : AxisWord) : Real :=
  (betaPhi w).toRealMinus
```

已有 `PhiInt.toRealPlus_phiPow`,但还没有 `toRealMinus_phiPow`。证明窗口前建议先补以下局部引理:

```lean
namespace UnifiedTheory.PhiInt

@[simp] theorem toRealMinus_phi :
    toRealMinus phi = Real.goldenConj := by
  simp [toRealMinus, phi]

theorem toRealMinus_mul (x y : PhiInt) :
    toRealMinus (x * y) = toRealMinus x * toRealMinus y := by
  simp only [toRealMinus, mul_a, mul_b]
  push_cast
  linear_combination (-(x.b : Real) * (y.b : Real)) * Real.goldenConj_sq

@[simp] theorem toRealMinus_phiPow (n : Nat) :
    toRealMinus (phiPow n) = Real.goldenConj ^ n := by
  induction n with
  | zero => simp [phiPow, toRealMinus]
  | succ k ih =>
      rw [phiPow, toRealMinus_mul, ih, toRealMinus_phi, pow_succ]

end UnifiedTheory.PhiInt
```

然后给 `AxisWord` 一个读数化简:

```lean
namespace UnifiedTheory.AxisWord

theorem betaMinusReal_eq_sum (w : AxisWord) :
    betaMinusReal w = (w.1.map fun i => Real.goldenConj ^ i).sum := by
  unfold betaMinusReal betaPhi
  induction w.1 with
  | nil => simp [PhiInt.toRealMinus]
  | cons i l ih =>
      simp [PhiInt.toRealMinus_add, PhiInt.toRealMinus_phiPow, ih]

end UnifiedTheory.AxisWord
```

风险很低;主要是 `foldr` 与 `List.sum` 的 simp 方向可能需要手动 `rw [List.map_map]` 或改成单独的 `foldr_toRealMinus` 引理。

## 6. 数学论证:有限非相邻指标的几何窗口

记:

```text
phi = Real.goldenRatio
psi = Real.goldenConj
r   = psi^2 = 1 / phi^2
```

由 `psi = -1/phi`,有:

```text
0 < r < 1
1 - r = 1 / phi
sum_{k >= 0} r^(k+1) = r / (1-r) = 1 / phi
psi * sum_{k >= 0} r^(k+1) = -1 / phi^2
```

由于 Zeckendorf 指标从 `2` 起:

- 偶指标正项从 `2` 起: `psi^(2k+2) = r^(k+1)`;
- 奇指标负项从 `3` 起: `psi^(2k+3) = psi * r^(k+1)`。

对合法有限列表 `l`:

```text
sum_{i in l} psi^i
  <= sum_{i in l, i even} psi^i
  <  sum_{k >= 0} psi^(2k+2)
  =  1 / phi
```

第一步使用奇项非正;第二步使用 `Nodup` 和 `2 <= i`,说明偶指标项是 `{2,4,6,...}` 的有限真子和。严格性来自几何级数有无限正尾。

下界:

```text
sum_{i in l} psi^i
  >= sum_{i in l, i odd} psi^i
  >  sum_{k >= 0} psi^(2k+3)
  = -1 / phi^2
```

第一步使用偶项非负;第二步可把奇项写成 `psi * r^(k+1)`,先证明有限正子和严格小于全正几何和,再乘以 `psi < 0` 反向。

端点常数核对:

```text
sum_{k >= 0} psi^(2k+2)
  = sum_{k >= 0} r^(k+1)
  = r / (1-r)
  = (1/phi^2) / (1/phi)
  = 1/phi

sum_{k >= 0} psi^(2k+3)
  = psi * sum_{k >= 0} r^(k+1)
  = (-1/phi) * (1/phi)
  = -1/phi^2
```

## 7. Lean 证明骨架

### 7.1 黄金常数与符号

自建:

```lean
lemma goldenConj_eq_neg_inv :
    Real.goldenConj = - Real.goldenRatio⁻¹ := ...

lemma goldenConj_sq_eq_inv_sq :
    Real.goldenConj ^ 2 = Real.goldenRatio⁻¹ ^ 2 := ...

lemma one_sub_goldenConj_sq :
    1 - Real.goldenConj ^ 2 = Real.goldenRatio⁻¹ := ...

lemma goldenConj_sq_pos :
    0 < Real.goldenConj ^ 2 := ...

lemma goldenConj_sq_lt_one :
    Real.goldenConj ^ 2 < 1 := ...
```

策略: `goldenConj_eq_neg_inv`, `Real.one_lt_goldenRatio`, `Real.goldenRatio_pos`, `Real.goldenRatio_sq`;常数等式用 `field_simp` 或 `linear_combination`。

现成:

- `Real.inv_goldenRatio`
- `Real.goldenConj_neg`
- `Real.neg_one_lt_goldenConj`
- `Real.goldenRatio_sq`
- `Real.goldenRatio_pos`
- `Real.one_lt_goldenRatio`

### 7.2 幂的奇偶符号

自建:

```lean
lemma goldenConj_pow_nonneg_of_even {i : Nat} (hi : Even i) :
    0 <= Real.goldenConj ^ i := by
  simpa using hi.pow_nonneg Real.goldenConj

lemma goldenConj_pow_nonpos_of_odd {i : Nat} (hi : Odd i) :
    Real.goldenConj ^ i <= 0 := by
  exact (le_of_lt ((Odd.pow_neg_iff hi).2 Real.goldenConj_neg))
```

现成:

- root predicate `Even`, `Odd`
- `Nat.even_or_odd`
- `Even.pow_nonneg`
- `Odd.pow_neg_iff`
- `Even.neg_pow`
- `Odd.neg_pow`

注意:没有 `Nat.Even` / `Nat.Odd`;探针确认这两个名字不存在。

### 7.3 指标参数化

自建:

```lean
lemma even_index_from_two {i : Nat} (h2 : 2 <= i) (he : Even i) :
    exists k : Nat, i = 2 * k + 2 := ...

lemma odd_index_from_two {i : Nat} (h2 : 2 <= i) (ho : Odd i) :
    exists k : Nat, i = 2 * k + 3 := ...
```

策略:拆 `Even i` / `Odd i` 的 witness 后用 `omega`。

### 7.4 有限子和严格小于几何级数

这是最可能耗时的工程点。建议封装成独立通用引理:

```lean
lemma finite_subsum_lt_tsum_geometric_shift
    {s : Finset Nat} {r : Real} (hr0 : 0 < r) (hr1 : r < 1) :
    (sum k in s, r ^ (k + 1)) < (sum' k : Nat, r ^ (k + 1)) := ...
```

证明策略:

1. 用 `summable_geometric_of_lt_one (le_of_lt hr0) hr1` 得 `Summable fun k => r ^ k`,再推 shifted summable。
2. 把有限和写成 indicator 的 `tsum`,或用 `Summable.tsum_lt_tsum_of_nonneg`。
3. 选择一个 `k0` 不在 `s` 中,例如 `s.sup id + 1` 或 `s.max' + 1`;在该点 indicator 项为 `0`,全级数项 `r^(k0+1) > 0`。
4. 所有项非负由 `pow_nonneg (le_of_lt hr0)`。

可用现成声明:

- `hasSum_geometric_of_lt_one`
- `summable_geometric_of_lt_one`
- `tsum_geometric_of_lt_one`
- `Summable.sum_le_tsum`
- `Summable.tsum_lt_tsum_of_nonneg`
- `tsum_mul_left`
- `Finset.sum_le_sum`
- `Finset.sum_lt_sum`

若严格版卡住,可退一步证明一个带上界的有限 range 版本:

```lean
lemma finite_subsum_le_range_of_subset
    {s : Finset Nat} {M : Nat} (hs : forall k in s, k < M)
    {r : Real} (hr0 : 0 <= r) :
    (sum k in s, r ^ (k+1)) <= sum k in Finset.range M, r ^ (k+1) := ...

lemma range_geom_shift_lt_tsum
    {M : Nat} {r : Real} (hr0 : 0 < r) (hr1 : r < 1) :
    (sum k in Finset.range M, r ^ (k+1)) < sum' k : Nat, r ^ (k+1) := ...
```

第二个可用 closed form:

```lean
geom_sum_eq
geom_sum_mul_neg
tsum_geometric_of_lt_one
```

并由 `r^M > 0` 得严格。

### 7.5 偶项上界

自建主引理:

```lean
lemma zeckendorf_psi_sum_upper
    {l : List Nat} (hl : l.IsZeckendorfRep) :
    (l.map fun i => Real.goldenConj ^ i).sum < 1 / Real.goldenRatio := by
  -- hnodup : l.Nodup
  -- hmin : forall i in l, 2 <= i
  -- split list/finset by parity
  -- odd terms <= 0, so total <= even part
  -- even part maps injectively to k with i = 2*k+2
  -- compare with full shifted geometric positive series
  -- compute shifted geometric value as 1 / phi
  ...
```

风险点:把 `List` 上的 parity filter 和 `Finset` 子和对齐。建议先用 `l.toFinset` 和 `List.sum_toFinset`:

```lean
rw [← List.sum_toFinset (fun i => Real.goldenConj ^ i) hnodup]
```

然后在 `Finset` 上处理 parity。

### 7.6 奇项下界

自建:

```lean
lemma zeckendorf_psi_sum_lower
    {l : List Nat} (hl : l.IsZeckendorfRep) :
    -(1 / Real.goldenRatio ^ 2)
      < (l.map fun i => Real.goldenConj ^ i).sum := by
  -- split by parity
  -- even terms >= 0, so odd part <= total
  -- odd part maps to i = 2*k+3, hence psi^(2*k+3)=psi * r^(k+1)
  -- finite positive subseries < full positive subseries
  -- multiply by psi < 0 to reverse inequality
  -- compute psi * (1/phi) = -1/phi^2
  ...
```

常数归一化可用:

```lean
have hpsi : Real.goldenConj = - (1 / Real.goldenRatio) := by ...
have hgeom : (sum' k : Nat, (Real.goldenConj ^ 2) ^ (k+1)) = 1 / Real.goldenRatio := by ...
```

### 7.7 `MinusWindow`

最后目标很短:

```lean
theorem minusWindow_geometric : MinusWindow := by
  intro n
  rw [AxisWord.betaMinusReal_eq_sum]
  exact ⟨
    zeckendorf_psi_sum_lower (AxisWord.encode n).2,
    zeckendorf_psi_sum_upper (AxisWord.encode n).2
  ⟩
```

如果 simp 不认 `(AxisWord.encode n).2`,可写:

```lean
let w := AxisWord.encode n
change -(1 / Real.goldenRatio ^ 2) < AxisWord.betaMinusReal w
  ∧ AxisWord.betaMinusReal w < 1 / Real.goldenRatio
rw [AxisWord.betaMinusReal_eq_sum w]
exact ⟨zeckendorf_psi_sum_lower w.2, zeckendorf_psi_sum_upper w.2⟩
```

## 8. 已有现成界的检索结论

未在 mathlib 中发现 Zeckendorf 词的 `psi` 读数窗口界或等价命题。检索词包括:

```text
Zeckendorf.*golden
golden.*Zeckendorf
goldenConj.*zeckendorf
IsZeckendorfRep.*golden
betaMinus
MinusWindow
goldenConj ^
```

mathlib 的 `Real.goldenConj` 侧只有黄金比恒等式、Binet 公式、Fibonacci recurrence solution 等基础工具。窗口界是本项目特定引理,需要自建。

## 9. Route 乙: Beatty / floor 路线评估

路线内容:

```text
S(v) = shifted Zeckendorf decode = sum_{i in encode v} F_{i+1}
betaMinusReal(encode v) = S(v) - v * phi
S(v) = floor((v+1) * phi) - 1
```

若已证明这些,窗口界会非常短。因为:

```text
S(v) = floor(v*phi + 1/phi)
mu(v) = betaMinusReal(encode v)
      = floor(v*phi + 1/phi) - v*phi
```

由 floor 基本界:

```text
x - 1 < floor x <= x
```

取 `x = v*phi + 1/phi`,得到:

```text
-1 + 1/phi < mu(v) <= 1/phi
```

而 `-1 + 1/phi = -1/phi^2`。上界要从 `<=` 改成 `<`,需证明
`v*phi + 1/phi` 不是整数;这可由 `Real.goldenRatio_irrational` 和 `v+1 != 0` 推出,因为
`v*phi + 1/phi = (v+1)*phi - 1`。

可用 floor 现成工具:

- `Int.floor`
- `Int.floor_le`
- `Int.lt_floor_add_one`
- `Int.floor_add_intCast`
- `Int.fract`
- `Int.fract_nonneg`
- `Int.fract_lt_one`
- `Int.floor_add_fract`
- `Int.fract_eq_iff`

但这条路线的前置主命题 `S(v) = floor((v+1) * phi) - 1` 是 Wythoff / Beatty 型定理。mathlib 没有现成的 Zeckendorf shifted decode floor 公式。若按文档中的证明思路,它通常还会借助窗口唯一整数性质,从而对 `MinusWindow` 本身形成循环。

建议:

```text
为证明 MinusWindow: 选几何级数路线。
为证明推论 6.45 或亏空相位判读: 在 MinusWindow 之后再走 Beatty 路线。
```

几何级数路线的依赖面小:Zeckendorf list 结构、有限列表求和、`psi` 奇偶符号、实几何级数。Beatty 路线的最终三值证明更漂亮,但要先形式化 shifted decode、floor 公式、无理性非端点,前置成本更高。

## 10. 风险排序

低风险:

- `PhiInt.toRealMinus_phiPow`
- `AxisWord.betaMinusReal_eq_sum`
- 黄金比常数化简
- `IsZeckendorfRep` 推出 `2 <= i`

中风险:

- `IsZeckendorfRep` 推出 `Nodup`,主要因为 `List.isChain_iff_pairwise` 需要显式传递性实例。
- `List` sum 与 `Finset` parity split 的工程细节。
- 严格有限子和 `<` 无限几何和的封装。

高风险:

- 直接走 Beatty floor 路线证明 `S(v)=floor((v+1)phi)-1`。这不是局部代数引理,而是 Wythoff/切割投影层的结构定理。

最稳实现顺序:

1. `toRealMinus_phiPow` 与 `betaMinusReal_eq_sum`;
2. `IsZeckendorfRep` 的 `two_le_of_mem`, `nodup`;
3. 黄金常数与 `r = psi^2` 的几何级数值;
4. 通用 `finite_subsum_lt_tsum_geometric_shift`;
5. parity split 得上下界;
6. `MinusWindow` 一行收束。
