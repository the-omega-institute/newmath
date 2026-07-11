# UnifiedTheory phase-1 形式化施工蓝图

本文是 `papers/unified_theory/lean4` 的 phase-1 施工蓝图。真实 Lean root 为
`UnifiedTheory`: `lakefile.lean` 中是 `lean_lib UnifiedTheory`, 根文件是
`UnifiedTheory.lean`。所有模块路径、namespace 与 `#check` 目标都以 `UnifiedTheory` 为准。

phase-1 只处理有限生成语法、mathlib 数论包装、PZG 稀疏素轴位表、规范归一化、
黄金双面有限代数、亏空整性与有限词递推。解析层、zeta/RH、自然边界、PNT、无穷
Euler product、窗口实验和总 kernel 载荷元命题不进入 universal theorem 路径。

## 0. Batch A 勘测结果

工作目录:

```bash
cd papers/unified_theory/lean4
```

指定勘测命令已在本地通过:

```lean
import Mathlib
#check @Nat.factorizationEquiv
#check @Nat.factorization_mul
#check @Nat.zeckendorfEquiv
#check @List.IsZeckendorfRep
#check @Nat.sum_zeckendorf_fib
#check @Nat.zeckendorf_sum_fib
#check @Real.goldenRatio
#check @Real.goldenConj
#check @Real.goldenRatio_sq
#check @Real.coe_fib_eq
#check @Relation.ReflTransGen
#check @Relation.Join
#check @WellFounded.induction
```

已确认的核心 declaration:

| declaration | confirmed signature | phase-1 用途 |
|---|---|---|
| `Nat.factorizationEquiv` | `ℕ+ ≃ ↑{f | ∀ p ∈ f.support, Nat.Prime p}` | `PrimeExp ≃ ℕ+`, theorem 4.4, PZG decode |
| `Nat.factorization_mul` | `∀ {a b : ℕ}, a ≠ 0 → b ≠ 0 → (a * b).factorization = a.factorization + b.factorization` | 乘法转指数向量加法 |
| `Nat.zeckendorfEquiv` | `ℕ ≃ { l // l.IsZeckendorfRep }` | theorem 5.3 与逐轴 Zeckendorf word |
| `List.IsZeckendorfRep` | `List ℕ → Prop` | canonical `AxisWord` 合法性谓词 |
| `Nat.sum_zeckendorf_fib` | `∀ n, (List.map Nat.fib n.zeckendorf).sum = n` | greedy encode 后 decode |
| `Nat.zeckendorf_sum_fib` | `∀ {l}, l.IsZeckendorfRep → (List.map Nat.fib l).sum.zeckendorf = l` | Zeckendorf 唯一性 |
| `Real.goldenRatio` | `ℝ` | `φ` 的实嵌入 |
| `Real.goldenConj` | `ℝ` | `ψ` 的实嵌入 |
| `Real.goldenRatio_sq` | `Real.goldenRatio ^ 2 = Real.goldenRatio + 1` | carry 与 `PhiInt.toRealPlus` |
| `Real.coe_fib_eq` | `∀ n, ↑(Nat.fib n) = (Real.goldenRatio ^ n - Real.goldenConj ^ n) / √5` | Binet bridge |
| `Relation.ReflTransGen` | `(α → α → Prop) → α → α → Prop` | abstract rewriting star closure |
| `Relation.Join` | `(α → α → Prop) → α → α → Prop` | joinability substrate |
| `WellFounded.induction` | `WellFounded r → ∀ {C}, ∀ a, (∀ x, (∀ y, r y x → C y) → C x) → C a` | Newman proof induction |

补充勘测也已通过:

| declaration | 用途 |
|---|---|
| `Nat.factorizationEquiv_inv_apply` | inverse factorization 是有限素数幂乘积 |
| `Nat.factorization_prod_apply` | 有限乘积的单坐标指数公式 |
| `Nat.factorization_inj` | 非零自然数上 factorization injective |
| `Nat.eq_of_factorization_eq` | 坐标相等推出非零自然数相等 |
| `Nat.prod_pow_factorization_eq_self` | prime-supported `Finsupp` refactorization |
| `Nat.factorization_prod_pow_eq_self` | 从 factorization 重构非零自然数 |
| `List.IsZeckendorfRep_nil` | empty AxisWord 合法 |
| `Nat.isZeckendorfRep_zeckendorf` | greedy Zeckendorf word 合法 |
| `Real.goldenConj_sq` | `ψ ^ 2 = ψ + 1` |
| `Real.goldenRatio_mul_goldenConj` | `φ * ψ = -1` |
| `Real.goldenConj_mul_goldenRatio` | `ψ * φ = -1` |
| `Real.goldenRatio_add_goldenConj` | `φ + ψ = 1` |
| `Real.goldenRatio_sub_goldenConj` | `φ - ψ = √5` |
| `Real.inv_goldenRatio` | `φ⁻¹ = -ψ` |
| `Relation.TransGen` | positive rewrite closure |
| `Relation.ReflTransGen.trans` | star closure 传递性 |
| `Relation.ReflTransGen.single` | one-step rewrite 转 star rewrite |

指定 survey 中需要核验的名字没有失败项；Batch A 当前没有 `[NEEDS-FIX]` 条目。

## 1. 模块结构

phase-1 模块树:

```text
UnifiedTheory/Foundation/Mark.lean
UnifiedTheory/Foundation/History.lean
UnifiedTheory/Foundation/Rewriting.lean

UnifiedTheory/Arithmetic/PrimeAxes.lean
UnifiedTheory/Arithmetic/Zeckendorf.lean

UnifiedTheory/PZG/Carrier.lean
UnifiedTheory/PZG/Decode.lean
UnifiedTheory/PZG/Normalize.lean

UnifiedTheory/Golden/PhiInt.lean
UnifiedTheory/Golden/Lambda.lean
UnifiedTheory/Golden/Carry.lean
UnifiedTheory/Golden/Deficit.lean
UnifiedTheory/Golden/FiniteWords.lean

UnifiedTheory/Kernel/Components.lean
UnifiedTheory/Kernel/LedgerStatus.lean

UnifiedTheory/All.lean
```

Import 约束:

| layer | 可 import | 禁 import |
|---|---|---|
| `Foundation` | 必要的 Mathlib relation/list 基础 | `Arithmetic`, `PZG`, `Golden`, 任何 analytic/zeta 层 |
| `Arithmetic` | 必要时 import `Foundation`;通常直接用 Mathlib | `PZG`, `Golden`, analytic 模块 |
| `PZG` | `Arithmetic`, 少量 public `Foundation` 名字 | `Golden`, analytic 模块 |
| `Golden` | `Arithmetic`, `PZG`, golden-ratio Mathlib API | zeta/RH/completion/zero-ledger 模块 |
| `Kernel` | `Foundation`, `Arithmetic`, `PZG`, `Golden` 的 public interface | proof-internal helper 与 analytic 层 |
| `All.lean` | phase-1 public modules | statement-only frontier files;除非有明确边界,不 import finite scan files |

依赖 DAG:

```text
Foundation.Mark
  -> Foundation.History
  -> Kernel.Components

Foundation.Rewriting
  -> Kernel.Components

Arithmetic.PrimeAxes
  -> PZG.Carrier
  -> PZG.Decode
  -> PZG.Normalize
  -> Golden.Lambda
  -> Kernel.Components

Arithmetic.Zeckendorf
  -> PZG.Carrier
  -> PZG.Decode
  -> Golden.PhiInt
  -> Golden.Lambda
  -> Golden.Carry
  -> Golden.Deficit
  -> Golden.FiniteWords
  -> Kernel.Components

Golden.PhiInt
  -> Golden.Lambda
  -> Golden.Carry
  -> Golden.Deficit
  -> Golden.FiniteWords
```

`Foundation.Rewriting` 是 generic rewriting 模块,与 history/PZG 无关。它可以被
`Kernel.Components` 暴露,但 PZG normalization 在 phase-1 中不依赖 carry-rewrite theorem。
Normalization 通过 decode/encode equivalence 定义。

## 2. 冻结接口草案

下面的 Lean signature 是 public target shape。execution worker 可以调整局部 helper 名称,
但不能改变 public carrier choice 或 theorem scope。

### 2.1 Mark 与 sigma

File: `UnifiedTheory/Foundation/Mark.lean`

```lean
namespace UnifiedTheory

inductive Mark where
  | zero : Mark
  | one : Mark
deriving DecidableEq, Repr

namespace Mark

def sigma : Mark -> Mark

theorem sigma_zero : sigma zero = one
theorem sigma_one : sigma one = zero
theorem sigma_involutive : Function.Involutive sigma
theorem sigma_ne_id : sigma zero ≠ zero

end Mark
end UnifiedTheory
```

`Mark` 是 `σ` 的 primary API；不要把 `Bool` 暴露为 primary carrier。

### 2.2 History 与 Event

File: `UnifiedTheory/Foundation/History.lean`

```lean
namespace UnifiedTheory

inductive MarkHist where
  | empty : MarkHist
  | ext (tag : Mark) (prev : MarkHist) : MarkHist
deriving DecidableEq, Repr

namespace MarkHist

def length : MarkHist -> Nat
def append : MarkHist -> MarkHist -> MarkHist

theorem empty_append (h : MarkHist) : append empty h = h
theorem append_empty (h : MarkHist) : append h empty = h
theorem append_assoc (a b c : MarkHist) :
  append (append a b) c = append a (append b c)
theorem length_append (a b : MarkHist) :
  length (append a b) = length a + length b

end MarkHist

structure Event (Op Arg : Type u) where
  src : MarkHist
  op : Op
  arg : Arg
  tag : Mark

abbrev EventHist (Op Arg : Type u) := List (Event Op Arg)

namespace EventHist

def generate {Op Arg : Type u}
    (h : EventHist Op Arg) (u : Event Op Arg) : EventHist Op Arg :=
  h ++ [u]

theorem generate_length {Op Arg : Type u}
    (h : EventHist Op Arg) (u : Event Op Arg) :
  (generate h u).length = h.length + 1

end EventHist
end UnifiedTheory
```

A1/A2 不写成 axiom,也不写成假 theorem。A1 是 inductive/list recursor,
A2 是 `MarkHist` 与 `List` 的 finite-by-construction 性质。

### 2.3 Generic rewriting 与 Newman

File: `UnifiedTheory/Foundation/Rewriting.lean`

```lean
namespace UnifiedTheory.Rewriting

variable {α : Type u}

abbrev Reduces (r : α -> α -> Prop) := Relation.ReflTransGen r

def NormalForm (r : α -> α -> Prop) (a : α) : Prop :=
  ∀ b, ¬ r a b

def Joinable (r : α -> α -> Prop) (a b : α) : Prop :=
  ∃ c, Reduces r a c ∧ Reduces r b c

def LocallyConfluent (r : α -> α -> Prop) : Prop :=
  ∀ a b c, r a b -> r a c -> Joinable r b c

def Confluent (r : α -> α -> Prop) : Prop :=
  ∀ a b c, Reduces r a b -> Reduces r a c -> Joinable r b c

def Terminates (r : α -> α -> Prop) : Prop :=
  WellFounded (fun y x => r x y)

theorem newman_confluent
    (r : α -> α -> Prop) :
  Terminates r -> LocallyConfluent r -> Confluent r

theorem normal_form_unique_of_confluent
    (r : α -> α -> Prop) :
  Confluent r ->
  Reduces r a n1 -> NormalForm r n1 ->
  Reduces r a n2 -> NormalForm r n2 ->
  n1 = n2

theorem exists_unique_normal_form
    (r : α -> α -> Prop) :
  Terminates r -> LocallyConfluent r ->
  ∃! n, Reduces r a n ∧ NormalForm r n

end UnifiedTheory.Rewriting
```

证明路线:用 `WellFounded.induction` 在 terminating successor relation 上证明 generic
Newman theorem。closure 使用 `Relation.ReflTransGen.single`, `.trans` 与 star reduction 的
head/tail case split。mathlib 已有 relation/well-founded substrate,但没有已核验的 generic
Newman package。

### 2.4 Prime axes

File: `UnifiedTheory/Arithmetic/PrimeAxes.lean`

```lean
namespace UnifiedTheory

abbrev PrimeExp :=
  { f : Nat ->₀ Nat // ∀ p, p ∈ f.support -> Nat.Prime p }

namespace PrimeExp

noncomputable def equivPNat : PrimeExp ≃ ℕ+ :=
  Nat.factorizationEquiv.symm

def vp (p : Nat) (n : ℕ+) : Nat :=
  (n : Nat).factorization p

theorem vp_mul (p : Nat) (m n : ℕ+) :
  vp p (m * n) = vp p m + vp p n

theorem factorization_mul_pnat (m n : ℕ+) :
  ((m * n : ℕ+) : Nat).factorization =
    (m : Nat).factorization + (n : Nat).factorization

end PrimeExp

def euclidEscape (S : Finset Nat) : Nat :=
  S.prod id + 1

theorem euclidEscape_mod_eq_one
    (S : Finset Nat) (hS : ∀ p, p ∈ S -> Nat.Prime p) :
  ∀ p, p ∈ S -> euclidEscape S % p = 1

theorem euclidEscape_has_prime_outside
    (S : Finset Nat) (hS : ∀ p, p ∈ S -> Nat.Prime p) :
  ∃ q, Nat.Prime q ∧ q ∣ euclidEscape S ∧ q ∉ S

end UnifiedTheory
```

对应 theorem 4.2/4.3 通过 mathlib 复用；4.4 是 exponent-vector equivalence 与 additivity；
4.5 是 Euclid escape。禁止从 histories 重建 `Nat`、FTA 或 division。

### 2.5 Zeckendorf bridge

File: `UnifiedTheory/Arithmetic/Zeckendorf.lean`

```lean
namespace UnifiedTheory

def pzgFib (k : Nat) : Nat := Nat.fib (k + 1)

abbrev AxisWord := { l : List Nat // l.IsZeckendorfRep }

namespace AxisWord

instance : Zero AxisWord := ⟨[], List.IsZeckendorfRep_nil⟩

def decode (w : AxisWord) : Nat :=
  (w.1.map Nat.fib).sum

noncomputable def ofNat (n : Nat) : AxisWord :=
  Nat.zeckendorfEquiv n

noncomputable def equivNat : AxisWord ≃ Nat :=
  Nat.zeckendorfEquiv.symm

theorem decode_ofNat (n : Nat) : decode (ofNat n) = n
theorem ofNat_decode (w : AxisWord) : ofNat (decode w) = w
theorem pzgFib_eq (k : Nat) : pzgFib k = Nat.fib (k + 1)

end AxisWord
end UnifiedTheory
```

Index convention: 文档 bit index `k ≥ 1` 对应 mathlib Fibonacci index `k+1`。内部
`AxisWord` 存 mathlib Fibonacci indices；合法 representation 使用 indices `≥ 2`。

### 2.6 PZG sparse prime-axis table

Files: `UnifiedTheory/PZG/Carrier.lean`, `UnifiedTheory/PZG/Decode.lean`

```lean
namespace UnifiedTheory

structure PZGTable where
  axis : Nat ->₀ AxisWord
  prime_support : ∀ p, p ∈ axis.support -> Nat.Prime p

namespace PZGTable

def exponent (z : PZGTable) : Nat ->₀ Nat

theorem exponent_prime_support (z : PZGTable) :
  ∀ p, p ∈ (exponent z).support -> Nat.Prime p

def toPrimeExp (z : PZGTable) : PrimeExp :=
  ⟨exponent z, exponent_prime_support z⟩

noncomputable def ofPrimeExp (e : PrimeExp) : PZGTable

noncomputable def equivPrimeExp : PZGTable ≃ PrimeExp

noncomputable def decode : PZGTable -> ℕ+ :=
  fun z => PrimeExp.equivPNat (toPrimeExp z)

noncomputable def encode : ℕ+ -> PZGTable :=
  fun n => ofPrimeExp (Nat.factorizationEquiv n)

noncomputable def equivPNat : PZGTable ≃ ℕ+

def bit (z : PZGTable) (p k : Nat) : Bool :=
  decide ((k + 1) ∈ (z.axis p).1)

theorem decode_encode (n : ℕ+) : decode (encode n) = n
theorem encode_decode (z : PZGTable) : encode (decode z) = z

end PZGTable
end UnifiedTheory
```

此 carrier 是硬约束。`PZGTable` 是 prime axis 到 Zeckendorf word 的 sparse table,
不是 exponent vector 的同义别名。证明可以经过 `PrimeExp`,但 public carrier 必须保留
literal bit-table projection `bit z p k`。

### 2.7 PZG normalization

File: `UnifiedTheory/PZG/Normalize.lean`

```lean
namespace UnifiedTheory.PZGTable

noncomputable def normAdd (z w : PZGTable) : PZGTable :=
  encode (decode z * decode w)

theorem decode_normAdd (z w : PZGTable) :
  decode (normAdd z w) = decode z * decode w

theorem normAdd_unique
    (z w u : PZGTable)
    (h : decode u = decode z * decode w) :
  u = normAdd z w

end UnifiedTheory.PZGTable
```

Theorem 5.6 通过 `PZGTable.equivPNat` 的 canonical re-encoding 证明。Theorem 5.7
carry-chain termination 不作为本模块依赖。

### 2.8 Exact `PhiInt`

File: `UnifiedTheory/Golden/PhiInt.lean`

```lean
namespace UnifiedTheory.Golden

structure PhiInt where
  a : Int
  b : Int
deriving DecidableEq, Repr

namespace PhiInt

def zero : PhiInt := ⟨0, 0⟩
def one : PhiInt := ⟨1, 0⟩
def ofInt (n : Int) : PhiInt := ⟨n, 0⟩
def phi : PhiInt := ⟨0, 1⟩

def add (x y : PhiInt) : PhiInt := ⟨x.a + y.a, x.b + y.b⟩
def neg (x : PhiInt) : PhiInt := ⟨-x.a, -x.b⟩
def sub (x y : PhiInt) : PhiInt := add x (neg y)

def mul (x y : PhiInt) : PhiInt :=
  ⟨x.a * y.a + x.b * y.b,
   x.a * y.b + x.b * y.a + x.b * y.b⟩

instance : Zero PhiInt := ⟨zero⟩
instance : One PhiInt := ⟨one⟩
instance : Add PhiInt := ⟨add⟩
instance : Neg PhiInt := ⟨neg⟩
instance : Sub PhiInt := ⟨sub⟩
instance : Mul PhiInt := ⟨mul⟩

def conj (x : PhiInt) : PhiInt :=
  ⟨x.a + x.b, -x.b⟩

def phiPow : Nat -> PhiInt

noncomputable def toRealPlus (x : PhiInt) : Real :=
  (x.a : Real) + (x.b : Real) * Real.goldenRatio

noncomputable def toRealMinus (x : PhiInt) : Real :=
  (x.a : Real) + (x.b : Real) * Real.goldenConj

theorem conj_involutive : Function.Involutive conj
theorem conj_phi : conj phi = ⟨1, -1⟩
theorem fixed_conj_iff_integer (x : PhiInt) :
  conj x = x ↔ x.b = 0

theorem toRealPlus_phiPow (i : Nat) :
  toRealPlus (phiPow i) = Real.goldenRatio ^ i

theorem toRealMinus_phiPow (i : Nat) :
  toRealMinus (phiPow i) = Real.goldenConj ^ i

end PhiInt
end UnifiedTheory.Golden
```

不用 `Zsqrtd` 作为 primary carrier；`φ = (1 + √5) / 2` 会引入半整 parity。phase-1
使用 basis `{1, φ}` 上的 pair model `ℤ[φ]`,关系为 `φ² = φ + 1`。

### 2.9 Lambda 与 beta

File: `UnifiedTheory/Golden/Lambda.lean`

```lean
namespace UnifiedTheory
namespace AxisWord

noncomputable def betaPlusReal (w : AxisWord) : Real :=
  (w.1.map fun i => Real.goldenRatio ^ i).sum

noncomputable def betaMinusReal (w : AxisWord) : Real :=
  (w.1.map fun i => Real.goldenConj ^ i).sum

def betaPhi (w : AxisWord) : Golden.PhiInt :=
  w.1.foldr (fun i acc => Golden.PhiInt.phiPow i + acc) 0

theorem beta_binet (w : AxisWord) :
  betaPlusReal w - betaMinusReal w =
    Real.sqrt 5 * (decode w : Real)

theorem betaPhi_b_coeff (w : AxisWord) :
  (betaPhi w).b = (decode w : Int)

theorem betaMinus_window (w : AxisWord) (hw : decode w ≠ 0) :
  -((Real.goldenRatio ^ 2)⁻¹) < betaMinusReal w ∧
    betaMinusReal w < Real.goldenRatio⁻¹

end AxisWord

namespace Golden

noncomputable def betaPlusNat (n : Nat) : Real :=
  AxisWord.betaPlusReal (AxisWord.ofNat n)

noncomputable def betaMinusNat (n : Nat) : Real :=
  AxisWord.betaMinusReal (AxisWord.ofNat n)

def betaPhiNat (n : Nat) : PhiInt :=
  AxisWord.betaPhi (AxisWord.ofNat n)

theorem betaPhiNat_b_coeff (n : Nat) :
  (betaPhiNat n).b = (n : Int)

end Golden

namespace PZGTable

noncomputable def lambdaPlus (z : PZGTable) : Real :=
  z.axis.sum fun p w => AxisWord.betaPlusReal w * Real.log (p : Real)

noncomputable def lambdaMinus (z : PZGTable) : Real :=
  z.axis.sum fun p w => AxisWord.betaMinusReal w * Real.log (p : Real)

theorem lambdaMinus_normAdd_disjoint
    (z w : PZGTable)
    (hdisj : Disjoint z.axis.support w.axis.support) :
  lambdaMinus (normAdd z w) = lambdaMinus z + lambdaMinus w

theorem lambdaMinus_mul_of_coprime
    (m n : ℕ+) (h : Nat.Coprime (m : Nat) (n : Nat)) :
  lambdaMinus (encode (m * n)) =
    lambdaMinus (encode m) + lambdaMinus (encode n)

end PZGTable
end UnifiedTheory
```

`lambdaPlus/lambdaMinus` 是 finite PZG table 上的 universal definition。无穷 `W`,
`Z_qc`, Euler products, zeta transport 只保留 statement-only。

### 2.10 Carry algebra

File: `UnifiedTheory/Golden/Carry.lean`

```lean
namespace UnifiedTheory.Golden

theorem carry_adjacent_phi (i : Nat) :
  PhiInt.phiPow i + PhiInt.phiPow (i + 1) = PhiInt.phiPow (i + 2)

theorem carry_double_internal (i : Nat) (hi : 4 ≤ i) :
  PhiInt.phiPow i + PhiInt.phiPow i =
    PhiInt.phiPow (i + 1) + PhiInt.phiPow (i - 2)

theorem carry_bottom_two :
  PhiInt.phiPow 2 + PhiInt.phiPow 2 - PhiInt.phiPow 3 = PhiInt.ofInt 1

theorem carry_bottom_three :
  PhiInt.phiPow 3 + PhiInt.phiPow 3 -
    PhiInt.phiPow 4 - PhiInt.phiPow 2 = PhiInt.ofInt (-1)

end UnifiedTheory.Golden
```

底部规则的低指标必须与文档 index convention 对齐后再收 batch。这里证明的是 local algebra
identity,不是 global carry termination。

### 2.11 Deficit

File: `UnifiedTheory/Golden/Deficit.lean`

```lean
namespace UnifiedTheory.Golden

def deficitPhi (v w : Nat) : PhiInt :=
  betaPhiNat v + betaPhiNat w - betaPhiNat (v + w)

def deficitInt (v w : Nat) : Int :=
  (deficitPhi v w).a

theorem deficitPhi_integer (v w : Nat) :
  (deficitPhi v w).b = 0

theorem deficitPhi_eq_ofInt (v w : Nat) :
  deficitPhi v w = PhiInt.ofInt (deficitInt v w)

theorem betaMinus_window (n : Nat) (hn : 0 < n) :
  -((Real.goldenRatio ^ 2)⁻¹) < betaMinusNat n ∧
    betaMinusNat n < Real.goldenRatio⁻¹

theorem deficitInt_mem_three (v w : Nat) (hv : 0 < v) (hw : 0 < w) :
  deficitInt v w = -1 ∨ deficitInt v w = 0 ∨ deficitInt v w = 1

end UnifiedTheory.Golden
```

Theorem 6.22 证明路线:

1. 由 `Real.coe_fib_eq` 证明 `AxisWord.beta_binet`。
2. 对 `AxisWord.ofNat n` 应用 Binet gap,并用 `AxisWord.decode_ofNat` 得到
   `betaPlusNat n - betaMinusNat n = √5 * n`。
3. 在 exact carrier 中证明同一事实的系数形态:
   `Golden.betaPhiNat_b_coeff : (betaPhiNat n).b = n`。
4. `deficitPhi v w` 的 `b` 系数按 `v + w - (v+w)` 抵消,所以亏空落在 integer subring。

Theorem 6.25 证明路线:

1. 用合法 Zeckendorf word 的奇偶几何界证明 universal `AxisWord.betaMinus_window`。
2. 推出 Nat-level `Golden.betaMinus_window`,再与 `deficitPhi_integer` 合用。
3. 将实区间约束与 integer 约束相交,得到 `{-1,0,1}`。

若 window 界证不出,6.25 留出 universal scope；有限 scan 不能替代。

### 2.12 Finite words

File: `UnifiedTheory/Golden/FiniteWords.lean`

```lean
namespace UnifiedTheory.Golden

def LegalWordUpTo (K : Nat) : Type :=
  { w : AxisWord // ∀ i ∈ w.1, i ≤ K }

noncomputable def WFinite (K : Nat) (x y : Real) : Real
noncomputable def tWeight (K : Nat) (x y : Real) : Real

noncomputable def uCoord (K : Nat) (x y : Real) : Real :=
  -x * Real.goldenRatio ^ (K + 1) + y * Real.goldenConj ^ (K + 1)

def qForm (a b : Real) : Real :=
  a ^ 2 - a * b - b ^ 2

def signedFiveXY (K : Nat) (x y : Real) : Real :=
  if Even K then -(5 * x * y) else 5 * x * y

theorem W_finite_recurrence (K : Nat) (x y : Real) (hK : 1 ≤ K) :
  WFinite (K + 1) x y =
    WFinite K x y + tWeight (K + 1) x y * WFinite (K - 1) x y

theorem tWeight_recurrence (K : Nat) (x y : Real) (hK : 1 ≤ K) :
  tWeight (K + 1) x y = tWeight K x y * tWeight (K - 1) x y

theorem cassini_fricke (K : Nat) (x y : Real) :
  qForm (uCoord (K + 1) x y) (uCoord K x y) = signedFiveXY (K + 1) x y

end UnifiedTheory.Golden
```

`signedFiveXY` 编码 `5*x*y*(-1)^(K+1)`,避免在 `Real` 中处理 integer power coercion。
无穷 `W(x,y)` 仍是 statement-only。

### 2.13 Kernel aggregate

Files: `UnifiedTheory/Kernel/LedgerStatus.lean`, `UnifiedTheory/Kernel/Components.lean`

```lean
namespace UnifiedTheory.Kernel

inductive LedgerStatus where
  | open
  | closed
  | tail
  | semantic
deriving DecidableEq, Repr

structure Generation where
  mark : Type
  history : Type

structure PZGInterface where
  table : Type
  decode : table -> ℕ+
  encode : ℕ+ -> table

structure GoldenInterface where
  phiInt : Type
  lambdaPlus : PZGTable -> Real
  lambdaMinus : PZGTable -> Real

structure Components where
  generation : Generation
  pzg : PZGInterface
  golden : GoldenInterface
  ledgerStatus : Type

end UnifiedTheory.Kernel
```

`Components` 只聚合已经稳定的 public interface,不声称完整 21-component `𝒦` 已闭合。

## 3. Phase-1 target table

| source item | Lean status | module | proof route | confirmed dependencies |
|---|---|---|---|---|
| 1.1/1.2 marks and `σ` | universal / build-from-scratch | `Foundation.Mark` | 对 `Mark` case split | Lean core |
| 2.1/2.4 histories and append laws | universal / build-from-scratch | `Foundation.History` | `MarkHist` structural induction | inductive recursor/List |
| A1/A2 | by construction | `Foundation.History` | 不写 axiom；用 recursor 与 finite carrier | Lean inductive/List |
| 3.2 Newman unit criterion | universal / build-from-scratch over mathlib substrate | `Foundation.Rewriting` | well-founded induction | `Relation.ReflTransGen`, `Relation.Join`, `WellFounded.induction` |
| 4.2/4.3 FTA existence/uniqueness | mathlib-wrap | `Arithmetic.PrimeAxes` | factorization equivalence/injectivity | `Nat.factorizationEquiv`, `Nat.factorization_inj`, `Nat.eq_of_factorization_eq` |
| 4.4 free prime axes/additivity | universal wrapper | `Arithmetic.PrimeAxes` | finite-support exponent vectors | `Nat.factorizationEquiv`, `Nat.factorization_mul` |
| 4.5 Euclid escape | universal wrapper | `Arithmetic.PrimeAxes` | finite product and outside prime divisor | `Nat.factorization_prod_apply`, prime factor APIs |
| 5.3 Zeckendorf uniqueness | mathlib-wrap | `Arithmetic.Zeckendorf` | equivalence and round-trip | `Nat.zeckendorfEquiv`, `Nat.sum_zeckendorf_fib`, `Nat.zeckendorf_sum_fib` |
| 5.5 PZG bijection | universal / mathlib-assisted | `PZG.Decode` | compose `PrimeExp ≃ ℕ+` with per-axis Zeckendorf | `Nat.factorizationEquiv`, `Nat.zeckendorfEquiv` |
| 5.6 normalization multiplication | universal / mathlib-assisted | `PZG.Normalize` | `normAdd := encode (decode z * decode w)` | `Nat.factorization_mul`, `PZGTable.equivPNat` |
| 5.7 carry termination | deferred | none in phase-1 import path | later algorithmic rewrite termination | not needed for 5.6 |
| 6.2 local golden identities | universal helper | `Golden.PhiInt`, `Golden.Carry` | exact pair algebra plus real embedding | `Real.goldenRatio_sq`, `Real.goldenConj_sq` |
| full 6.3 minimality | statement-only unless linear algebra proof lands | not required | 只定义 `Prop` when tracking is needed | golden identities |
| 6.8 finite `λ₋` coprime additivity | universal finite theorem | `Golden.Lambda` | disjoint prime supports and finite sums | factorization support, PZG encode/decode |
| 6.21 carry ledger identities | universal local algebra | `Golden.Carry` | finite identities in `PhiInt` | `Real.goldenRatio_sq`, `Real.goldenConj_sq` |
| 6.22 deficit integrality | universal | `Golden.Deficit` | Binet gap and `PhiInt` coefficient cancellation | `Real.coe_fib_eq`, `Real.goldenRatio_sub_goldenConj` |
| 6.25 deficit three values | universal only after window proof | `Golden.Deficit` | geometric window plus integrality | `Real.inv_goldenRatio`, golden sign/size lemmas |
| 6.35 finite `W_K` | universal finite theorem | `Golden.FiniteWords` | finite word decomposition | `AxisWord` legality |
| 6.36 Cassini-Fricke | universal finite theorem | `Golden.FiniteWords` | direct algebra on `u_K` and `Q` | golden recurrence identities |

## 4. Scope 分类

### 4.1 Universal theorem

这些是 phase-1 可承重 theorem target:

| group | targets |
|---|---|
| finite syntax | `Mark.sigma_involutive`, `MarkHist.empty_append`, `MarkHist.append_empty`, `MarkHist.append_assoc`, `MarkHist.length_append` |
| rewriting | `Rewriting.newman_confluent`, `Rewriting.normal_form_unique_of_confluent`, `Rewriting.exists_unique_normal_form` |
| arithmetic | `PrimeExp.equivPNat`, `PrimeExp.vp_mul`, `euclidEscape_has_prime_outside` |
| Zeckendorf | `AxisWord.equivNat`, `AxisWord.decode_ofNat`, `AxisWord.ofNat_decode`, `AxisWord.pzgFib_eq` |
| PZG | `PZGTable.equivPNat`, `PZGTable.decode_encode`, `PZGTable.encode_decode`, `PZGTable.decode_normAdd` |
| finite lambda | `AxisWord.beta_binet`, `AxisWord.betaPhi_b_coeff`, `AxisWord.betaMinus_window`, `PZGTable.lambdaMinus_normAdd_disjoint`, `PZGTable.lambdaMinus_mul_of_coprime` |
| carry | adjacent/internal/bottom carry algebra identities |
| deficit | `deficitPhi_integer`, `deficitPhi_eq_ofInt`, `Golden.betaMinus_window`, `deficitInt_mem_three` |
| finite words | finite `W_K` recurrence, finite `tWeight` recurrence, `cassini_fricke` |

### 4.2 Statement-only

需要 Lean-side name 时可写 `def ..._Statement : Prop`。禁止跟一个
`theorem ... : True := True.intro`;也不能把这类目标计入 checked theorem。

| source items | reason |
|---|---|
| full 6.3 minimal shift-invariant double-sided lift | 需要专门 linear-algebra interface |
| 6.4 infinite `W(x,y)` | infinite analytic object |
| 6.5/6.6/6.7/6.8 analytic forms | convergence/model-set/density/infinite series |
| 6.10 load-bearing meta-claim | paper-level eligibility statement |
| 6.11/6.12/6.14/6.19 | Dirichlet series, Euler products, zeta factors, analytic convergence |
| 6.30/6.32/6.34 | zero transport, PNT, reflection, spectral geometry |
| 6.55/6.57 | two-variable Euler products, meromorphic continuation, natural boundary |
| O-5/O-6 | open bridge channels |

允许形态:

```lean
def ZqcEulerProduct_Statement : Prop := ...
def ZeroTransport_Statement : Prop := ...
```

禁止形态:

```lean
def ZqcEulerProduct_Statement : Prop := ...
theorem ZqcEulerProduct_well_formed : True := True.intro
```

### 4.3 Finite executable check

Finite check 只允许在 bound 写进 theorem 名与 statement 时出现。它们不得被
`PZG.Decode`, `PZG.Normalize`, universal `Golden.Deficit` import。

| source items | allowed target shape |
|---|---|
| 6.17 Tribonacci comparison | `WindowCheck.tribonacciUnique_bound_200000` |
| 6.28(ii) noncongruence scan | `WindowCheck.noncongruence_bound_<N>` |
| 6.38/6.49/6.53/6.54/6.58/6.59 coefficient tables | 带 degree/row bound 的低阶检查 |

Example:

```lean
namespace UnifiedTheory.WindowCheck

def TribonacciUnique (bound : Nat) : Bool := ...

theorem tribonacciUnique_bound_200000 :
  TribonacciUnique 200000 = true := by
  native_decide

end UnifiedTheory.WindowCheck
```

Finite check 不能用来证明 theorem 6.25；三值定理必须依赖 universal `betaMinus_window`。

### 4.4 DROP

phase-1 排除:

| item | decision |
|---|---|
| histories-to-`Nat` reconstruction | 直接用 mathlib `Nat` |
| hand FTA proof from histories | 直接用 `Nat.factorization` APIs |
| hand Zeckendorf proof when `Nat.zeckendorfEquiv` suffices | 直接用 mathlib equivalence |
| `PZGTable` as just exponent vector | invalid carrier; 会丢掉 Zeckendorf bit table |
| `_well_formed : True := True.intro` | fake proof pattern |
| theorem names that assert a source claim only because Lean has a similar name | invalid |
| 6.25 via finite scan without window proof | invalid |
| total-kernel record with unused fields | not phase-1 |
| RH/zeta/zero/PNT/natural-boundary modules in phase-1 imports | out of scope |

## 5. Batch A-K

每个 batch 的统一 acceptance gate:

```bash
cd papers/unified_theory/lean4 && lake build
```

再加对应 `#check` 目标与 no-`sorry` 条件。若 theorem 证不出,不要弱化成 `True`
theorem；要么停在该 batch,要么诚实移入 statement-only。

| batch | files | dependencies | parallel status | acceptance checks |
|---|---|---|---|---|
| A | `UnifiedTheory/All.lean`, import sanity only | none | serial first | 本文 Batch A 的 mathlib `#check`; `lake build` |
| B | `Foundation/Mark.lean`, `Foundation/History.lean`, `Kernel/LedgerStatus.lean` | A | A 后可与 C/D/E parallel | `#check UnifiedTheory.Mark.sigma_involutive`, `#check UnifiedTheory.MarkHist.append_assoc` |
| C | `Foundation/Rewriting.lean` | A | A 后 independent; proof high-risk | `#check UnifiedTheory.Rewriting.exists_unique_normal_form` |
| D | `Arithmetic/PrimeAxes.lean` | A | A 后可与 B/C/E parallel | `#check UnifiedTheory.PrimeExp.equivPNat`, `#check UnifiedTheory.euclidEscape_has_prime_outside` |
| E | `Arithmetic/Zeckendorf.lean` | A | A 后可与 B/C/D parallel | `#check UnifiedTheory.AxisWord.equivNat`, `#check UnifiedTheory.AxisWord.decode_ofNat` |
| F | `PZG/Carrier.lean`, `PZG/Decode.lean` | D, E | serial after D/E | `#check UnifiedTheory.PZGTable.equivPNat`, `#check UnifiedTheory.PZGTable.decode_encode`, `#check UnifiedTheory.PZGTable.encode_decode` |
| G | `PZG/Normalize.lean` | F | serial after F | `#check UnifiedTheory.PZGTable.decode_normAdd` |
| H | `Golden/PhiInt.lean`, `Golden/Lambda.lean` | E, F; `PhiInt` part 可在 A 后开工 | Lambda serial after F | `#check UnifiedTheory.AxisWord.beta_binet`, `#check UnifiedTheory.PZGTable.lambdaMinus` |
| I | `Golden/Carry.lean`, `Golden/Deficit.lean` | H, E | serial after H; carry 可先于 deficit | `#check UnifiedTheory.Golden.deficitPhi_integer`, `#check UnifiedTheory.Golden.deficitInt_mem_three` |
| J | `Golden/FiniteWords.lean` | E, H | H 后可与 I parallel | `#check UnifiedTheory.Golden.W_finite_recurrence`, `#check UnifiedTheory.Golden.cassini_fricke` |
| K | `Kernel/Components.lean` | B-G public outputs and completed H pieces | last | 从 clean file import `UnifiedTheory.Kernel.Components` 并访问 public structures |

Batch notes:

- C 独立处理 generic Newman；不能阻塞 PZG arithmetic。
- D/E 主要是 mathlib API wrapper,应保持文件小而稳定。
- F 是 phase-1 中央交付；必须暴露 `PZGTable`,不能只暴露自然数 equivalence。
- G 通过 canonical encode/decode 证明 theorem 5.6；不实现 carry algorithm。
- I 只有在 `betaMinus_window` 是 universal proof 时才收 6.25。否则只收 carry identities
  与 6.22 integrality,并把 6.25 留出 universal scope。
- K 不重述 theorem,只聚合已收 batch 的 public names。

## 6. Execution codex 开工须知

1. 工作目录是 `papers/unified_theory/lean4`。
2. Root namespace 和 import path 是 `UnifiedTheory`,不是 `PZGBEDC`。
3. 每个 theorem 必须 no `sorry`。
4. `Nat`, FTA, factorization, Zeckendorf 走 mathlib-wrap；不要从 histories 重建。
5. `Mark` 保持 two-constructor inductive；不要把 `Bool` 作为 primary API。
6. `MarkHist`/`EventHist` 保持 finite syntax；A1/A2 是 construction facts,不是 axioms。
7. Generic Newman 放在 `Foundation.Rewriting`,与 history/PZG 解耦。
8. `PZGTable.axis : Nat ->₀ AxisWord` 和 `prime_support` 是硬约束；不要 collapse 到 `PrimeExp`。
9. Theorem 5.6 的 normalization 定义为 `encode (decode z * decode w)`。
10. `PhiInt = ℤ × ℤ` with `φ² = φ + 1`;不要用 `Zsqrtd` 作 primary carrier。
11. Theorem 6.22 走 Binet gap 与 exact `PhiInt` 系数抵消。
12. Theorem 6.25 只接受 universal `betaMinus_window`;有限 scan 不能替代。
13. Finite executable check 不得被 universal modules import,且 theorem 名必须包含 bound。
14. Analytic modules 永远在 phase-1 下游；phase-1 modules 不 import zeta/RH/completion/zero-ledger code。
15. 每个 batch 的 canonical gate 是 `lake build` + targeted `#check` + no `sorry`。
