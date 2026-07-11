import BEDC.Derived.RHRoute.ZeroGenerationInitiality

/-
Prime–Zeckendorf–Gödel located generation tower (ζ-free forward dynamics + the
analytic-bridge obligation firewall).

这是 `GenerativeZeroCompletion` 的 fuller standalone 版 (oracle conv_ff4ff126afd06e33
的设计): 把 ChatGPT PZG-tower thread 的 "tick = 径向 scaling ⊕ 角向 rotation ⊕
正交 residual" 落成一个 **完全 ζ-free** 的 forward 生成动力学, 并把 "generation
orbit = 真 ζ 零集" 拆成 binding / completeness / soundness 三条 obligation, 用一道
依赖 firewall 把 analytic ζ evaluator 隔在动力学之外.

设计纪律 (全部 0-axiom / propext-free):
  * carrier = `LocatedComplex LR` (re/im over 抽象 located-real `LR`); 保持抽象 ⟹
    不 commit 任何具体 analytic 基础, 也无法 backward-fit ζ.
  * 维度用 unary `UDim`, Zeckendorf gate 用 Type-valued `ZBits.NoAdjacentGate`
    (rfl-checkable, 无 `decide` / `native_decide`).
  * `GenState` 只存 **syntax** (`GeneratedZero`), located 点是 *derived*
    (`GenState.point := locatedFold M term`) — 防 backward-fit.
  * orbit 只能从 `Orbit.init` + `Orbit.tick` 前推 (forward-only).
  * membership / 双向对应用 **Type-valued** `GeneratedPoint` / `TwoWay`, 不用
    Set / ∈ / ↔ / propext.
  * 三条 obligation 用带真字段的 `structure` (不是空 inductive marker); analytic
    evaluator (`LocatedZetaEvaluator`) 与 dynamics 之间是纯接口, dynamics 侧不 import ζ.

ConstructiveRH 的实际连接在 `GenerativeZeroCompletion` (走 tree 已有 RatComplex
surface); 本 brick 提供 ζ-free 动力学骨架 + obligation firewall, 不重复那条 bridge.
-/

namespace BEDC.Derived.RHRoute.LocatedGenerationTower

open BEDC.Derived.RHRoute.ZeroGenerationInitiality

universe u

/-! ## 1. Located-complex carrier -/

/-- 最小 located-complex 点: re/im over 抽象 located-real `LR`. -/
structure LocatedComplex (LR : Type u) where
  re : LR
  im : LR

namespace LocatedComplex

def mk' {LR : Type u} (re im : LR) : LocatedComplex LR := ⟨re, im⟩

theorem mk'_re {LR : Type u} (x y : LR) : (mk' x y).re = x := rfl
theorem mk'_im {LR : Type u} (x y : LR) : (mk' x y).im = y := rfl

end LocatedComplex

/-! ## 2. Unary dimension (无 Nat 算术 lemma) -/

inductive UDim : Type where
  | zero : UDim
  | succ : UDim → UDim

namespace UDim

def add : UDim → UDim → UDim
  | zero, m => m
  | succ n, m => succ (add n m)

theorem add_zero_left (m : UDim) : add zero m = m := rfl
theorem add_succ_left (n m : UDim) : add (succ n) m = succ (add n m) := rfl

end UDim

/-! ## 3. Zeckendorf bits + no-adjacent gate (Type-valued, rfl-checkable) -/

inductive ZBit : Type where
  | z : ZBit
  | o : ZBit

inductive ZBits : Type where
  | nil : ZBits
  | cons : ZBit → ZBits → ZBits

namespace ZBits

/-- `noAdjacentFrom prevWasOne xs`: 结构递归 on `xs`, 无 mutual, 无 decide.
`prev` 用完整 (非重叠) `Bool` 内层 match, 避免 wildcard-overlap 触发 propext. -/
def noAdjacentFrom (prev : Bool) : ZBits → Bool
  | nil => true
  | cons ZBit.z xs => noAdjacentFrom false xs
  | cons ZBit.o xs =>
      match prev with
      | true => false
      | false => noAdjacentFrom true xs

def noAdjacent (xs : ZBits) : Bool := noAdjacentFrom false xs

/-- 具体 Zeckendorf 无相邻 certificate, Type-valued. -/
structure NoAdjacentGate (xs : ZBits) where
  checked : noAdjacent xs = true

end ZBits

/-- 非平凡性 sanity: `1 0 1` 满足无相邻, gate 由 rfl 构造 (无 decide). -/
def bits_101 : ZBits :=
  ZBits.cons ZBit.o (ZBits.cons ZBit.z (ZBits.cons ZBit.o ZBits.nil))

theorem bits_101_ok : ZBits.noAdjacent bits_101 = true := rfl

def bits_101_gate : ZBits.NoAdjacentGate bits_101 := ⟨bits_101_ok⟩

/-- 相邻 `1 1` 被拒 (anti-vacuity: gate 真的能 sense adjacency). -/
theorem bits_11_rejected :
    ZBits.noAdjacent (ZBits.cons ZBit.o (ZBits.cons ZBit.o ZBits.nil)) = false := rfl

/-! ## 4. Located interpretation of the free zero syntax -/

/-- located-complex 解释: `α := LocatedComplex LR`, 构造子语义在 `zeroAlg` 里.
不 import ζ ⟹ 无法 backward-fit. -/
structure LocatedZeroModel (sig : RHFreeZeroSignature) (LR : Type u) where
  zeroAlg : ZeroAlgebra sig (LocatedComplex LR)

/-- 复用已证的 initial-algebra fold (不重造). -/
def locatedFold {sig : RHFreeZeroSignature} {LR : Type u}
    (M : LocatedZeroModel sig LR) :
    GeneratedZero sig → LocatedComplex LR :=
  GeneratedZero.fold M.zeroAlg

/-! ## 5. ζ-free forward dynamics -/

/-- 动力学载体类型族 (由已有 BEDC 模块供给: prime event / register / ledger / 残差). -/
structure DynamicsTypes where
  LogScale : Type u
  Angle : Type u
  PrimeEvent : Type u
  Register : Type u
  Ledger : Type u
  ResidualAtom : Type u
  Refinement : Type u

/-- 一次 tick 的原始数据 (仍 ζ-free): 径向 logScale ⊕ 角向 angle ⊕ 正交 residual. -/
structure RawGenerationStep (K : DynamicsTypes) where
  primeEvent : K.PrimeEvent
  logScale : K.LogScale
  angle : K.Angle
  residual : K.ResidualAtom
  residualDim : UDim
  zeckBits : ZBits
  refinement : K.Refinement

/-- 生成状态只存 syntax; located 点是 derived, 见 `GenState.point`. -/
structure GenState {sig : RHFreeZeroSignature} {LR : Type u}
    (_M : LocatedZeroModel sig LR) (K : DynamicsTypes) where
  term : GeneratedZero sig
  register : K.Register
  ledger : K.Ledger
  dim : UDim

/-- located 点 = 对 syntax 做 fold, 不单独存储. -/
def GenState.point {sig : RHFreeZeroSignature} {LR : Type u}
    {M : LocatedZeroModel sig LR} {K : DynamicsTypes}
    (s : GenState M K) : LocatedComplex LR :=
  locatedFold M s.term

/-- ζ-free forward 动力学: 唯一推进方式 = 旧 syntax + prime-driven tick → 新 syntax. -/
structure GenerationDynamics {sig : RHFreeZeroSignature} {LR : Type u}
    (M : LocatedZeroModel sig LR) (K : DynamicsTypes) where
  initTerm : GeneratedZero sig
  initRegister : K.Register
  initLedger : K.Ledger
  nextTerm : GeneratedZero sig → RawGenerationStep K → GeneratedZero sig
  advanceRegister : K.Register → RawGenerationStep K → K.Register
  extendLedger : K.Ledger → RawGenerationStep K → K.Ledger
  invariantOK : K.Register → RawGenerationStep K → Type u
  residualOK : K.Ledger → RawGenerationStep K → Type u

/-- 一个 legal step 携带 raw tick + Zeckendorf gate + invariant + residual certificate. -/
structure LegalGenerationStep {sig : RHFreeZeroSignature} {LR : Type u}
    {M : LocatedZeroModel sig LR} {K : DynamicsTypes}
    (D : GenerationDynamics M K) (s : GenState M K) where
  raw : RawGenerationStep K
  zeckOK : ZBits.NoAdjacentGate raw.zeckBits
  invariant : D.invariantOK s.register raw
  residual : D.residualOK s.ledger raw

def initState {sig : RHFreeZeroSignature} {LR : Type u}
    {M : LocatedZeroModel sig LR} {K : DynamicsTypes}
    (D : GenerationDynamics M K) : GenState M K :=
  { term := D.initTerm
    register := D.initRegister
    ledger := D.initLedger
    dim := UDim.zero }

def step {sig : RHFreeZeroSignature} {LR : Type u}
    {M : LocatedZeroModel sig LR} {K : DynamicsTypes}
    (D : GenerationDynamics M K) (s : GenState M K)
    (g : LegalGenerationStep D s) : GenState M K :=
  { term := D.nextTerm s.term g.raw
    register := D.advanceRegister s.register g.raw
    ledger := D.extendLedger s.ledger g.raw
    dim := UDim.add s.dim g.raw.residualDim }

/-! ### 结构性 step 引理, 全部 rfl -/

theorem step_term {sig : RHFreeZeroSignature} {LR : Type u}
    {M : LocatedZeroModel sig LR} {K : DynamicsTypes}
    (D : GenerationDynamics M K) (s : GenState M K)
    (g : LegalGenerationStep D s) :
    (step D s g).term = D.nextTerm s.term g.raw := rfl

theorem step_register {sig : RHFreeZeroSignature} {LR : Type u}
    {M : LocatedZeroModel sig LR} {K : DynamicsTypes}
    (D : GenerationDynamics M K) (s : GenState M K)
    (g : LegalGenerationStep D s) :
    (step D s g).register = D.advanceRegister s.register g.raw := rfl

theorem step_ledger {sig : RHFreeZeroSignature} {LR : Type u}
    {M : LocatedZeroModel sig LR} {K : DynamicsTypes}
    (D : GenerationDynamics M K) (s : GenState M K)
    (g : LegalGenerationStep D s) :
    (step D s g).ledger = D.extendLedger s.ledger g.raw := rfl

theorem step_dim {sig : RHFreeZeroSignature} {LR : Type u}
    {M : LocatedZeroModel sig LR} {K : DynamicsTypes}
    (D : GenerationDynamics M K) (s : GenState M K)
    (g : LegalGenerationStep D s) :
    (step D s g).dim = UDim.add s.dim g.raw.residualDim := rfl

theorem step_point {sig : RHFreeZeroSignature} {LR : Type u}
    {M : LocatedZeroModel sig LR} {K : DynamicsTypes}
    (D : GenerationDynamics M K) (s : GenState M K)
    (g : LegalGenerationStep D s) :
    (step D s g).point = locatedFold M (D.nextTerm s.term g.raw) := rfl

/-! ## 6. Forward-only orbit + recursor -/

/-- 只能从 init 前推的生成轨道. -/
inductive Orbit {sig : RHFreeZeroSignature} {LR : Type u}
    {M : LocatedZeroModel sig LR} {K : DynamicsTypes}
    (D : GenerationDynamics M K) : GenState M K → Type u where
  | init : Orbit D (initState D)
  | tick : {s : GenState M K} → Orbit D s →
      (g : LegalGenerationStep D s) → Orbit D (step D s g)

-- forward-only 消去用自动生成的 `Orbit.rec` (init / tick 两支); 不写手动索引
-- match, 因为 indexed-family match 会经 index 单一化引入 propext.

/-! ## 7. Type-valued 生成点 membership -/

/-- 点等价关系 (由 located-real tolerance kit 供给; 不用 Lean `=` 作 located 相等). -/
structure PointEquality (LC : Type u) where
  Eqv : LC → LC → Type u

/-- `z` 被生成 = 存在 forward state 其 located 点与 `z` 等价.
用 `Sigma`/`Prod` (Type), 不用 `Exists`/`And` (Prop), 避 propext. -/
def GeneratedPoint {sig : RHFreeZeroSignature} {LR : Type u}
    {M : LocatedZeroModel sig LR} {K : DynamicsTypes}
    (D : GenerationDynamics M K)
    (PEq : PointEquality (LocatedComplex LR))
    (z : LocatedComplex LR) : Type u :=
  Sigma (fun s : GenState M K =>
    Prod (Orbit D s) (PEq.Eqv (GenState.point s) z))

/-! ## 8. Analytic evaluator layer (firewall: dynamics 侧不依赖此层) -/

/-- located ζ evaluator 接口: carrier 求值 vs 真超越 ζ 求值, Type-valued 谓词. -/
structure LocatedZetaEvaluator (LC : Type u) (Val : Type u) where
  carrierEval : LC → Val
  trueEval : LC → Val
  IsZero : Val → Type u
  ValEq : Val → Val → Type u

def CarrierZetaZero {LC : Type u} {Val : Type u}
    (E : LocatedZetaEvaluator LC Val) (z : LC) : Type u :=
  E.IsZero (E.carrierEval z)

def TrueZetaZero {LC : Type u} {Val : Type u}
    (E : LocatedZetaEvaluator LC Val) (z : LC) : Type u :=
  E.IsZero (E.trueEval z)

/-! ## 9. 三条 obligation (structure 带真字段, 非空 marker) -/

/-- binding: carrier evaluator = 真 located ζ (诚实 analytic binding) + 零点 transport. -/
structure BindingObligation {LC : Type u} {Val : Type u}
    (E : LocatedZetaEvaluator LC Val) where
  eval_eq : (z : LC) → E.ValEq (E.carrierEval z) (E.trueEval z)
  carrier_zero_to_true : (z : LC) → CarrierZetaZero E z → TrueZetaZero E z
  true_zero_to_carrier : (z : LC) → TrueZetaZero E z → CarrierZetaZero E z

/-- completeness: 每个真 ζ 零点都出现在 forward orbit 里 ("BEDC 生成所有 ζ 点"). -/
structure CompletenessObligation {sig : RHFreeZeroSignature} {LR : Type u}
    {M : LocatedZeroModel sig LR} {K : DynamicsTypes}
    (D : GenerationDynamics M K)
    (PEq : PointEquality (LocatedComplex LR))
    (E : LocatedZetaEvaluator (LocatedComplex LR) (LocatedComplex LR)) where
  complete : (z : LocatedComplex LR) → TrueZetaZero E z → GeneratedPoint D PEq z

/-- soundness: 每个 forward-generated 点是真 ζ 零点. -/
structure SoundnessObligation {sig : RHFreeZeroSignature} {LR : Type u}
    {M : LocatedZeroModel sig LR} {K : DynamicsTypes}
    (D : GenerationDynamics M K)
    (PEq : PointEquality (LocatedComplex LR))
    (E : LocatedZetaEvaluator (LocatedComplex LR) (LocatedComplex LR)) where
  sound : (z : LocatedComplex LR) → GeneratedPoint D PEq z → TrueZetaZero E z

/-- 打包三条 obligation. forward brick 里没有任何定理去 *construct* 它. -/
structure ZetaBridgeObligations {sig : RHFreeZeroSignature} {LR : Type u}
    {M : LocatedZeroModel sig LR} {K : DynamicsTypes}
    (D : GenerationDynamics M K)
    (PEq : PointEquality (LocatedComplex LR))
    (E : LocatedZetaEvaluator (LocatedComplex LR) (LocatedComplex LR)) where
  binding : BindingObligation E
  completeness : CompletenessObligation D PEq E
  soundness : SoundnessObligation D PEq E

/-! ## 10. 无 ↔ / Set-ext 的零集双向对应 (projection-only, 被证) -/

structure TwoWay (A : Type u) (B : Type u) where
  toFun : A → B
  invFun : B → A

/-- 给定三条 obligation, generation orbit 与真 ζ 零集 Type-valued 双向对应.
纯 projection, 无 propext. -/
def generated_true_zero_twoWay {sig : RHFreeZeroSignature} {LR : Type u}
    {M : LocatedZeroModel sig LR} {K : DynamicsTypes}
    {D : GenerationDynamics M K}
    {PEq : PointEquality (LocatedComplex LR)}
    {E : LocatedZetaEvaluator (LocatedComplex LR) (LocatedComplex LR)}
    (O : ZetaBridgeObligations D PEq E)
    (z : LocatedComplex LR) :
    TwoWay (GeneratedPoint D PEq z) (TrueZetaZero E z) :=
  { toFun := O.soundness.sound z
    invFun := O.completeness.complete z }

end BEDC.Derived.RHRoute.LocatedGenerationTower
