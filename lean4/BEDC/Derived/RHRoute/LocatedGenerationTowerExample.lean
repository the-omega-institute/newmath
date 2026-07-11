import BEDC.Derived.RHRoute.LocatedGenerationTower
import BEDC.Derived.RHRoute.FiniteEulerDirichlet
import BEDC.Derived.RHRoute.FinitePrimeTowerReadout

/-
`LocatedGenerationTower` 的端到端 toy 实例, 坐实非 vacuity: 每个抽象参数
(`LR` / `DynamicsTypes` / `GenerationDynamics` / `PointEquality`) 都被具体值填满,
forward 动力学真的推进 (register 0 → 1), 并且给出 `GeneratedPoint` 的具体 inhabitant
(init 点 + depth-1 tick 点都 genuinely generated). 全部 0-axiom / propext-free.

这是 *toy*: `toyZeroAlg` 是常值代数 (无真 ζ 语义), toy dynamics 用 `Unit` 填充非
essential 通道 — 目的是证明 `LocatedGenerationTower` 的类型全部可 inhabit、动力学可
run、`GeneratedPoint` 非空, 不是一个有意义的零集. 真 prime-seed 语义 + located-real
carrier 的实例化撞 located-ζ 墙 (user-decision / Loning territory), 不在此.
-/

namespace BEDC.Derived.RHRoute.LocatedGenerationTowerExample

open BEDC.Derived.RHRoute.LocatedGenerationTower
open BEDC.Derived.RHRoute.ZeroGenerationInitiality
open BEDC.Derived.RHRoute.FinitePrimeWindow
open BEDC.Derived.RHRoute.FiniteEulerDirichlet
open BEDC.Derived.RHRoute.FinitePrimeTowerReadout

/-- toy located-real = unary `UDim` (propext-clean, non-degenerate). -/
abbrev ToyLR : Type := UDim

/-! ### 具体 prime window {2} + 一个 base `GeneratedZero` seed -/

def emptyWindow : FinitePrimeWindow.PrimeWindow :=
  { elems := [], nodup := NoDup.nil, all_prime := All.nil }

def toyWindow : FinitePrimeWindow.PrimeWindow := extendWindow emptyWindow 2 two_isPrime

theorem toyWindow_mem_two : PrimeWindow.mem 2 toyWindow :=
  extendWindow_mem_self emptyWindow 2 two_isPrime

/-- prime-2-seeded base 生成元 (唯一非递归构造子 `primeLocal`). -/
def toySeed : GeneratedZero rhFreeZeroSignature :=
  GeneratedZero.primeLocal toyWindow 2 toyWindow_mem_two

/-! ### 具体 located-complex 模型 (toy 常值代数) -/

def toyZeroAlg : ZeroAlgebra rhFreeZeroSignature (LocatedComplex ToyLR) where
  alg := fun _ => LocatedComplex.mk' UDim.zero UDim.zero

def toyModel : LocatedZeroModel rhFreeZeroSignature ToyLR :=
  { zeroAlg := toyZeroAlg }

/-! ### 具体动力学 (register / ledger = UDim 步数计数; 其余 = Unit) -/

def toyDyn : DynamicsTypes :=
  { LogScale := Unit
    Angle := Unit
    PrimeEvent := Unit
    Register := UDim
    Ledger := UDim
    ResidualAtom := Unit
    Refinement := Unit }

def toyDynamics : GenerationDynamics toyModel toyDyn where
  initTerm := toySeed
  initRegister := UDim.zero
  initLedger := UDim.zero
  nextTerm := fun t _ => GeneratedZero.functionalMirror t
  advanceRegister := fun r _ => UDim.succ r
  extendLedger := fun l _ => UDim.succ l
  invariantOK := fun _ _ => Unit
  residualOK := fun _ _ => Unit

/-! ### 一个具体 legal step (Zeckendorf gate = bits_101; invariant/residual = Unit) -/

def toyRaw : RawGenerationStep toyDyn :=
  { primeEvent := ()
    logScale := ()
    angle := ()
    residual := ()
    residualDim := UDim.succ UDim.zero
    zeckBits := bits_101
    refinement := () }

def toyStep : LegalGenerationStep toyDynamics (initState toyDynamics) :=
  { raw := toyRaw
    zeckOK := bits_101_gate
    invariant := ()
    residual := () }

/-- forward 动力学真的推进: 一 tick 后 register 从 0 变成 1. -/
theorem toyStep_register_advances :
    (step toyDynamics (initState toyDynamics) toyStep).register
      = UDim.succ UDim.zero := rfl

theorem toyStep_ledger_advances :
    (step toyDynamics (initState toyDynamics) toyStep).ledger
      = UDim.succ UDim.zero := rfl

/-! ### depth-1 orbit + Type-valued point equality -/

def toyOrbit1 :
    Orbit toyDynamics (step toyDynamics (initState toyDynamics) toyStep) :=
  Orbit.tick Orbit.init toyStep

/-- toy 点等价 = 结构相等的 `PLift` (Type-valued, propext-free). -/
def toyPEq : PointEquality (LocatedComplex ToyLR) where
  Eqv := fun a b => PLift (a = b)

/-! ### 非 vacuity: 具体点 genuinely generated -/

/-- init 点被生成 (depth-0 witness). -/
def toyPoint0_generated :
    GeneratedPoint toyDynamics toyPEq (GenState.point (initState toyDynamics)) :=
  ⟨initState toyDynamics, (Orbit.init, PLift.up rfl)⟩

/-- depth-1 tick 点被生成 (forward 动力学真的产出一个新 orbit 点). -/
def toyPoint1_generated :
    GeneratedPoint toyDynamics toyPEq
      (GenState.point (step toyDynamics (initState toyDynamics) toyStep)) :=
  ⟨step toyDynamics (initState toyDynamics) toyStep, (toyOrbit1, PLift.up rfl)⟩

end BEDC.Derived.RHRoute.LocatedGenerationTowerExample
