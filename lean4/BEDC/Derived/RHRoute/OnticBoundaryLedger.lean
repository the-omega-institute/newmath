import BEDC.Derived.RHRoute.ConstructiveRHStatement
import BEDC.Derived.RHRoute.FinitePrimeWindow
import BEDC.Derived.RHRoute.ZeroGenerationInitiality

namespace BEDC.Derived.RHRoute.OnticBoundaryLedger

abbrev RatComplex :=
  BEDC.Derived.RHRoute.ConstructiveRHStatement.RatComplex

abbrev ConstructiveRH :=
  BEDC.Derived.RHRoute.ConstructiveRHStatement.ConstructiveRH

abbrev NontrivialZetaZero :=
  BEDC.Derived.RHRoute.ConstructiveRHStatement.NontrivialZetaZero

abbrev OnCriticalLine :=
  BEDC.Derived.RHRoute.ConstructiveRHStatement.OnCriticalLine

abbrev PrimeWindow :=
  BEDC.Derived.RHRoute.FinitePrimeWindow.PrimeWindow

abbrev RatNum :=
  BEDC.Derived.RationalUp.RatNum

abbrev RHFreeZeroSignature :=
  BEDC.Derived.RHRoute.ZeroGenerationInitiality.RHFreeZeroSignature

abbrev GeneratedZero :=
  BEDC.Derived.RHRoute.ZeroGenerationInitiality.GeneratedZero

/--
边界原因只给 ledger 分类。它不是证明状态, 也不是可消解的证书。
-/
inductive BoundaryReason where
  | conditional
  | classical
  | farEndBoundary
  | coverBoundary
  | noHairBoundary
  | hamiltonianResonanceBoundary

/--
集中 ledger 条目只保存陈述形状和原因。`statement` 是未证明命题,
不能被解读为 BEDC 已经证明该边界命题。
-/
structure BoundaryLedgerEntry where
  reason : BoundaryReason
  statement : Prop

/--
条件 RH 充分性边界的行数据。两个充分性入口都作为条件行出现:
`coreCompleteness` 和 `primeSieveOddExactness`。这里没有给出任何一行。
-/
structure ConditionalRHSufficiencyRows where
  coreCompleteness : Prop
  mirrorOddDefectPublic : Prop
  primeSieveOddExactness : Prop
  locatedFixedHalfCollapse : Prop

/--
boundary/conditional: 该陈述只记录 vision 中的条件证明形状。
未提供 `coreCompleteness` 或 `primeSieveOddExactness`, 因而没有证明 RH。
-/
def ConditionalRHSufficiencyBoundary_statement
    (rows : ConditionalRHSufficiencyRows) : Prop :=
  ((rows.coreCompleteness ∧ rows.mirrorOddDefectPublic) ∨
      (rows.primeSieveOddExactness ∧ rows.locatedFixedHalfCollapse)) ->
    ConstructiveRH

def conditionalRHSufficiencyBoundary
    (rows : ConditionalRHSufficiencyRows) : BoundaryLedgerEntry where
  reason := BoundaryReason.conditional
  statement := ConditionalRHSufficiencyBoundary_statement rows

/--
核心共通性与完备性边界的行数据。`coreCommonality` 是公共语言行;
`zetaZeroCoreCompleteness` 是对象专属完备性行, 不由公共语言自动给出。
-/
structure CoreCommonalityCompletionRows where
  coreCommonality : Prop
  zetaZeroCoreCompleteness : Prop
  normalDisplacementPublic : Prop
  noFourthLedger : Prop

/--
boundary/conditional: 该陈述记录“公共核心语言 + zeta 专属完备性”
才进入 RH 目标形状。公共核心语言本身不被当成完备性证明。
-/
def CoreCommonalityCompletionBoundary_statement
    (rows : CoreCommonalityCompletionRows) : Prop :=
  rows.coreCommonality ->
    ((rows.zetaZeroCoreCompleteness ∧ rows.normalDisplacementPublic) ∨
        rows.noFourthLedger) ->
      ConstructiveRH

def coreCommonalityCompletionBoundary
    (rows : CoreCommonalityCompletionRows) : BoundaryLedgerEntry where
  reason := BoundaryReason.conditional
  statement := CoreCommonalityCompletionBoundary_statement rows

/--
无远端吸收边界的行数据。有限窗口用 `PrimeWindow` 承载,
缺少的是 zeta 完成载体上排除有限缺陷的条件行。
-/
structure NoFarEndAbsorptionRows where
  finitePrimeDefect : PrimeWindow -> RatComplex -> Prop
  archimedeanCompletionRetained : Prop
  noFarEndAbsorption : Prop

/--
boundary/far-end: 该陈述记录有限素窗口缺陷不能被完成边界隐藏的形状。
远端不被放入 carrier, 也不作为可消去缺陷的内部对象。
-/
def NoFarEndAbsorptionBoundary_statement
    (rows : NoFarEndAbsorptionRows) : Prop :=
  rows.archimedeanCompletionRetained ->
    rows.noFarEndAbsorption ->
      ∀ s : RatComplex,
        NontrivialZetaZero s ->
          (∃ W : PrimeWindow, rows.finitePrimeDefect W s) ->
            False

def noFarEndAbsorptionBoundary
    (rows : NoFarEndAbsorptionRows) : BoundaryLedgerEntry where
  reason := BoundaryReason.farEndBoundary
  statement := NoFarEndAbsorptionBoundary_statement rows

/--
零源递归器 cover 边界的行数据。`generatedZero` 是已有闭生成零源,
`cover` 是缺失的全零源覆盖行, `farEndUnity` 是生成行上的远端统一条件。
-/
structure ZeroRecursorCoverRows where
  signature : RHFreeZeroSignature
  interpret : GeneratedZero signature -> RatComplex
  cover : (s : RatComplex) -> NontrivialZetaZero s ->
    ∃ z : GeneratedZero signature, interpret z = s
  farEndUnity : (z : GeneratedZero signature) -> OnCriticalLine (interpret z)

/--
boundary/cover: 该陈述记录“cover + 生成行远端统一”给出 RH section 的形状。
这里没有构造 `cover`, 也没有从单个零行推出全零源递归器。
-/
def ZeroRecursorCoverBoundary_statement
    (rows : ZeroRecursorCoverRows) : Prop :=
  (∀ s : RatComplex,
    NontrivialZetaZero s ->
      ∃ z : GeneratedZero rows.signature, rows.interpret z = s) ->
    ((z : GeneratedZero rows.signature) -> OnCriticalLine (rows.interpret z)) ->
      ∀ s : RatComplex,
        NontrivialZetaZero s ->
          OnCriticalLine s

def ZeroRecursorCoverBoundary_recordedCover
    (rows : ZeroRecursorCoverRows) : Prop :=
  ∀ s : RatComplex,
    NontrivialZetaZero s ->
      ∃ z : GeneratedZero rows.signature,
        rows.interpret z = s

def ZeroRecursorCoverBoundary_recordedFarEndUnity
    (rows : ZeroRecursorCoverRows) : Prop :=
  (z : GeneratedZero rows.signature) -> OnCriticalLine (rows.interpret z)

def zeroRecursorCoverBoundary
    (rows : ZeroRecursorCoverRows) : BoundaryLedgerEntry where
  reason := BoundaryReason.coverBoundary
  statement := ZeroRecursorCoverBoundary_statement rows

/--
远端 identity 边界的行数据。`energy`、`closure` 和 `far-end` 只按
vision 的路线标签读取: Lean 侧不把它们解释成物理能量、几何端点,
也不构造隐藏的远端对象。
-/
structure FarEndIdentityBoundaryRows where
  finiteEnergyReadout : PrimeWindow -> RatComplex -> RatNum
  farEndClose : RatComplex -> RatComplex
  farEndClosed : RatComplex -> Prop
  farEndEnergyUnity : RatComplex -> Prop

def FarEndIdentityBoundary_identityPreservesFiniteEnergy
    (rows : FarEndIdentityBoundaryRows) : Prop :=
  ∀ s : RatComplex,
    rows.farEndClosed s ->
      ∀ W : PrimeWindow,
        BEDC.Derived.RationalUp.RatEq
          (rows.finiteEnergyReadout W s)
          (rows.finiteEnergyReadout W (rows.farEndClose s))

def FarEndIdentityBoundary_zeroRowsReachIdentity
    (rows : FarEndIdentityBoundaryRows) : Prop :=
  ∀ s : RatComplex,
    NontrivialZetaZero s ->
      rows.farEndClosed s ∧ rows.farEndEnergyUnity s

def FarEndIdentityBoundary_energyUnityFixedHalf
    (rows : FarEndIdentityBoundaryRows) : Prop :=
  ∀ s : RatComplex,
    NontrivialZetaZero s ->
      rows.farEndEnergyUnity s ->
        OnCriticalLine s

/--
boundary/far-end: 该陈述只登记“远端 identity 行 + 零行到达 +
fixed-half 读回”足以形成 RH 形状。它没有给出三条前提中的任何一条。
-/
def FarEndIdentityBoundary_statement
    (rows : FarEndIdentityBoundaryRows) : Prop :=
  FarEndIdentityBoundary_identityPreservesFiniteEnergy rows ->
    FarEndIdentityBoundary_zeroRowsReachIdentity rows ->
      FarEndIdentityBoundary_energyUnityFixedHalf rows ->
        ConstructiveRH

def farEndIdentityBoundary
    (rows : FarEndIdentityBoundaryRows) : BoundaryLedgerEntry where
  reason := BoundaryReason.farEndBoundary
  statement := FarEndIdentityBoundary_statement rows

/--
素 resonance chord 的有限节点。`resonance` 与 `chord` 是路线标签;
kernel 端这里只保存 finite list 节点和 prime-window membership。
-/
structure PrimeResonanceNode where
  prime : Nat
  layer : Nat

structure PrimeResonanceFamily where
  nodes : List PrimeResonanceNode
  window : PrimeWindow
  nonempty : nodes ≠ []
  node_mem_window :
    (node : PrimeResonanceNode) -> node ∈ nodes -> window.mem node.prime

/--
prime resonance no-hair 边界的行数据。`projectedSilence` 只命名一阶投影
静默行; `normalizedResonanceEnergy` 只是一条有理读回, 不声称完成分析。
-/
structure PrimeResonanceChordNoHairRows where
  stableZeroRelevant : RatComplex -> PrimeResonanceFamily -> Prop
  projectedSilence : RatComplex -> PrimeResonanceFamily -> Prop
  normalizedResonanceEnergy : RatComplex -> PrimeResonanceFamily -> RatNum

def PrimeResonanceChordNoHair_stableFamilyExists
    (rows : PrimeResonanceChordNoHairRows) : Prop :=
  ∀ s : RatComplex,
    NontrivialZetaZero s ->
      ∃ family : PrimeResonanceFamily,
        rows.stableZeroRelevant s family ∧ rows.projectedSilence s family

def PrimeResonanceChordNoHair_noHair
    (rows : PrimeResonanceChordNoHairRows) : Prop :=
  ∀ s : RatComplex,
    NontrivialZetaZero s ->
      ∀ family : PrimeResonanceFamily,
        rows.stableZeroRelevant s family ->
          BEDC.Derived.RationalUp.RatEq
            (rows.normalizedResonanceEnergy s family)
            BEDC.Derived.RationalUp.ratZero

def PrimeResonanceChordNoHair_energyCollapse
    (rows : PrimeResonanceChordNoHairRows) : Prop :=
  ∀ s : RatComplex,
    NontrivialZetaZero s ->
      ∀ family : PrimeResonanceFamily,
        rows.stableZeroRelevant s family ->
          BEDC.Derived.RationalUp.RatEq
            (rows.normalizedResonanceEnergy s family)
            BEDC.Derived.RationalUp.ratZero ->
              OnCriticalLine s

/--
boundary/no-hair: 该陈述记录“零相关有限 resonance family 存在、no-hair
归零行、归零到 fixed-half 的读回”这一条件形状。它没有证明存在性、
no-hair 或分析 collapse。
-/
def PrimeResonanceChordNoHairBoundary_statement
    (rows : PrimeResonanceChordNoHairRows) : Prop :=
  PrimeResonanceChordNoHair_stableFamilyExists rows ->
    PrimeResonanceChordNoHair_noHair rows ->
      PrimeResonanceChordNoHair_energyCollapse rows ->
        ConstructiveRH

def primeResonanceChordNoHairBoundary
    (rows : PrimeResonanceChordNoHairRows) : BoundaryLedgerEntry where
  reason := BoundaryReason.noHairBoundary
  statement := PrimeResonanceChordNoHairBoundary_statement rows

/--
Hamiltonian resonance island 边界的行数据。`Hamiltonian`、`island`、
`unitary` 和 `variance` 在这里都是 vision 的有限谱路线标签;
Lean 侧只登记有限 family、投影静默与有理方差读回的未证明边界形状。
-/
structure HamiltonianResonanceIslandRows where
  finiteDiagonalIsland : PrimeResonanceFamily -> Prop
  projectedSilence : RatComplex -> PrimeResonanceFamily -> Prop
  stableZeroIsland : RatComplex -> PrimeResonanceFamily -> Prop
  centeredVarianceEnergy : RatComplex -> PrimeResonanceFamily -> RatNum

def HamiltonianResonanceIsland_stableIslandExists
    (rows : HamiltonianResonanceIslandRows) : Prop :=
  ∀ s : RatComplex,
    NontrivialZetaZero s ->
      ∃ family : PrimeResonanceFamily,
        rows.finiteDiagonalIsland family ∧
          rows.projectedSilence s family ∧
            rows.stableZeroIsland s family

def HamiltonianResonanceIsland_noHair
    (rows : HamiltonianResonanceIslandRows) : Prop :=
  ∀ s : RatComplex,
    NontrivialZetaZero s ->
      ∀ family : PrimeResonanceFamily,
        rows.finiteDiagonalIsland family ->
          rows.stableZeroIsland s family ->
            BEDC.Derived.RationalUp.RatEq
              (rows.centeredVarianceEnergy s family)
              BEDC.Derived.RationalUp.ratZero

def HamiltonianResonanceIsland_varianceCollapse
    (rows : HamiltonianResonanceIslandRows) : Prop :=
  ∀ s : RatComplex,
    NontrivialZetaZero s ->
      ∀ family : PrimeResonanceFamily,
        rows.finiteDiagonalIsland family ->
          rows.stableZeroIsland s family ->
            BEDC.Derived.RationalUp.RatEq
              (rows.centeredVarianceEnergy s family)
              BEDC.Derived.RationalUp.ratZero ->
                OnCriticalLine s

/--
boundary/Hamiltonian-resonance: 该陈述只保存有限谱岛路线的条件证明负载。
它不构造 self-adjoint operator、谱定理、全局 Hamiltonian 流或 RH 证明。
-/
def HamiltonianResonanceIslandBoundary_statement
    (rows : HamiltonianResonanceIslandRows) : Prop :=
  HamiltonianResonanceIsland_stableIslandExists rows ->
    HamiltonianResonanceIsland_noHair rows ->
      HamiltonianResonanceIsland_varianceCollapse rows ->
        ConstructiveRH

def hamiltonianResonanceIslandBoundary
    (rows : HamiltonianResonanceIslandRows) : BoundaryLedgerEntry where
  reason := BoundaryReason.hamiltonianResonanceBoundary
  statement := HamiltonianResonanceIslandBoundary_statement rows

def resonanceBoundaryLedger
    (farEndIdentityRows : FarEndIdentityBoundaryRows)
    (primeResonanceRows : PrimeResonanceChordNoHairRows)
    (hamiltonianRows : HamiltonianResonanceIslandRows) :
    List BoundaryLedgerEntry :=
  [ farEndIdentityBoundary farEndIdentityRows,
    primeResonanceChordNoHairBoundary primeResonanceRows,
    hamiltonianResonanceIslandBoundary hamiltonianRows ]

def boundaryLedger
    (conditionalRows : ConditionalRHSufficiencyRows)
    (completionRows : CoreCommonalityCompletionRows)
    (farEndRows : NoFarEndAbsorptionRows)
    (coverRows : ZeroRecursorCoverRows) :
    List BoundaryLedgerEntry :=
  [ conditionalRHSufficiencyBoundary conditionalRows,
    coreCommonalityCompletionBoundary completionRows,
    noFarEndAbsorptionBoundary farEndRows,
    zeroRecursorCoverBoundary coverRows ]

def boundaryLedgerWithResonance
    (conditionalRows : ConditionalRHSufficiencyRows)
    (completionRows : CoreCommonalityCompletionRows)
    (farEndRows : NoFarEndAbsorptionRows)
    (coverRows : ZeroRecursorCoverRows)
    (farEndIdentityRows : FarEndIdentityBoundaryRows)
    (primeResonanceRows : PrimeResonanceChordNoHairRows)
    (hamiltonianRows : HamiltonianResonanceIslandRows) :
    List BoundaryLedgerEntry :=
  boundaryLedger conditionalRows completionRows farEndRows coverRows ++
    resonanceBoundaryLedger farEndIdentityRows primeResonanceRows hamiltonianRows

end BEDC.Derived.RHRoute.OnticBoundaryLedger
