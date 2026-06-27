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

end BEDC.Derived.RHRoute.OnticBoundaryLedger
