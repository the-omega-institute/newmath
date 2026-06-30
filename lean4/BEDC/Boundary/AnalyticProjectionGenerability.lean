import BEDC.Boundary.ArgumentPrincipleConstructive

namespace BEDC.Boundary.AnalyticProjectionGenerability

/-!
`BEDC/Boundary` 只记录解析投影与闭生成性的边界面, 不证明解析源行。
缺口包括解析延拓、局部次数或 argument-principle 输入、Rouché 型捕获,
以及投影零点行的复分析控制。当前 mathlib-free 有限 BEDC kernel 不提供
这些数据, 因此本文件只命名边界 statement, 并把每个 generability witness
保留为显式数据。
-/

inductive AnalyticProjectionSource : Type where
  | dirichletSeries
  | eulerProductConvergenceSide
  | mellinOrContourRepresentation
  | analyticContinuation
  | poleLedger
  | functionalEquation
  | completedValueProjection
  deriving DecidableEq, Repr

inductive AnalyticResidueDemand : Type where
  | positiveRealScale
  | hiddenNoncompactCoordinate
  | projectedZeroWithoutCapture
  | routingWithoutInverseLimitCompatibility
  | zeroPacketWithoutBoundaryStability
  deriving DecidableEq, Repr

structure AnalyticProjectionInterface where
  Row : Type
  analyticReadout : AnalyticProjectionSource -> Row -> Type
  zetaZero : Row -> Type
  criticalStrip : Row -> Type
  criticalLine : Row -> Type
  activeCapture : Row -> Type
  compactPhaseOrSolenoidFibre : Row -> Type
  routingCompatibility : Row -> Type
  triadicClosure : Row -> Type
  defectExtraction : Row -> Type
  boundaryStability : Row -> Type
  residueDemand : AnalyticResidueDemand -> Row -> Type

def AnalyticProjectionCarrier (I : AnalyticProjectionInterface) (row : I.Row) :
    Type :=
  Sigma (fun source : AnalyticProjectionSource => I.analyticReadout source row)

structure ClosedTriadicGenerationCertificate
    (I : AnalyticProjectionInterface) (row : I.Row) where
  activeCapture : I.activeCapture row
  compactPhaseOrSolenoidFibre : I.compactPhaseOrSolenoidFibre row
  routingCompatibility : I.routingCompatibility row
  triadicClosure : I.triadicClosure row
  defectExtraction : I.defectExtraction row
  boundaryStability : I.boundaryStability row

def ClosedGenerabilityCarrier (I : AnalyticProjectionInterface) (row : I.Row) :
    Type :=
  Sigma (fun _projection : AnalyticProjectionCarrier I row =>
    ClosedTriadicGenerationCertificate I row)

def NonGenerableAnalyticResidue
    (I : AnalyticProjectionInterface) (row : I.Row) : Type :=
  Sigma (fun demand : AnalyticResidueDemand =>
    Sigma (fun _projection : AnalyticProjectionCarrier I row =>
      Sigma (fun _needed : I.residueDemand demand row =>
        ClosedTriadicGenerationCertificate I row -> Empty)))

def ProjectionToClosedGenerabilityClaim
    (I : AnalyticProjectionInterface) : Type :=
  (row : I.Row) -> AnalyticProjectionCarrier I row ->
    ClosedGenerabilityCarrier I row

-- 这是边界 statement, 不是证明。解析投影 membership 本身不携带
-- `ClosedGenerabilityCarrier` 要求的 closed triadic certificate。
def ProjectionDoesNotSupplyClosedGenerability
    (I : AnalyticProjectionInterface) : Type :=
  ProjectionToClosedGenerabilityClaim I -> Empty

def ZetaZeroGenerabilityRow (I : AnalyticProjectionInterface) : Type :=
  (row : I.Row) -> I.zetaZero row -> I.criticalStrip row ->
    ClosedGenerabilityCarrier I row

def ClosedTriadicNoRealScaleRow (I : AnalyticProjectionInterface) : Type :=
  (row : I.Row) -> ClosedGenerabilityCarrier I row -> I.criticalLine row

structure AnalyticProjectionGenerabilityBoundarySurface
    (I : AnalyticProjectionInterface) where
  projectionCarrier : I.Row -> Type
  closedGenerabilityCarrier : I.Row -> Type
  nonGenerableResidue : I.Row -> Type
  projectionToClosedGenerabilityClaim : Type
  projectionDoesNotSupplyClosedGenerability : Type
  zetaZeroGenerabilityRow : Type
  closedTriadicNoRealScaleRow : Type

def analyticProjectionGenerability_boundary
    (I : AnalyticProjectionInterface) :
    AnalyticProjectionGenerabilityBoundarySurface I :=
  {
    projectionCarrier := AnalyticProjectionCarrier I
    closedGenerabilityCarrier := ClosedGenerabilityCarrier I
    nonGenerableResidue := NonGenerableAnalyticResidue I
    projectionToClosedGenerabilityClaim := ProjectionToClosedGenerabilityClaim I
    projectionDoesNotSupplyClosedGenerability :=
      ProjectionDoesNotSupplyClosedGenerability I
    zetaZeroGenerabilityRow := ZetaZeroGenerabilityRow I
    closedTriadicNoRealScaleRow := ClosedTriadicNoRealScaleRow I
  }

-- 只由 kernel 检查 surface shape; 这里不 inhabit generability row。
theorem analyticProjectionGenerability_boundary_zeta_row_shape
    (I : AnalyticProjectionInterface) :
    (analyticProjectionGenerability_boundary I).zetaZeroGenerabilityRow =
      ZetaZeroGenerabilityRow I := by
  rfl

end BEDC.Boundary.AnalyticProjectionGenerability
