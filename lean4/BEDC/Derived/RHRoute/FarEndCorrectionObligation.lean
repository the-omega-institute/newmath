import BEDC.Derived.RHRoute.FarEndUnityNormalization

namespace BEDC.Derived.RHRoute.FarEndCorrectionObligation

open BEDC.Derived.RationalUp

abbrev PrimeWindow :=
  BEDC.Derived.RHRoute.FinitePrimeWindow.PrimeWindow

abbrev PrimeLocalChannel :=
  BEDC.Derived.RHRoute.UnitaryBalance.PrimeLocalChannel

abbrev PrimeWindowNormalization :=
  BEDC.Derived.RHRoute.FarEndUnityNormalization.PrimeWindowNormalization

abbrev FarEndUnityNormalization :=
  BEDC.Derived.RHRoute.FarEndUnityNormalization.FarEndUnityNormalization

abbrev UnitaryBalanceSurface :=
  BEDC.Derived.RHRoute.FarEndUnityNormalization.UnitaryBalanceSurface

abbrev RatNum :=
  BEDC.Derived.RationalUp.RatNum

/--
归一化后的远端残余不是在本文件中消失的对象。它是一条有理读数,
后续校正必须以显式见证把它送回零残余。
-/
structure NormalizedResidual where
  normalization : FarEndUnityNormalization
  residual : RatNum

def CorrectsResidual (residual correction : RatNum) : Prop :=
  RatEq (ratAdd residual correction) ratZero

/--
校正义务只记录已给出的校正项和闭合见证; 不从归一化本身推出闭合。
-/
structure CorrectionObligation (row : NormalizedResidual) where
  correction : RatNum
  closes : CorrectsResidual row.residual correction

def CorrectionObligation.closedResidual {row : NormalizedResidual}
    (_obligation : CorrectionObligation row) : RatNum :=
  ratZero

theorem CorrectionObligation.satisfied {row : NormalizedResidual}
    (obligation : CorrectionObligation row) :
    CorrectsResidual row.residual obligation.correction :=
  obligation.closes

theorem CorrectionObligation.residual_eq_zero_after_correction
    {row : NormalizedResidual} (obligation : CorrectionObligation row) :
    RatEq (ratAdd row.residual obligation.correction)
      obligation.closedResidual :=
  obligation.closes

/-- 一层筛塔校正把源层残余、校正项和目标层残余的读回关系分开记录。 -/
structure SieveCorrectionLayer where
  source : NormalizedResidual
  target : NormalizedResidual
  correction : RatNum
  target_residual_readback :
    RatEq target.residual (ratAdd source.residual correction)

def SieveCorrectionLayerObligation (layer : SieveCorrectionLayer) : Prop :=
  CorrectsResidual layer.source.residual layer.correction

structure SieveCorrectionWitness (layer : SieveCorrectionLayer) where
  closes_source : SieveCorrectionLayerObligation layer

theorem SieveCorrectionWitness.target_residual_zero
    {layer : SieveCorrectionLayer} (witness : SieveCorrectionWitness layer) :
    RatEq layer.target.residual ratZero :=
  RatEq_trans layer.target.residual
    (ratAdd layer.source.residual layer.correction)
    ratZero
    layer.target_residual_readback
    witness.closes_source

def SieveCorrectionLayer.asObligation (layer : SieveCorrectionLayer)
    (witness : SieveCorrectionWitness layer) :
    CorrectionObligation layer.source where
  correction := layer.correction
  closes := witness.closes_source

theorem SieveCorrectionLayer.asObligation_satisfied
    (layer : SieveCorrectionLayer) (witness : SieveCorrectionWitness layer) :
    CorrectsResidual layer.source.residual
      (layer.asObligation witness).correction :=
  (layer.asObligation witness).closes

/--
校正链用 List 记录有限层。`terminal` 是链末读数; `terminal_readback`
和 `terminal_zero` 均为外部义务见证, 本文件只验证它们可被统一消费。
-/
structure CorrectionChain where
  seed : NormalizedResidual
  layers : List SieveCorrectionLayer
  terminal : NormalizedResidual
  terminal_readback : RatEq terminal.residual seed.residual
  terminal_zero : RatEq terminal.residual ratZero

def CorrectionChainObligationSatisfied (chain : CorrectionChain) : Prop :=
  RatEq chain.seed.residual ratZero

theorem CorrectionChain.seed_zero (chain : CorrectionChain) :
    CorrectionChainObligationSatisfied chain :=
  RatEq_trans chain.seed.residual chain.terminal.residual ratZero
    (RatEq_symm chain.terminal_readback)
    chain.terminal_zero

structure SieveTowerOneStep where
  layer : SieveCorrectionLayer
  witness : SieveCorrectionWitness layer

def SieveTowerOneStep.sourceObligation (tower : SieveTowerOneStep) :
    CorrectionObligation tower.layer.source :=
  tower.layer.asObligation tower.witness

theorem SieveTowerOneStep.source_obligation_satisfied
    (tower : SieveTowerOneStep) :
    CorrectsResidual tower.layer.source.residual
      tower.sourceObligation.correction :=
  tower.sourceObligation.closes

theorem SieveTowerOneStep.target_residual_zero
    (tower : SieveTowerOneStep) :
    RatEq tower.layer.target.residual ratZero :=
  SieveCorrectionWitness.target_residual_zero tower.witness

theorem normalized_residual_keeps_unit_norm (row : NormalizedResidual) :
    RatEq
      (BEDC.Derived.RHRoute.UnitaryBalance.squaredNormOnWindow
        row.normalization.toUnitaryBalanceSurface.channel)
      ratOne :=
  row.normalization.unit_norm_transfers

theorem normalized_residual_far_end_not_internalized
    (row : NormalizedResidual) :
    BEDC.Derived.TranscendentalFarEndUp.farEndSocketElementProjection
      BEDC.Derived.LocatedReal.RatMetricKitConcrete
      row.normalization.socket = none :=
  row.normalization.far_end_not_internalized

end BEDC.Derived.RHRoute.FarEndCorrectionObligation
