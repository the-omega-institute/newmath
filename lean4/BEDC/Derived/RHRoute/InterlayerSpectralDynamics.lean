import BEDC.Derived.RHRoute.RecursiveSpectralZeroHierarchy
import BEDC.Derived.RHRoute.ZetaBoxEvaluator

namespace BEDC.Derived.RHRoute.InterlayerSpectralDynamics

open BEDC.Derived.RHRoute.RecursiveSpectralZeroHierarchy
open BEDC.Derived.RHRoute.ZeroGenerationInitiality
open BEDC.Derived.RHRoute.RecursiveTower
open BEDC.Derived.RHRoute.FinitePrimeWindow

abbrev BoxGauge :=
  BEDC.Derived.RHRoute.ZetaBoxEvaluator.BoxGauge

abbrev CriticalStripInput :=
  BEDC.Derived.RHRoute.ZetaBoxEvaluator.CriticalStripInput

abbrev ZetaBoxEvaluator :=
  BEDC.Derived.RHRoute.ZetaBoxEvaluator.ZetaBoxEvaluator

abbrev ZetaPrecisionPacket {G : BoxGauge} {s : CriticalStripInput}
    (E : ZetaBoxEvaluator G s) (k : Nat) :=
  BEDC.Derived.RHRoute.ZetaBoxEvaluator.ZetaPrecisionPacket E k

-- 这里的 spectral/dynamics 是 vision 角色名；Lean 端只记录有限层构造子的转移。
structure InterlayerDynamics (signature : RHFreeZeroSignature) where
  map : SpectralZeroLayer signature -> SpectralZeroLayer signature
  generatedMap : GeneratedZero signature -> GeneratedZero signature
  traceMap : List TraceEvent -> List TraceEvent
  depthMap : Nat -> Nat
  generated_preserved :
    ∀ z : SpectralZeroLayer signature,
      forgetToGeneratedZero (map z) = generatedMap (forgetToGeneratedZero z)
  trace_preserved :
    ∀ z : SpectralZeroLayer signature,
      layerTrace (map z) = traceMap (layerTrace z)
  depth_preserved :
    ∀ z : SpectralZeroLayer signature,
      layerDepth (map z) = depthMap (layerDepth z)

namespace InterlayerDynamics

def identity (signature : RHFreeZeroSignature) :
    InterlayerDynamics signature where
  map := fun z => z
  generatedMap := fun z => z
  traceMap := fun trace => trace
  depthMap := fun depth => depth
  generated_preserved := by
    intro z
    rfl
  trace_preserved := by
    intro z
    rfl
  depth_preserved := by
    intro z
    rfl

def compose {signature : RHFreeZeroSignature}
    (outer inner : InterlayerDynamics signature) :
    InterlayerDynamics signature where
  map := fun z => outer.map (inner.map z)
  generatedMap := fun z => outer.generatedMap (inner.generatedMap z)
  traceMap := fun trace => outer.traceMap (inner.traceMap trace)
  depthMap := fun depth => outer.depthMap (inner.depthMap depth)
  generated_preserved := by
    intro z
    calc
      forgetToGeneratedZero (outer.map (inner.map z))
          = outer.generatedMap (forgetToGeneratedZero (inner.map z)) :=
            outer.generated_preserved (inner.map z)
      _ = outer.generatedMap
            (inner.generatedMap (forgetToGeneratedZero z)) := by
            exact congrArg outer.generatedMap (inner.generated_preserved z)
  trace_preserved := by
    intro z
    calc
      layerTrace (outer.map (inner.map z))
          = outer.traceMap (layerTrace (inner.map z)) :=
            outer.trace_preserved (inner.map z)
      _ = outer.traceMap (inner.traceMap (layerTrace z)) := by
            exact congrArg outer.traceMap (inner.trace_preserved z)
  depth_preserved := by
    intro z
    calc
      layerDepth (outer.map (inner.map z))
          = outer.depthMap (layerDepth (inner.map z)) :=
            outer.depth_preserved (inner.map z)
      _ = outer.depthMap (inner.depthMap (layerDepth z)) := by
            exact congrArg outer.depthMap (inner.depth_preserved z)

theorem generated_invariant {signature : RHFreeZeroSignature}
    (D : InterlayerDynamics signature) (z : SpectralZeroLayer signature) :
    forgetToGeneratedZero (D.map z) =
      D.generatedMap (forgetToGeneratedZero z) := by
  exact D.generated_preserved z

theorem trace_invariant {signature : RHFreeZeroSignature}
    (D : InterlayerDynamics signature) (z : SpectralZeroLayer signature) :
    layerTrace (D.map z) = D.traceMap (layerTrace z) := by
  exact D.trace_preserved z

theorem depth_invariant {signature : RHFreeZeroSignature}
    (D : InterlayerDynamics signature) (z : SpectralZeroLayer signature) :
    layerDepth (D.map z) = D.depthMap (layerDepth z) := by
  exact D.depth_preserved z

end InterlayerDynamics

def functionalMirrorDynamics (signature : RHFreeZeroSignature) :
    InterlayerDynamics signature where
  map := fun z => SpectralZeroLayer.functionalMirror z
  generatedMap := fun z => GeneratedZero.functionalMirror z
  traceMap := fun trace => trace
  depthMap := fun depth => Nat.succ depth
  generated_preserved := by
    intro z
    rfl
  trace_preserved := by
    intro z
    rfl
  depth_preserved := by
    intro z
    rfl

def conjugationTransportDynamics (signature : RHFreeZeroSignature) :
    InterlayerDynamics signature where
  map := fun z => SpectralZeroLayer.conjugationTransport z
  generatedMap := fun z => GeneratedZero.conjugationTransport z
  traceMap := fun trace => trace
  depthMap := fun depth => Nat.succ depth
  generated_preserved := by
    intro z
    rfl
  trace_preserved := by
    intro z
    rfl
  depth_preserved := by
    intro z
    rfl

def classifierTransportDynamics (signature : RHFreeZeroSignature)
    (tag : Nat) : InterlayerDynamics signature where
  map := fun z => SpectralZeroLayer.classifierTransport tag z
  generatedMap := fun z => GeneratedZero.classifierTransport tag z
  traceMap := fun trace => trace
  depthMap := fun depth => Nat.succ depth
  generated_preserved := by
    intro z
    rfl
  trace_preserved := by
    intro z
    rfl
  depth_preserved := by
    intro z
    rfl

def analyticGlueLeftDynamics {signature : RHFreeZeroSignature}
    (right : SpectralZeroLayer signature) :
    InterlayerDynamics signature where
  map := fun left => SpectralZeroLayer.analyticGlue left right
  generatedMap := fun left =>
    GeneratedZero.analyticGlue left (forgetToGeneratedZero right)
  traceMap := fun trace => trace ++ layerTrace right
  depthMap := fun depth => Nat.succ (depthJoin depth (layerDepth right))
  generated_preserved := by
    intro z
    rfl
  trace_preserved := by
    intro z
    rfl
  depth_preserved := by
    intro z
    rfl

def compatibleLimitSealDynamics (signature : RHFreeZeroSignature)
    (fuel : Nat) : InterlayerDynamics signature where
  map := fun z => SpectralZeroLayer.compatibleLimitSeal fuel z
  generatedMap := fun z => GeneratedZero.compatibleLimitSeal fuel z
  traceMap := fun trace => trace
  depthMap := fun depth => Nat.succ depth
  generated_preserved := by
    intro z
    rfl
  trace_preserved := by
    intro z
    rfl
  depth_preserved := by
    intro z
    rfl

def ledgerReplayDynamics (signature : RHFreeZeroSignature)
    (trace : List TraceEvent) : InterlayerDynamics signature where
  map := fun z => SpectralZeroLayer.ledgerReplay z trace
  generatedMap := fun z => GeneratedZero.ledgerReplay z trace
  traceMap := fun existing => trace ++ existing
  depthMap := fun depth => Nat.succ depth
  generated_preserved := by
    intro z
    rfl
  trace_preserved := by
    intro z
    rfl
  depth_preserved := by
    intro z
    rfl

def finiteWindowCloseDynamics (signature : RHFreeZeroSignature)
    (window : PrimeWindow) : InterlayerDynamics signature where
  map := fun z => SpectralZeroLayer.finiteWindowClose window z
  generatedMap := fun z => GeneratedZero.finiteWindowClose window z
  traceMap := fun trace => trace
  depthMap := fun depth => Nat.succ depth
  generated_preserved := by
    intro z
    rfl
  trace_preserved := by
    intro z
    rfl
  depth_preserved := by
    intro z
    rfl

def recursiveTowerReadbackDynamics (signature : RHFreeZeroSignature)
    (event : TraceEvent) : InterlayerDynamics signature where
  map := fun z => SpectralZeroLayer.recursiveTowerReadback event z
  generatedMap := fun z => GeneratedZero.recursiveTowerReadback event z
  traceMap := fun trace => event :: trace
  depthMap := fun depth => Nat.succ depth
  generated_preserved := by
    intro z
    rfl
  trace_preserved := by
    intro z
    rfl
  depth_preserved := by
    intro z
    rfl

def nonCollapseGuardDynamics (signature : RHFreeZeroSignature)
    (budget : Nat) : InterlayerDynamics signature where
  map := fun z => SpectralZeroLayer.nonCollapseGuard budget z
  generatedMap := fun z => GeneratedZero.nonCollapseGuard budget z
  traceMap := fun trace => trace
  depthMap := fun depth => Nat.succ depth
  generated_preserved := by
    intro z
    rfl
  trace_preserved := by
    intro z
    rfl
  depth_preserved := by
    intro z
    rfl

def towerReadbackDynamics (signature : RHFreeZeroSignature) :
    Nat -> InterlayerDynamics signature
  | 0 => InterlayerDynamics.identity signature
  | Nat.succ n =>
      InterlayerDynamics.compose
        (recursiveTowerReadbackDynamics signature
          (TraceEvent.readback (Nat.succ n) n))
        (towerReadbackDynamics signature n)

theorem towerReadbackDynamics_map_base {signature : RHFreeZeroSignature} :
    (fuel : Nat) -> (z : GeneratedZero signature) ->
      (towerReadbackDynamics signature fuel).map (SpectralZeroLayer.base z) =
        towerReadbackLayer fuel z
  | 0, _z => rfl
  | Nat.succ n, z => by
      change
        SpectralZeroLayer.recursiveTowerReadback
            (TraceEvent.readback (Nat.succ n) n)
            ((towerReadbackDynamics signature n).map
              (SpectralZeroLayer.base z)) =
          SpectralZeroLayer.recursiveTowerReadback
            (TraceEvent.readback (Nat.succ n) n)
            (towerReadbackLayer n z)
      exact
        congrArg
          (SpectralZeroLayer.recursiveTowerReadback
            (TraceEvent.readback (Nat.succ n) n))
          (towerReadbackDynamics_map_base n z)

theorem towerReadbackDynamics_depth {signature : RHFreeZeroSignature}
    (fuel : Nat) (z : GeneratedZero signature) :
    layerDepth
      ((towerReadbackDynamics signature fuel).map
        (SpectralZeroLayer.base z)) = fuel := by
  calc
    layerDepth
        ((towerReadbackDynamics signature fuel).map
          (SpectralZeroLayer.base z))
        = layerDepth (towerReadbackLayer fuel z) := by
          exact congrArg layerDepth (towerReadbackDynamics_map_base fuel z)
    _ = fuel := towerReadbackLayer_depth fuel z

theorem towerReadbackDynamics_forget {signature : RHFreeZeroSignature}
    (fuel : Nat) (z : GeneratedZero signature) :
    forgetToGeneratedZero
      ((towerReadbackDynamics signature fuel).map
        (SpectralZeroLayer.base z)) =
      towerReadbackGenerated fuel z := by
  calc
    forgetToGeneratedZero
        ((towerReadbackDynamics signature fuel).map
          (SpectralZeroLayer.base z))
        = forgetToGeneratedZero (towerReadbackLayer fuel z) := by
          exact
            congrArg forgetToGeneratedZero
              (towerReadbackDynamics_map_base fuel z)
    _ = towerReadbackGenerated fuel z :=
          towerReadbackLayer_forget fuel z

structure ZetaInterlayerState (G : BoxGauge)
    (s : CriticalStripInput) (signature : RHFreeZeroSignature) where
  layer : SpectralZeroLayer signature
  evaluator : ZetaBoxEvaluator G s

def applyDynamicsToZetaState {G : BoxGauge} {s : CriticalStripInput}
    {signature : RHFreeZeroSignature}
    (D : InterlayerDynamics signature)
    (state : ZetaInterlayerState G s signature) :
    ZetaInterlayerState G s signature where
  layer := D.map state.layer
  evaluator := state.evaluator

theorem applyDynamicsToZetaState_evaluator {G : BoxGauge}
    {s : CriticalStripInput} {signature : RHFreeZeroSignature}
    (D : InterlayerDynamics signature)
    (state : ZetaInterlayerState G s signature) :
    (applyDynamicsToZetaState D state).evaluator = state.evaluator := by
  rfl

theorem zetaPrecision_after_interlayerDynamics {G : BoxGauge}
    {s : CriticalStripInput} {signature : RHFreeZeroSignature}
    (D : InterlayerDynamics signature)
    (state : ZetaInterlayerState G s signature) (k : Nat) :
    ∃ packet :
        ZetaPrecisionPacket
          (applyDynamicsToZetaState D state).evaluator k,
      G.fits packet.zetaBox k := by
  exact
    BEDC.Derived.RHRoute.ZetaBoxEvaluator.zetaBoxEvaluableToPrecision
      state.evaluator k

theorem applyDynamics_preserves_layer_invariants {G : BoxGauge}
    {s : CriticalStripInput} {signature : RHFreeZeroSignature}
    (D : InterlayerDynamics signature)
    (state : ZetaInterlayerState G s signature) :
    forgetToGeneratedZero (applyDynamicsToZetaState D state).layer =
        D.generatedMap (forgetToGeneratedZero state.layer) ∧
      layerTrace (applyDynamicsToZetaState D state).layer =
        D.traceMap (layerTrace state.layer) ∧
      layerDepth (applyDynamicsToZetaState D state).layer =
        D.depthMap (layerDepth state.layer) := by
  exact
    And.intro
      (D.generated_preserved state.layer)
      (And.intro
        (D.trace_preserved state.layer)
        (D.depth_preserved state.layer))

end BEDC.Derived.RHRoute.InterlayerSpectralDynamics
