import BEDC.Derived.RHRoute.ZeroGenerationInitiality

namespace BEDC.Derived.RHRoute.RecursiveSpectralZeroHierarchy

open BEDC.Derived.RHRoute.FinitePrimeWindow
open BEDC.Derived.RHRoute.RecursiveTower
open BEDC.Derived.RHRoute.ZeroGenerationInitiality

-- 这里的 spectral 是 vision 角色名；Lean 端只记录有限构造链。
def depthJoin : Nat -> Nat -> Nat
  | 0, b => b
  | Nat.succ a, 0 => Nat.succ a
  | Nat.succ a, Nat.succ b => Nat.succ (depthJoin a b)

theorem depthJoin_self : (n : Nat) -> depthJoin n n = n
  | 0 => rfl
  | Nat.succ n => by
      change Nat.succ (depthJoin n n) = Nat.succ n
      exact congrArg Nat.succ (depthJoin_self n)

theorem congrArgTwo {α : Type u} {β : Type v} {γ : Type w}
    (f : α -> β -> γ) {a a' : α} {b b' : β} :
    a = a' -> b = b' -> f a b = f a' b' := by
  intro left right
  cases left
  cases right
  rfl

inductive SpectralZeroLayer (signature : RHFreeZeroSignature) : Type where
  | base : GeneratedZero signature -> SpectralZeroLayer signature
  | functionalMirror :
      SpectralZeroLayer signature -> SpectralZeroLayer signature
  | conjugationTransport :
      SpectralZeroLayer signature -> SpectralZeroLayer signature
  | classifierTransport :
      Nat -> SpectralZeroLayer signature -> SpectralZeroLayer signature
  | analyticGlue :
      SpectralZeroLayer signature -> SpectralZeroLayer signature ->
        SpectralZeroLayer signature
  | compatibleLimitSeal :
      Nat -> SpectralZeroLayer signature -> SpectralZeroLayer signature
  | ledgerReplay :
      SpectralZeroLayer signature -> List TraceEvent -> SpectralZeroLayer signature
  | finiteWindowClose :
      PrimeWindow -> SpectralZeroLayer signature -> SpectralZeroLayer signature
  | recursiveTowerReadback :
      TraceEvent -> SpectralZeroLayer signature -> SpectralZeroLayer signature
  | nonCollapseGuard :
      Nat -> SpectralZeroLayer signature -> SpectralZeroLayer signature

def layerDepth {signature : RHFreeZeroSignature} :
    SpectralZeroLayer signature -> Nat
  | SpectralZeroLayer.base _ => 0
  | SpectralZeroLayer.functionalMirror z =>
      Nat.succ (layerDepth z)
  | SpectralZeroLayer.conjugationTransport z =>
      Nat.succ (layerDepth z)
  | SpectralZeroLayer.classifierTransport _ z =>
      Nat.succ (layerDepth z)
  | SpectralZeroLayer.analyticGlue left right =>
      Nat.succ (depthJoin (layerDepth left) (layerDepth right))
  | SpectralZeroLayer.compatibleLimitSeal _ z =>
      Nat.succ (layerDepth z)
  | SpectralZeroLayer.ledgerReplay z _ =>
      Nat.succ (layerDepth z)
  | SpectralZeroLayer.finiteWindowClose _ z =>
      Nat.succ (layerDepth z)
  | SpectralZeroLayer.recursiveTowerReadback _ z =>
      Nat.succ (layerDepth z)
  | SpectralZeroLayer.nonCollapseGuard _ z =>
      Nat.succ (layerDepth z)

def AtDepth {signature : RHFreeZeroSignature}
    (level : Nat) (z : SpectralZeroLayer signature) : Prop :=
  layerDepth z = level

theorem atDepth_self {signature : RHFreeZeroSignature}
    (z : SpectralZeroLayer signature) :
    AtDepth (layerDepth z) z := by
  rfl

theorem layerDepth_eq_level {signature : RHFreeZeroSignature}
    {level : Nat} {z : SpectralZeroLayer signature} :
    AtDepth level z -> layerDepth z = level := by
  intro depth
  exact depth

def layerTrace {signature : RHFreeZeroSignature} :
    SpectralZeroLayer signature -> List TraceEvent
  | SpectralZeroLayer.base _ => []
  | SpectralZeroLayer.functionalMirror z =>
      layerTrace z
  | SpectralZeroLayer.conjugationTransport z =>
      layerTrace z
  | SpectralZeroLayer.classifierTransport _ z =>
      layerTrace z
  | SpectralZeroLayer.analyticGlue left right =>
      layerTrace left ++ layerTrace right
  | SpectralZeroLayer.compatibleLimitSeal _ z =>
      layerTrace z
  | SpectralZeroLayer.ledgerReplay z trace =>
      trace ++ layerTrace z
  | SpectralZeroLayer.finiteWindowClose _ z =>
      layerTrace z
  | SpectralZeroLayer.recursiveTowerReadback event z =>
      event :: layerTrace z
  | SpectralZeroLayer.nonCollapseGuard _ z =>
      layerTrace z

def forgetToGeneratedZero {signature : RHFreeZeroSignature} :
    SpectralZeroLayer signature -> GeneratedZero signature
  | SpectralZeroLayer.base z => z
  | SpectralZeroLayer.functionalMirror z =>
      GeneratedZero.functionalMirror (forgetToGeneratedZero z)
  | SpectralZeroLayer.conjugationTransport z =>
      GeneratedZero.conjugationTransport (forgetToGeneratedZero z)
  | SpectralZeroLayer.classifierTransport tag z =>
      GeneratedZero.classifierTransport tag (forgetToGeneratedZero z)
  | SpectralZeroLayer.analyticGlue left right =>
      GeneratedZero.analyticGlue
        (forgetToGeneratedZero left) (forgetToGeneratedZero right)
  | SpectralZeroLayer.compatibleLimitSeal fuel z =>
      GeneratedZero.compatibleLimitSeal fuel (forgetToGeneratedZero z)
  | SpectralZeroLayer.ledgerReplay z trace =>
      GeneratedZero.ledgerReplay (forgetToGeneratedZero z) trace
  | SpectralZeroLayer.finiteWindowClose window z =>
      GeneratedZero.finiteWindowClose window (forgetToGeneratedZero z)
  | SpectralZeroLayer.recursiveTowerReadback event z =>
      GeneratedZero.recursiveTowerReadback event (forgetToGeneratedZero z)
  | SpectralZeroLayer.nonCollapseGuard budget z =>
      GeneratedZero.nonCollapseGuard budget (forgetToGeneratedZero z)

theorem recursiveTowerReadback_forget {signature : RHFreeZeroSignature}
    (event : TraceEvent) (z : SpectralZeroLayer signature) :
    forgetToGeneratedZero (SpectralZeroLayer.recursiveTowerReadback event z) =
      GeneratedZero.recursiveTowerReadback event (forgetToGeneratedZero z) := by
  rfl

theorem recursiveTowerReadback_depth {signature : RHFreeZeroSignature}
    (event : TraceEvent) (z : SpectralZeroLayer signature) :
    layerDepth (SpectralZeroLayer.recursiveTowerReadback event z) =
      Nat.succ (layerDepth z) := by
  rfl

theorem recursiveTowerReadback_atDepth {signature : RHFreeZeroSignature}
    {level : Nat} (event : TraceEvent) (z : SpectralZeroLayer signature) :
    AtDepth level z ->
      AtDepth (Nat.succ level) (SpectralZeroLayer.recursiveTowerReadback event z) := by
  intro depth
  cases depth
  rfl

structure LayeredZero (signature : RHFreeZeroSignature) where
  zero : SpectralZeroLayer signature

namespace LayeredZero

def depth {signature : RHFreeZeroSignature}
    (z : LayeredZero signature) : Nat :=
  layerDepth z.zero

def forget {signature : RHFreeZeroSignature}
    (z : LayeredZero signature) : GeneratedZero signature :=
  forgetToGeneratedZero z.zero

theorem depth_sound {signature : RHFreeZeroSignature}
    (z : LayeredZero signature) :
    layerDepth z.zero = z.depth := by
  rfl

end LayeredZero

def generatedZeroDepthAlgebra (signature : RHFreeZeroSignature) :
    ZeroAlgebra signature Nat where
  alg
    | ZeroSigF.primeLocal _ _ _ => 0
    | ZeroSigF.functionalMirror n => Nat.succ n
    | ZeroSigF.conjugationTransport n => Nat.succ n
    | ZeroSigF.classifierTransport _ n => Nat.succ n
    | ZeroSigF.analyticGlue left right =>
        Nat.succ (depthJoin left right)
    | ZeroSigF.compatibleLimitSeal _ n => Nat.succ n
    | ZeroSigF.ledgerReplay n _ => Nat.succ n
    | ZeroSigF.finiteWindowClose _ n => Nat.succ n
    | ZeroSigF.recursiveTowerReadback _ n => Nat.succ n
    | ZeroSigF.nonCollapseGuard _ n => Nat.succ n

def generatedZeroConstructorDepth {signature : RHFreeZeroSignature}
    (z : GeneratedZero signature) : Nat :=
  GeneratedZero.fold (generatedZeroDepthAlgebra signature) z

theorem generatedZeroConstructorDepth_hom
    (signature : RHFreeZeroSignature) :
    IsZeroAlgebraHom (generatedZeroDepthAlgebra signature)
      (generatedZeroConstructorDepth (signature := signature)) :=
  (generatedZero_initiality (generatedZeroDepthAlgebra signature)).left

theorem generatedZeroConstructorDepth_unique
    {signature : RHFreeZeroSignature} (f : GeneratedZero signature -> Nat)
    (hom : IsZeroAlgebraHom (generatedZeroDepthAlgebra signature) f) :
    ∀ z : GeneratedZero signature,
      f z = generatedZeroConstructorDepth z := by
  exact
    (generatedZero_initiality
      (generatedZeroDepthAlgebra signature)).right f hom

def layeredZeroAlgebra (signature : RHFreeZeroSignature) :
    ZeroAlgebra signature (LayeredZero signature) where
  alg
    | ZeroSigF.primeLocal window p member =>
        { zero :=
            SpectralZeroLayer.base
              (GeneratedZero.primeLocal window p member) }
    | ZeroSigF.functionalMirror z =>
        { zero := SpectralZeroLayer.functionalMirror z.zero }
    | ZeroSigF.conjugationTransport z =>
        { zero := SpectralZeroLayer.conjugationTransport z.zero }
    | ZeroSigF.classifierTransport tag z =>
        { zero := SpectralZeroLayer.classifierTransport tag z.zero }
    | ZeroSigF.analyticGlue left right =>
        { zero := SpectralZeroLayer.analyticGlue left.zero right.zero }
    | ZeroSigF.compatibleLimitSeal fuel z =>
        { zero := SpectralZeroLayer.compatibleLimitSeal fuel z.zero }
    | ZeroSigF.ledgerReplay z trace =>
        { zero := SpectralZeroLayer.ledgerReplay z.zero trace }
    | ZeroSigF.finiteWindowClose window z =>
        { zero := SpectralZeroLayer.finiteWindowClose window z.zero }
    | ZeroSigF.recursiveTowerReadback event z =>
        { zero := SpectralZeroLayer.recursiveTowerReadback event z.zero }
    | ZeroSigF.nonCollapseGuard budget z =>
        { zero := SpectralZeroLayer.nonCollapseGuard budget z.zero }

def generatedZeroLayered {signature : RHFreeZeroSignature}
    (z : GeneratedZero signature) : LayeredZero signature :=
  GeneratedZero.fold (layeredZeroAlgebra signature) z

theorem generatedZeroLayered_hom (signature : RHFreeZeroSignature) :
    IsZeroAlgebraHom (layeredZeroAlgebra signature)
      (generatedZeroLayered (signature := signature)) :=
  (generatedZero_initiality (layeredZeroAlgebra signature)).left

theorem generatedZeroLayered_unique
    {signature : RHFreeZeroSignature}
    (f : GeneratedZero signature -> LayeredZero signature)
    (hom : IsZeroAlgebraHom (layeredZeroAlgebra signature) f) :
    ∀ z : GeneratedZero signature, f z = generatedZeroLayered z := by
  exact
    (generatedZero_initiality
      (layeredZeroAlgebra signature)).right f hom

theorem generatedZeroLayered_forget {signature : RHFreeZeroSignature} :
    ∀ z : GeneratedZero signature,
      LayeredZero.forget (generatedZeroLayered z) = z := by
  intro z
  induction z with
  | primeLocal window p member =>
      rfl
  | functionalMirror z ih =>
      change
        GeneratedZero.functionalMirror
            (LayeredZero.forget (generatedZeroLayered z)) =
          GeneratedZero.functionalMirror z
      exact congrArg GeneratedZero.functionalMirror ih
  | conjugationTransport z ih =>
      change
        GeneratedZero.conjugationTransport
            (LayeredZero.forget (generatedZeroLayered z)) =
          GeneratedZero.conjugationTransport z
      exact congrArg GeneratedZero.conjugationTransport ih
  | classifierTransport tag z ih =>
      change
        GeneratedZero.classifierTransport tag
            (LayeredZero.forget (generatedZeroLayered z)) =
          GeneratedZero.classifierTransport tag z
      exact congrArg (GeneratedZero.classifierTransport tag) ih
  | analyticGlue left right ihLeft ihRight =>
      change
        GeneratedZero.analyticGlue
            (LayeredZero.forget (generatedZeroLayered left))
            (LayeredZero.forget (generatedZeroLayered right)) =
          GeneratedZero.analyticGlue left right
      exact congrArgTwo GeneratedZero.analyticGlue ihLeft ihRight
  | compatibleLimitSeal fuel z ih =>
      change
        GeneratedZero.compatibleLimitSeal fuel
            (LayeredZero.forget (generatedZeroLayered z)) =
          GeneratedZero.compatibleLimitSeal fuel z
      exact congrArg (GeneratedZero.compatibleLimitSeal fuel) ih
  | ledgerReplay z trace ih =>
      change
        GeneratedZero.ledgerReplay
            (LayeredZero.forget (generatedZeroLayered z)) trace =
          GeneratedZero.ledgerReplay z trace
      exact congrArg (fun g => GeneratedZero.ledgerReplay g trace) ih
  | finiteWindowClose window z ih =>
      change
        GeneratedZero.finiteWindowClose window
            (LayeredZero.forget (generatedZeroLayered z)) =
          GeneratedZero.finiteWindowClose window z
      exact congrArg (GeneratedZero.finiteWindowClose window) ih
  | recursiveTowerReadback event z ih =>
      change
        GeneratedZero.recursiveTowerReadback event
            (LayeredZero.forget (generatedZeroLayered z)) =
          GeneratedZero.recursiveTowerReadback event z
      exact congrArg (GeneratedZero.recursiveTowerReadback event) ih
  | nonCollapseGuard budget z ih =>
      change
        GeneratedZero.nonCollapseGuard budget
            (LayeredZero.forget (generatedZeroLayered z)) =
          GeneratedZero.nonCollapseGuard budget z
      exact congrArg (GeneratedZero.nonCollapseGuard budget) ih

theorem generatedZeroLayered_depth_matches_constructorDepth
    {signature : RHFreeZeroSignature} :
    ∀ z : GeneratedZero signature,
      (generatedZeroLayered z).depth = generatedZeroConstructorDepth z := by
  intro z
  induction z with
  | primeLocal window p member =>
      rfl
  | functionalMirror z ih =>
      change
        Nat.succ (generatedZeroLayered z).depth =
          Nat.succ (generatedZeroConstructorDepth z)
      exact congrArg Nat.succ ih
  | conjugationTransport z ih =>
      change
        Nat.succ (generatedZeroLayered z).depth =
          Nat.succ (generatedZeroConstructorDepth z)
      exact congrArg Nat.succ ih
  | classifierTransport tag z ih =>
      change
        Nat.succ (generatedZeroLayered z).depth =
          Nat.succ (generatedZeroConstructorDepth z)
      exact congrArg Nat.succ ih
  | analyticGlue left right ihLeft ihRight =>
      change
        Nat.succ
            (depthJoin (generatedZeroLayered left).depth
              (generatedZeroLayered right).depth) =
          Nat.succ
            (depthJoin (generatedZeroConstructorDepth left)
              (generatedZeroConstructorDepth right))
      exact congrArg Nat.succ (congrArgTwo depthJoin ihLeft ihRight)
  | compatibleLimitSeal fuel z ih =>
      change
        Nat.succ (generatedZeroLayered z).depth =
          Nat.succ (generatedZeroConstructorDepth z)
      exact congrArg Nat.succ ih
  | ledgerReplay z trace ih =>
      change
        Nat.succ (generatedZeroLayered z).depth =
          Nat.succ (generatedZeroConstructorDepth z)
      exact congrArg Nat.succ ih
  | finiteWindowClose window z ih =>
      change
        Nat.succ (generatedZeroLayered z).depth =
          Nat.succ (generatedZeroConstructorDepth z)
      exact congrArg Nat.succ ih
  | recursiveTowerReadback event z ih =>
      change
        Nat.succ (generatedZeroLayered z).depth =
          Nat.succ (generatedZeroConstructorDepth z)
      exact congrArg Nat.succ ih
  | nonCollapseGuard budget z ih =>
      change
        Nat.succ (generatedZeroLayered z).depth =
          Nat.succ (generatedZeroConstructorDepth z)
      exact congrArg Nat.succ ih

def towerReadbackGenerated {signature : RHFreeZeroSignature} :
    Nat -> GeneratedZero signature -> GeneratedZero signature
  | 0, z => z
  | Nat.succ n, z =>
      GeneratedZero.recursiveTowerReadback
        (TraceEvent.readback (Nat.succ n) n)
        (towerReadbackGenerated n z)

def towerReadbackLayer {signature : RHFreeZeroSignature} :
    Nat -> GeneratedZero signature -> SpectralZeroLayer signature
  | 0, z => SpectralZeroLayer.base z
  | Nat.succ n, z =>
      SpectralZeroLayer.recursiveTowerReadback
        (TraceEvent.readback (Nat.succ n) n)
        (towerReadbackLayer n z)

theorem towerReadbackLayer_depth {signature : RHFreeZeroSignature} :
    (fuel : Nat) -> (z : GeneratedZero signature) ->
      layerDepth (towerReadbackLayer fuel z) = fuel
  | 0, _z => rfl
  | Nat.succ n, z => by
      change Nat.succ (layerDepth (towerReadbackLayer n z)) = Nat.succ n
      exact congrArg Nat.succ (towerReadbackLayer_depth n z)

theorem towerReadbackLayer_forget {signature : RHFreeZeroSignature} :
    (fuel : Nat) -> (z : GeneratedZero signature) ->
      forgetToGeneratedZero (towerReadbackLayer fuel z) =
        towerReadbackGenerated fuel z
  | 0, _z => rfl
  | Nat.succ n, z => by
      change
        GeneratedZero.recursiveTowerReadback
            (TraceEvent.readback (Nat.succ n) n)
            (forgetToGeneratedZero (towerReadbackLayer n z)) =
          GeneratedZero.recursiveTowerReadback
            (TraceEvent.readback (Nat.succ n) n)
            (towerReadbackGenerated n z)
      exact
        congrArg
          (GeneratedZero.recursiveTowerReadback
            (TraceEvent.readback (Nat.succ n) n))
          (towerReadbackLayer_forget n z)

end BEDC.Derived.RHRoute.RecursiveSpectralZeroHierarchy
