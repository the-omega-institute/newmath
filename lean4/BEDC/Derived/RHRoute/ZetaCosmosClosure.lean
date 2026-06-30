import BEDC.Derived.RHRoute.ZeroGenerationInitiality

namespace BEDC.Derived.RHRoute.ZetaCosmosClosure

open BEDC.Derived.RHRoute.ZeroGenerationInitiality
open BEDC.Derived.RHRoute.FunctionalEquationSymmetry

inductive PositiveNat : Nat -> Prop where
  | succ (n : Nat) : PositiveNat (Nat.succ n)

inductive PhaseDirection where
  | recursive
  | inertial

inductive NonUnitaryPhaseDirection : PhaseDirection -> Prop where
  | inertial : NonUnitaryPhaseDirection PhaseDirection.inertial

structure ActiveCenteredChannel
    (signature : RHFreeZeroSignature) where
  center : GeneratedZero signature
  code : Nat

structure InertialPhaseState
    (signature : RHFreeZeroSignature) where
  zero : GeneratedZero signature
  recursiveTime : Nat
  inertialHeight : Nat
  direction : PhaseDirection

/-
Galperin-style inertial unfolding is recorded as source-internal data for
generated zeta zeros: finite active centered channels, a second non-unitary
time direction with positive height, and a projected orbit in the source
zero carrier.
-/
structure ZetaGalperinInertialUnfolding
    (signature : RHFreeZeroSignature) where
  realization : GeneratedZeroRealization signature
  activeCenteredChannels : List (ActiveCenteredChannel signature)
  activeChannel : ActiveCenteredChannel signature -> Prop
  channelFor : GeneratedZero signature -> ActiveCenteredChannel signature
  channelFor_mem :
    (z : GeneratedZero signature) ->
      channelFor z ∈ activeCenteredChannels
  channelFor_active :
    (z : GeneratedZero signature) ->
      activeChannel (channelFor z)
  channelFor_centered :
    (z : GeneratedZero signature) ->
      (channelFor z).center = z
  inertialHeightFor : GeneratedZero signature -> Nat
  inertialHeight_positive :
    (z : GeneratedZero signature) ->
      PositiveNat (inertialHeightFor z)
  phaseFlow :
    GeneratedZero signature -> Nat -> InertialPhaseState signature
  phaseFlow_tracks_zero :
    (z : GeneratedZero signature) -> (t : Nat) ->
      (phaseFlow z t).zero = z
  phaseFlow_height :
    (z : GeneratedZero signature) -> (t : Nat) ->
      (phaseFlow z t).inertialHeight = inertialHeightFor z
  phaseFlow_inertial :
    (z : GeneratedZero signature) -> (t : Nat) ->
      (phaseFlow z t).direction = PhaseDirection.inertial
  phaseFlow_nonunitary :
    (z : GeneratedZero signature) -> (t : Nat) ->
      NonUnitaryPhaseDirection (phaseFlow z t).direction
  projectedPoint : GeneratedZero signature -> SourceZeroPoint
  projectionOrbit : GeneratedZero signature -> List SourceZeroPoint
  projection_contains_projected :
    (z : GeneratedZero signature) ->
      projectedPoint z ∈ projectionOrbit z
  projection_matches_generated_zero :
    (z : GeneratedZero signature) ->
      ComplexEq (projectedPoint z) (realization.epsilon z)
  canonicalGeneratedCarrier : GeneratedZero signature -> Prop
  activeCapture : GeneratedZero signature -> Prop
  farEndCompatibleSocket : GeneratedZero signature -> Prop
  noHiddenScaleAbsorption : GeneratedZero signature -> Prop
  constructorTriadicInvariant :
    ZeroSigF signature (GeneratedZero signature) -> Prop
  constructorRecursiveTimePreserved :
    ZeroSigF signature (GeneratedZero signature) -> Prop
  hiddenCoordinatesRestricted :
    ZeroSigF signature (GeneratedZero signature) -> Prop
  generatedRowNoIndependentRealScaleLedger :
    ZeroSigF signature (GeneratedZero signature) -> Prop

def generatedZeroProjection
    {signature : RHFreeZeroSignature}
    (unfolding : ZetaGalperinInertialUnfolding signature) :
    GeneratedZero signature -> SourceZeroPoint :=
  unfolding.projectedPoint

theorem channelFor_is_active
    {signature : RHFreeZeroSignature}
    (unfolding : ZetaGalperinInertialUnfolding signature)
    (z : GeneratedZero signature) :
    unfolding.activeChannel (unfolding.channelFor z) :=
  unfolding.channelFor_active z

theorem channelFor_is_centered
    {signature : RHFreeZeroSignature}
    (unfolding : ZetaGalperinInertialUnfolding signature)
    (z : GeneratedZero signature) :
    (unfolding.channelFor z).center = z :=
  unfolding.channelFor_centered z

theorem phaseFlow_height_positive
    {signature : RHFreeZeroSignature}
    (unfolding : ZetaGalperinInertialUnfolding signature)
    (z : GeneratedZero signature) (t : Nat) :
    PositiveNat (unfolding.phaseFlow z t).inertialHeight := by
  rw [unfolding.phaseFlow_height z t]
  exact unfolding.inertialHeight_positive z

theorem phaseFlow_has_nonunitary_inertial_direction
    {signature : RHFreeZeroSignature}
    (unfolding : ZetaGalperinInertialUnfolding signature)
    (z : GeneratedZero signature) (t : Nat) :
    NonUnitaryPhaseDirection (unfolding.phaseFlow z t).direction :=
  unfolding.phaseFlow_nonunitary z t

def CanonicalDominanceOrActiveCapture
    {signature : RHFreeZeroSignature}
    (unfolding : ZetaGalperinInertialUnfolding signature) : Prop :=
  ∀ z : GeneratedZero signature,
    unfolding.canonicalGeneratedCarrier z ∨ unfolding.activeCapture z

def FarEndNoScaleAbsorption
    {signature : RHFreeZeroSignature}
    (unfolding : ZetaGalperinInertialUnfolding signature) : Prop :=
  ∀ z : GeneratedZero signature,
    unfolding.farEndCompatibleSocket z ∧
      unfolding.noHiddenScaleAbsorption z

def TriadicInvariantPreserved
    {signature : RHFreeZeroSignature}
    (unfolding : ZetaGalperinInertialUnfolding signature) : Prop :=
  ∀ row : ZeroSigF signature (GeneratedZero signature),
    unfolding.constructorTriadicInvariant row ∧
      unfolding.constructorRecursiveTimePreserved row ∧
        unfolding.hiddenCoordinatesRestricted row

def NoIndependentRealScaleLedger
    {signature : RHFreeZeroSignature}
    (unfolding : ZetaGalperinInertialUnfolding signature) : Prop :=
  ∀ row : ZeroSigF signature (GeneratedZero signature),
    unfolding.generatedRowNoIndependentRealScaleLedger row

/-
This structure packages the four strong-route obligations. It is not an
unconditional proof of the zeta route, and it does not assert RH.
-/
structure ZetaCosmosClosure
    {signature : RHFreeZeroSignature}
    (unfolding : ZetaGalperinInertialUnfolding signature) where
  canonical_dominance_or_active_capture :
    CanonicalDominanceOrActiveCapture unfolding
  far_end_no_scale_absorption :
    FarEndNoScaleAbsorption unfolding
  triadic_invariant_preserved :
    TriadicInvariantPreserved unfolding
  no_independent_real_scale_ledger :
    NoIndependentRealScaleLedger unfolding

def ConservativePhaseClosure
    {signature : RHFreeZeroSignature}
    (unfolding : ZetaGalperinInertialUnfolding signature) : Prop :=
  CanonicalDominanceOrActiveCapture unfolding ∧
    FarEndNoScaleAbsorption unfolding ∧
      TriadicInvariantPreserved unfolding ∧
        NoIndependentRealScaleLedger unfolding

theorem zeta_cosmos_closure_strong_route
    (unfolding :
      ZetaGalperinInertialUnfolding rhFreeZeroSignature)
    (closure : ZetaCosmosClosure unfolding) :
    ConservativePhaseClosure unfolding := by
  exact
    ⟨closure.canonical_dominance_or_active_capture,
      closure.far_end_no_scale_absorption,
      closure.triadic_invariant_preserved,
      closure.no_independent_real_scale_ledger⟩

end BEDC.Derived.RHRoute.ZetaCosmosClosure
