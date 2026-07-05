import BEDC.Derived.RHRoute.FinitePrimeWindow
import BEDC.Derived.RHRoute.ZetaBoxEvaluator

namespace BEDC.Derived.RHRoute.DynamicsUnitaryCocycle

open BEDC.Derived.RHRoute.FinitePrimeWindow
open BEDC.Derived.RHRoute.ZetaBoxEvaluator
open BEDC.Derived.RationalUp

abbrev PrimeWindow := BEDC.Derived.RHRoute.FinitePrimeWindow.PrimeWindow
abbrev RatComplex := BEDC.Derived.RHRoute.ZetaBoxEvaluator.RatComplex

structure PhaseUnitReadout where
  phase : RatComplex
  unit_norm : RatEq (ratComplexNormSq phase) ratOne

theorem phase_unit_norm (readout : PhaseUnitReadout) :
    RatEq (ratComplexNormSq readout.phase) ratOne :=
  readout.unit_norm

structure PrimeGenerationEvent where
  address : PrimeWindow
  multiplicity : Nat -> Nat
  supported : (p : Nat) -> Not (address.mem p) -> multiplicity p = 0
  activated : Nat
  activated_mem : address.mem activated
  activated_pos : 0 < multiplicity activated

def primeEventCost (event : PrimeGenerationEvent) : Nat :=
  event.address.elems.length

theorem prime_event_activated_prime (event : PrimeGenerationEvent) :
    IsPrime event.activated := by
  exact All.mem event.address.all_prime event.activated_mem

theorem prime_event_address_nonempty (event : PrimeGenerationEvent) :
    0 < event.address.elems.length := by
  exact List.length_pos_of_mem event.activated_mem

theorem prime_event_cost_positive (event : PrimeGenerationEvent) :
    0 < primeEventCost event := by
  exact prime_event_address_nonempty event

theorem prime_event_supported_off_address
    (event : PrimeGenerationEvent) (p : Nat) :
    Not (event.address.mem p) -> event.multiplicity p = 0 := by
  intro outside
  exact event.supported p outside

structure PrimeDynamicsState where
  window : PrimeWindow
  exponent : Nat -> Nat
  normalizedCode : Nat
  phase : PhaseUnitReadout
  finiteReadout : Nat
  ledger : List (List Nat)

def eventAddressTrace (event : PrimeGenerationEvent) : List Nat :=
  event.address.elems

def updateState
    (state : PrimeDynamicsState) (event : PrimeGenerationEvent)
    (normalizedCode finiteReadout : Nat) (phase : PhaseUnitReadout) :
    PrimeDynamicsState where
  window := PrimeWindow.union state.window event.address
  exponent := fun p => state.exponent p + event.multiplicity p
  normalizedCode := normalizedCode
  phase := phase
  finiteReadout := finiteReadout
  ledger := eventAddressTrace event :: state.ledger

theorem update_state_coord
    (state : PrimeDynamicsState) (event : PrimeGenerationEvent)
    (normalizedCode finiteReadout : Nat) (phase : PhaseUnitReadout) (p : Nat) :
    (updateState state event normalizedCode finiteReadout phase).exponent p =
      state.exponent p + event.multiplicity p := by
  rfl

theorem update_state_old_window_mem
    (state : PrimeDynamicsState) (event : PrimeGenerationEvent)
    (normalizedCode finiteReadout : Nat) (phase : PhaseUnitReadout) (p : Nat) :
    state.window.mem p ->
      (updateState state event normalizedCode finiteReadout phase).window.mem p := by
  intro member
  exact PrimeWindow.mem_union_left member

theorem update_state_event_address_mem
    (state : PrimeDynamicsState) (event : PrimeGenerationEvent)
    (normalizedCode finiteReadout : Nat) (phase : PhaseUnitReadout) (p : Nat) :
    event.address.mem p ->
      (updateState state event normalizedCode finiteReadout phase).window.mem p := by
  intro member
  exact PrimeWindow.mem_union_right member

theorem update_state_ledger_length_arrow
    (state : PrimeDynamicsState) (event : PrimeGenerationEvent)
    (normalizedCode finiteReadout : Nat) (phase : PhaseUnitReadout) :
    state.ledger.length <
      (updateState state event normalizedCode finiteReadout phase).ledger.length := by
  exact Nat.lt_succ_self state.ledger.length

def costAfter (cost : Nat) (event : PrimeGenerationEvent) : Nat :=
  cost + primeEventCost event

theorem prime_cost_time_arrow (cost : Nat) (event : PrimeGenerationEvent) :
    cost < costAfter cost event := by
  unfold costAfter
  exact Nat.lt_add_of_pos_right (prime_event_cost_positive event)

structure SignedPrimeEvent where
  address : PrimeWindow
  absoluteMultiplicity : Nat -> Nat
  supported : (p : Nat) -> Not (address.mem p) -> absoluteMultiplicity p = 0
  activated : Nat
  activated_mem : address.mem activated
  activated_pos : 0 < absoluteMultiplicity activated

def signedEventCost (event : SignedPrimeEvent) : Nat :=
  event.address.elems.length

theorem signed_event_cost_positive (event : SignedPrimeEvent) :
    0 < signedEventCost event := by
  exact List.length_pos_of_mem event.activated_mem

def signedCostAfter (cost : Nat) (event : SignedPrimeEvent) : Nat :=
  cost + signedEventCost event

theorem signed_cost_time_arrow (cost : Nat) (event : SignedPrimeEvent) :
    cost < signedCostAfter cost event := by
  unfold signedCostAfter
  exact Nat.lt_add_of_pos_right (signed_event_cost_positive event)

def HiddenFiberRigidityObligation
    (Interval HiddenFiber : Type u)
    (Continuous : (Interval -> HiddenFiber) -> Prop) : Prop :=
  (path : Interval -> HiddenFiber) ->
    Continuous path -> exists fiber : HiddenFiber, (t : Interval) -> path t = fiber

structure HiddenFiberJump where
  address : PrimeWindow
  displacement : Nat -> Nat
  supported : (p : Nat) -> Not (address.mem p) -> displacement p = 0

structure ThroatTransition where
  source : Nat
  target : Nat
  jumps : List HiddenFiberJump

def throatCompose
    (left right : ThroatTransition) (_match : left.target = right.source) :
    ThroatTransition where
  source := left.source
  target := right.target
  jumps := left.jumps ++ right.jumps

def ThroatCocycleConsistent
    (left right direct : ThroatTransition)
    (match_mid : left.target = right.source) : Prop :=
  direct = throatCompose left right match_mid

theorem throat_cocycle_identity
    (left right : ThroatTransition)
    (match_mid : left.target = right.source) :
    ThroatCocycleConsistent left right
      (throatCompose left right match_mid) match_mid := by
  rfl

theorem throat_cocycle_jumps
    (left right : ThroatTransition)
    (match_mid : left.target = right.source) :
    (throatCompose left right match_mid).jumps = left.jumps ++ right.jumps := by
  rfl

theorem throat_cocycle_source
    (left right : ThroatTransition)
    (match_mid : left.target = right.source) :
    (throatCompose left right match_mid).source = left.source := by
  rfl

theorem throat_cocycle_target
    (left right : ThroatTransition)
    (match_mid : left.target = right.source) :
    (throatCompose left right match_mid).target = right.target := by
  rfl

end BEDC.Derived.RHRoute.DynamicsUnitaryCocycle
