import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CrossHistoryCausalDependenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CrossHistoryCausalDependenceUp : Type where
  | mk :
      (source target route stability noGlobalFrame estimate bridge transport replay provenance
        name : BHist) ->
      CrossHistoryCausalDependenceUp
  deriving DecidableEq

def crossHistoryCausalDependenceEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: crossHistoryCausalDependenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: crossHistoryCausalDependenceEncodeBHist h

def crossHistoryCausalDependenceDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (crossHistoryCausalDependenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (crossHistoryCausalDependenceDecodeBHist tail)

private theorem crossHistoryCausalDependenceDecode_encode_bhist :
    forall h : BHist,
      crossHistoryCausalDependenceDecodeBHist
        (crossHistoryCausalDependenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def crossHistoryCausalDependenceToEventFlow :
    CrossHistoryCausalDependenceUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CrossHistoryCausalDependenceUp.mk source target route stability noGlobalFrame estimate
      bridge transport replay provenance name =>
      [crossHistoryCausalDependenceEncodeBHist source,
        crossHistoryCausalDependenceEncodeBHist target,
        crossHistoryCausalDependenceEncodeBHist route,
        crossHistoryCausalDependenceEncodeBHist stability,
        crossHistoryCausalDependenceEncodeBHist noGlobalFrame,
        crossHistoryCausalDependenceEncodeBHist estimate,
        crossHistoryCausalDependenceEncodeBHist bridge,
        crossHistoryCausalDependenceEncodeBHist transport,
        crossHistoryCausalDependenceEncodeBHist replay,
        crossHistoryCausalDependenceEncodeBHist provenance,
        crossHistoryCausalDependenceEncodeBHist name]

def crossHistoryCausalDependenceFromEventFlow :
    EventFlow -> Option CrossHistoryCausalDependenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [source, target, route, stability, noGlobalFrame, estimate, bridge, transport, replay,
      provenance, name] =>
      some
        (CrossHistoryCausalDependenceUp.mk
          (crossHistoryCausalDependenceDecodeBHist source)
          (crossHistoryCausalDependenceDecodeBHist target)
          (crossHistoryCausalDependenceDecodeBHist route)
          (crossHistoryCausalDependenceDecodeBHist stability)
          (crossHistoryCausalDependenceDecodeBHist noGlobalFrame)
          (crossHistoryCausalDependenceDecodeBHist estimate)
          (crossHistoryCausalDependenceDecodeBHist bridge)
          (crossHistoryCausalDependenceDecodeBHist transport)
          (crossHistoryCausalDependenceDecodeBHist replay)
          (crossHistoryCausalDependenceDecodeBHist provenance)
          (crossHistoryCausalDependenceDecodeBHist name))
  | _ => none

private theorem crossHistoryCausalDependence_round_trip :
    forall x : CrossHistoryCausalDependenceUp,
      crossHistoryCausalDependenceFromEventFlow
        (crossHistoryCausalDependenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source target route stability noGlobalFrame estimate bridge transport replay provenance
      name =>
      change
        some
          (CrossHistoryCausalDependenceUp.mk
            (crossHistoryCausalDependenceDecodeBHist
              (crossHistoryCausalDependenceEncodeBHist source))
            (crossHistoryCausalDependenceDecodeBHist
              (crossHistoryCausalDependenceEncodeBHist target))
            (crossHistoryCausalDependenceDecodeBHist
              (crossHistoryCausalDependenceEncodeBHist route))
            (crossHistoryCausalDependenceDecodeBHist
              (crossHistoryCausalDependenceEncodeBHist stability))
            (crossHistoryCausalDependenceDecodeBHist
              (crossHistoryCausalDependenceEncodeBHist noGlobalFrame))
            (crossHistoryCausalDependenceDecodeBHist
              (crossHistoryCausalDependenceEncodeBHist estimate))
            (crossHistoryCausalDependenceDecodeBHist
              (crossHistoryCausalDependenceEncodeBHist bridge))
            (crossHistoryCausalDependenceDecodeBHist
              (crossHistoryCausalDependenceEncodeBHist transport))
            (crossHistoryCausalDependenceDecodeBHist
              (crossHistoryCausalDependenceEncodeBHist replay))
            (crossHistoryCausalDependenceDecodeBHist
              (crossHistoryCausalDependenceEncodeBHist provenance))
            (crossHistoryCausalDependenceDecodeBHist
              (crossHistoryCausalDependenceEncodeBHist name))) =
          some
            (CrossHistoryCausalDependenceUp.mk source target route stability noGlobalFrame
              estimate bridge transport replay provenance name)
      rw [crossHistoryCausalDependenceDecode_encode_bhist source,
        crossHistoryCausalDependenceDecode_encode_bhist target,
        crossHistoryCausalDependenceDecode_encode_bhist route,
        crossHistoryCausalDependenceDecode_encode_bhist stability,
        crossHistoryCausalDependenceDecode_encode_bhist noGlobalFrame,
        crossHistoryCausalDependenceDecode_encode_bhist estimate,
        crossHistoryCausalDependenceDecode_encode_bhist bridge,
        crossHistoryCausalDependenceDecode_encode_bhist transport,
        crossHistoryCausalDependenceDecode_encode_bhist replay,
        crossHistoryCausalDependenceDecode_encode_bhist provenance,
        crossHistoryCausalDependenceDecode_encode_bhist name]

private theorem crossHistoryCausalDependenceToEventFlow_injective
    {x y : CrossHistoryCausalDependenceUp} :
    crossHistoryCausalDependenceToEventFlow x =
      crossHistoryCausalDependenceToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      crossHistoryCausalDependenceFromEventFlow
          (crossHistoryCausalDependenceToEventFlow x) =
        crossHistoryCausalDependenceFromEventFlow
          (crossHistoryCausalDependenceToEventFlow y) :=
    congrArg crossHistoryCausalDependenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (crossHistoryCausalDependence_round_trip x).symm
      (Eq.trans hread (crossHistoryCausalDependence_round_trip y)))

instance crossHistoryCausalDependenceBHistCarrier :
    BHistCarrier CrossHistoryCausalDependenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := crossHistoryCausalDependenceToEventFlow
  fromEventFlow := crossHistoryCausalDependenceFromEventFlow

instance crossHistoryCausalDependenceChapterTasteGate :
    ChapterTasteGate CrossHistoryCausalDependenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      crossHistoryCausalDependenceFromEventFlow
        (crossHistoryCausalDependenceToEventFlow x) = some x
    exact crossHistoryCausalDependence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (crossHistoryCausalDependenceToEventFlow_injective heq)

def crossHistoryCausalDependenceFields :
    CrossHistoryCausalDependenceUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CrossHistoryCausalDependenceUp.mk source target route stability noGlobalFrame estimate
      bridge transport replay provenance name =>
      [source, target, route, stability, noGlobalFrame, estimate, bridge, transport, replay,
        provenance, name]

theorem CrossHistoryCausalDependenceCarrier_no_global_frame_row_deterministic
    {source target route stability noGlobalFrame noGlobalFrame' estimate bridge transport replay
      provenance name : BHist} :
    crossHistoryCausalDependenceFields
        (CrossHistoryCausalDependenceUp.mk source target route stability noGlobalFrame estimate
          bridge transport replay provenance name) =
      crossHistoryCausalDependenceFields
        (CrossHistoryCausalDependenceUp.mk source target route stability noGlobalFrame' estimate
          bridge transport replay provenance name) →
      hsame noGlobalFrame noGlobalFrame' := by
  -- BEDC touchpoint anchor: BHist BMark hsame
  intro hfields
  change
    [source, target, route, stability, noGlobalFrame, estimate, bridge, transport, replay,
        provenance, name] =
      [source, target, route, stability, noGlobalFrame', estimate, bridge, transport, replay,
        provenance, name] at hfields
  injection hfields with _ tailSource
  injection tailSource with _ tailTarget
  injection tailTarget with _ tailRoute
  injection tailRoute with _ tailStability
  injection tailStability with noGlobalFrameEq _

private theorem crossHistoryCausalDependence_field_faithful_concrete :
    forall x y : CrossHistoryCausalDependenceUp,
      crossHistoryCausalDependenceFields x = crossHistoryCausalDependenceFields y ->
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk source target route stability noGlobalFrame estimate bridge transport replay provenance
      name =>
      cases y with
      | mk source' target' route' stability' noGlobalFrame' estimate' bridge' transport'
          replay' provenance' name' =>
          change
            [source, target, route, stability, noGlobalFrame, estimate, bridge, transport,
                replay, provenance, name] =
              [source', target', route', stability', noGlobalFrame', estimate', bridge',
                transport', replay', provenance', name'] at hfields
          cases hfields
          rfl

instance crossHistoryCausalDependenceFieldFaithful :
    FieldFaithful CrossHistoryCausalDependenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := crossHistoryCausalDependenceFields
  field_faithful := crossHistoryCausalDependence_field_faithful_concrete

instance crossHistoryCausalDependenceNontrivial :
    Nontrivial CrossHistoryCausalDependenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CrossHistoryCausalDependenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CrossHistoryCausalDependenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CrossHistoryCausalDependenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  crossHistoryCausalDependenceChapterTasteGate

end BEDC.Derived.CrossHistoryCausalDependenceUp
