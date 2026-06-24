import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HomotopyExtensionPropertyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HomotopyExtensionPropertyUp : Type where
  | mk
      (closedSubcarrier ambientCarrier cylinderWindow initialMap subcarrierHomotopy handoff
        request extendedWindow transport replay provenance name : BHist) :
      HomotopyExtensionPropertyUp
  deriving DecidableEq

def homotopyExtensionPropertyEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: homotopyExtensionPropertyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: homotopyExtensionPropertyEncodeBHist h

def homotopyExtensionPropertyDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (homotopyExtensionPropertyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (homotopyExtensionPropertyDecodeBHist tail)

private theorem homotopyExtensionProperty_decode_encode :
    forall h : BHist,
      homotopyExtensionPropertyDecodeBHist (homotopyExtensionPropertyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def homotopyExtensionPropertyFields : HomotopyExtensionPropertyUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HomotopyExtensionPropertyUp.mk closedSubcarrier ambientCarrier cylinderWindow initialMap
      subcarrierHomotopy handoff request extendedWindow transport replay provenance name =>
      [closedSubcarrier, ambientCarrier, cylinderWindow, initialMap, subcarrierHomotopy,
        handoff, request, extendedWindow, transport, replay, provenance, name]

def homotopyExtensionPropertyToEventFlow : HomotopyExtensionPropertyUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (homotopyExtensionPropertyFields x).map homotopyExtensionPropertyEncodeBHist

def homotopyExtensionPropertyEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => homotopyExtensionPropertyEventAt index rest

def homotopyExtensionPropertyFromEventFlow :
    EventFlow -> Option HomotopyExtensionPropertyUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      some
        (HomotopyExtensionPropertyUp.mk
          (homotopyExtensionPropertyDecodeBHist
            (homotopyExtensionPropertyEventAt 0 flow))
          (homotopyExtensionPropertyDecodeBHist
            (homotopyExtensionPropertyEventAt 1 flow))
          (homotopyExtensionPropertyDecodeBHist
            (homotopyExtensionPropertyEventAt 2 flow))
          (homotopyExtensionPropertyDecodeBHist
            (homotopyExtensionPropertyEventAt 3 flow))
          (homotopyExtensionPropertyDecodeBHist
            (homotopyExtensionPropertyEventAt 4 flow))
          (homotopyExtensionPropertyDecodeBHist
            (homotopyExtensionPropertyEventAt 5 flow))
          (homotopyExtensionPropertyDecodeBHist
            (homotopyExtensionPropertyEventAt 6 flow))
          (homotopyExtensionPropertyDecodeBHist
            (homotopyExtensionPropertyEventAt 7 flow))
          (homotopyExtensionPropertyDecodeBHist
            (homotopyExtensionPropertyEventAt 8 flow))
          (homotopyExtensionPropertyDecodeBHist
            (homotopyExtensionPropertyEventAt 9 flow))
          (homotopyExtensionPropertyDecodeBHist
            (homotopyExtensionPropertyEventAt 10 flow))
          (homotopyExtensionPropertyDecodeBHist
            (homotopyExtensionPropertyEventAt 11 flow)))

private theorem homotopyExtensionProperty_round_trip :
    forall x : HomotopyExtensionPropertyUp,
      homotopyExtensionPropertyFromEventFlow
        (homotopyExtensionPropertyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk closedSubcarrier ambientCarrier cylinderWindow initialMap subcarrierHomotopy handoff
      request extendedWindow transport replay provenance name =>
      change
        some
          (HomotopyExtensionPropertyUp.mk
            (homotopyExtensionPropertyDecodeBHist
              (homotopyExtensionPropertyEncodeBHist closedSubcarrier))
            (homotopyExtensionPropertyDecodeBHist
              (homotopyExtensionPropertyEncodeBHist ambientCarrier))
            (homotopyExtensionPropertyDecodeBHist
              (homotopyExtensionPropertyEncodeBHist cylinderWindow))
            (homotopyExtensionPropertyDecodeBHist
              (homotopyExtensionPropertyEncodeBHist initialMap))
            (homotopyExtensionPropertyDecodeBHist
              (homotopyExtensionPropertyEncodeBHist subcarrierHomotopy))
            (homotopyExtensionPropertyDecodeBHist
              (homotopyExtensionPropertyEncodeBHist handoff))
            (homotopyExtensionPropertyDecodeBHist
              (homotopyExtensionPropertyEncodeBHist request))
            (homotopyExtensionPropertyDecodeBHist
              (homotopyExtensionPropertyEncodeBHist extendedWindow))
            (homotopyExtensionPropertyDecodeBHist
              (homotopyExtensionPropertyEncodeBHist transport))
            (homotopyExtensionPropertyDecodeBHist
              (homotopyExtensionPropertyEncodeBHist replay))
            (homotopyExtensionPropertyDecodeBHist
              (homotopyExtensionPropertyEncodeBHist provenance))
            (homotopyExtensionPropertyDecodeBHist
              (homotopyExtensionPropertyEncodeBHist name))) =
          some
            (HomotopyExtensionPropertyUp.mk closedSubcarrier ambientCarrier cylinderWindow
              initialMap subcarrierHomotopy handoff request extendedWindow transport replay
              provenance name)
      rw [homotopyExtensionProperty_decode_encode closedSubcarrier,
        homotopyExtensionProperty_decode_encode ambientCarrier,
        homotopyExtensionProperty_decode_encode cylinderWindow,
        homotopyExtensionProperty_decode_encode initialMap,
        homotopyExtensionProperty_decode_encode subcarrierHomotopy,
        homotopyExtensionProperty_decode_encode handoff,
        homotopyExtensionProperty_decode_encode request,
        homotopyExtensionProperty_decode_encode extendedWindow,
        homotopyExtensionProperty_decode_encode transport,
        homotopyExtensionProperty_decode_encode replay,
        homotopyExtensionProperty_decode_encode provenance,
        homotopyExtensionProperty_decode_encode name]

private theorem homotopyExtensionPropertyToEventFlow_injective
    {x y : HomotopyExtensionPropertyUp} :
    homotopyExtensionPropertyToEventFlow x = homotopyExtensionPropertyToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      homotopyExtensionPropertyFromEventFlow (homotopyExtensionPropertyToEventFlow x) =
        homotopyExtensionPropertyFromEventFlow (homotopyExtensionPropertyToEventFlow y) :=
    congrArg homotopyExtensionPropertyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (homotopyExtensionProperty_round_trip x).symm
      (Eq.trans hread (homotopyExtensionProperty_round_trip y)))

instance homotopyExtensionPropertyBHistCarrier :
    BHistCarrier HomotopyExtensionPropertyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := homotopyExtensionPropertyToEventFlow
  fromEventFlow := homotopyExtensionPropertyFromEventFlow

instance homotopyExtensionPropertyChapterTasteGate :
    ChapterTasteGate HomotopyExtensionPropertyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change homotopyExtensionPropertyFromEventFlow
      (homotopyExtensionPropertyToEventFlow x) = some x
    exact homotopyExtensionProperty_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (homotopyExtensionPropertyToEventFlow_injective heq)

theorem HomotopyExtensionPropertyTasteGate_single_carrier_alignment :
    (forall h : BHist,
      homotopyExtensionPropertyDecodeBHist (homotopyExtensionPropertyEncodeBHist h) = h) /\
      (forall x : HomotopyExtensionPropertyUp,
        homotopyExtensionPropertyFromEventFlow
          (homotopyExtensionPropertyToEventFlow x) = some x) /\
      (forall x y : HomotopyExtensionPropertyUp,
        homotopyExtensionPropertyToEventFlow x =
          homotopyExtensionPropertyToEventFlow y -> x = y) /\
      homotopyExtensionPropertyEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨homotopyExtensionProperty_decode_encode,
      homotopyExtensionProperty_round_trip,
      (fun _ _ heq => homotopyExtensionPropertyToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.HomotopyExtensionPropertyUp
