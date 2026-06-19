import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CaristiFixedPointUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CaristiFixedPointUp : Type where
  | mk (domain distance potential selfMap descent ekeland endpoint transport replay provenance
      localName : BHist) : CaristiFixedPointUp
  deriving DecidableEq

def caristiFixedPointEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: caristiFixedPointEncodeBHist h
  | BHist.e1 h => BMark.b1 :: caristiFixedPointEncodeBHist h

def caristiFixedPointDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (caristiFixedPointDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (caristiFixedPointDecodeBHist tail)

private theorem caristiFixedPointDecode_encode_bhist :
    ∀ h : BHist, caristiFixedPointDecodeBHist (caristiFixedPointEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def caristiFixedPointFields : CaristiFixedPointUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CaristiFixedPointUp.mk domain distance potential selfMap descent ekeland endpoint
      transport replay provenance localName =>
      [domain, distance, potential, selfMap, descent, ekeland, endpoint, transport,
        replay, provenance, localName]

def caristiFixedPointToEventFlow : CaristiFixedPointUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (caristiFixedPointFields x).map caristiFixedPointEncodeBHist

private def caristiFixedPointEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => caristiFixedPointEventAtDefault index rest

def caristiFixedPointFromEventFlow (ef : EventFlow) : Option CaristiFixedPointUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CaristiFixedPointUp.mk
      (caristiFixedPointDecodeBHist (caristiFixedPointEventAtDefault 0 ef))
      (caristiFixedPointDecodeBHist (caristiFixedPointEventAtDefault 1 ef))
      (caristiFixedPointDecodeBHist (caristiFixedPointEventAtDefault 2 ef))
      (caristiFixedPointDecodeBHist (caristiFixedPointEventAtDefault 3 ef))
      (caristiFixedPointDecodeBHist (caristiFixedPointEventAtDefault 4 ef))
      (caristiFixedPointDecodeBHist (caristiFixedPointEventAtDefault 5 ef))
      (caristiFixedPointDecodeBHist (caristiFixedPointEventAtDefault 6 ef))
      (caristiFixedPointDecodeBHist (caristiFixedPointEventAtDefault 7 ef))
      (caristiFixedPointDecodeBHist (caristiFixedPointEventAtDefault 8 ef))
      (caristiFixedPointDecodeBHist (caristiFixedPointEventAtDefault 9 ef))
      (caristiFixedPointDecodeBHist (caristiFixedPointEventAtDefault 10 ef)))

private theorem caristiFixedPoint_round_trip :
    ∀ x : CaristiFixedPointUp,
      caristiFixedPointFromEventFlow (caristiFixedPointToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk domain distance potential selfMap descent ekeland endpoint transport replay provenance
      localName =>
      change
        some
          (CaristiFixedPointUp.mk
            (caristiFixedPointDecodeBHist (caristiFixedPointEncodeBHist domain))
            (caristiFixedPointDecodeBHist (caristiFixedPointEncodeBHist distance))
            (caristiFixedPointDecodeBHist (caristiFixedPointEncodeBHist potential))
            (caristiFixedPointDecodeBHist (caristiFixedPointEncodeBHist selfMap))
            (caristiFixedPointDecodeBHist (caristiFixedPointEncodeBHist descent))
            (caristiFixedPointDecodeBHist (caristiFixedPointEncodeBHist ekeland))
            (caristiFixedPointDecodeBHist (caristiFixedPointEncodeBHist endpoint))
            (caristiFixedPointDecodeBHist (caristiFixedPointEncodeBHist transport))
            (caristiFixedPointDecodeBHist (caristiFixedPointEncodeBHist replay))
            (caristiFixedPointDecodeBHist (caristiFixedPointEncodeBHist provenance))
            (caristiFixedPointDecodeBHist (caristiFixedPointEncodeBHist localName))) =
          some
            (CaristiFixedPointUp.mk domain distance potential selfMap descent ekeland
              endpoint transport replay provenance localName)
      rw [caristiFixedPointDecode_encode_bhist domain,
        caristiFixedPointDecode_encode_bhist distance,
        caristiFixedPointDecode_encode_bhist potential,
        caristiFixedPointDecode_encode_bhist selfMap,
        caristiFixedPointDecode_encode_bhist descent,
        caristiFixedPointDecode_encode_bhist ekeland,
        caristiFixedPointDecode_encode_bhist endpoint,
        caristiFixedPointDecode_encode_bhist transport,
        caristiFixedPointDecode_encode_bhist replay,
        caristiFixedPointDecode_encode_bhist provenance,
        caristiFixedPointDecode_encode_bhist localName]

private theorem caristiFixedPointToEventFlow_injective {x y : CaristiFixedPointUp} :
    caristiFixedPointToEventFlow x = caristiFixedPointToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      caristiFixedPointFromEventFlow (caristiFixedPointToEventFlow x) =
        caristiFixedPointFromEventFlow (caristiFixedPointToEventFlow y) :=
    congrArg caristiFixedPointFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (caristiFixedPoint_round_trip x).symm
      (Eq.trans hread (caristiFixedPoint_round_trip y)))

private theorem caristiFixedPoint_fields_faithful :
    ∀ x y : CaristiFixedPointUp, caristiFixedPointFields x = caristiFixedPointFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk domain1 distance1 potential1 selfMap1 descent1 ekeland1 endpoint1 transport1 replay1
      provenance1 localName1 =>
      cases y with
      | mk domain2 distance2 potential2 selfMap2 descent2 ekeland2 endpoint2 transport2
          replay2 provenance2 localName2 =>
          cases hfields
          rfl

instance caristiFixedPointBHistCarrier : BHistCarrier CaristiFixedPointUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := caristiFixedPointToEventFlow
  fromEventFlow := caristiFixedPointFromEventFlow

instance caristiFixedPointChapterTasteGate : ChapterTasteGate CaristiFixedPointUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change caristiFixedPointFromEventFlow (caristiFixedPointToEventFlow x) = some x
    exact caristiFixedPoint_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (caristiFixedPointToEventFlow_injective heq)

instance caristiFixedPointFieldFaithful : FieldFaithful CaristiFixedPointUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := caristiFixedPointFields
  field_faithful := caristiFixedPoint_fields_faithful

instance caristiFixedPointNontrivial : Nontrivial CaristiFixedPointUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CaristiFixedPointUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CaristiFixedPointUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CaristiFixedPointUp :=
  -- BEDC touchpoint anchor: BHist BMark
  caristiFixedPointChapterTasteGate

theorem CaristiFixedPointTasteGate_single_carrier_alignment :
    (∀ x : CaristiFixedPointUp,
        caristiFixedPointFromEventFlow (caristiFixedPointToEventFlow x) = some x) ∧
      (∀ x y : CaristiFixedPointUp,
        caristiFixedPointFields x = caristiFixedPointFields y → x = y) ∧
        caristiFixedPointEncodeBHist BHist.Empty = ([] : RawEvent) ∧
          caristiFixedPointEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨caristiFixedPoint_round_trip, caristiFixedPoint_fields_faithful, rfl, rfl⟩

end BEDC.Derived.CaristiFixedPointUp
