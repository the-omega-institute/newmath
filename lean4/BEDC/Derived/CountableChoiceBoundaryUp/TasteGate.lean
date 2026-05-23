import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CountableChoiceBoundaryUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CountableChoiceBoundaryUp : Type where
  | mk :
      (request window readback realSeal finiteWitness localRefusal uniqueReadback transport replay
        provenance name : BHist) →
        CountableChoiceBoundaryUp
  deriving DecidableEq

def countableChoiceBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: countableChoiceBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: countableChoiceBoundaryEncodeBHist h

def countableChoiceBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (countableChoiceBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (countableChoiceBoundaryDecodeBHist tail)

private theorem countableChoiceBoundary_decode_encode_bhist :
    ∀ h : BHist,
      countableChoiceBoundaryDecodeBHist (countableChoiceBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def countableChoiceBoundaryFields : CountableChoiceBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CountableChoiceBoundaryUp.mk request window readback realSeal finiteWitness localRefusal
      uniqueReadback transport replay provenance name =>
      [request, window, readback, realSeal, finiteWitness, localRefusal, uniqueReadback,
        transport, replay, provenance, name]

def countableChoiceBoundaryToEventFlow : CountableChoiceBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (countableChoiceBoundaryFields x).map countableChoiceBoundaryEncodeBHist

private def countableChoiceBoundaryDecodePacket
    (request window readback realSeal finiteWitness localRefusal uniqueReadback transport replay
      provenance name : RawEvent) :
    CountableChoiceBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  CountableChoiceBoundaryUp.mk
    (countableChoiceBoundaryDecodeBHist request)
    (countableChoiceBoundaryDecodeBHist window)
    (countableChoiceBoundaryDecodeBHist readback)
    (countableChoiceBoundaryDecodeBHist realSeal)
    (countableChoiceBoundaryDecodeBHist finiteWitness)
    (countableChoiceBoundaryDecodeBHist localRefusal)
    (countableChoiceBoundaryDecodeBHist uniqueReadback)
    (countableChoiceBoundaryDecodeBHist transport)
    (countableChoiceBoundaryDecodeBHist replay)
    (countableChoiceBoundaryDecodeBHist provenance)
    (countableChoiceBoundaryDecodeBHist name)

private def countableChoiceBoundaryRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => countableChoiceBoundaryRawAt n rest

private def countableChoiceBoundaryLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => countableChoiceBoundaryLengthEq n rest

def countableChoiceBoundaryFromEventFlow : EventFlow → Option CountableChoiceBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match countableChoiceBoundaryLengthEq 11 flow with
      | true =>
          some
            (countableChoiceBoundaryDecodePacket
              (countableChoiceBoundaryRawAt 0 flow)
              (countableChoiceBoundaryRawAt 1 flow)
              (countableChoiceBoundaryRawAt 2 flow)
              (countableChoiceBoundaryRawAt 3 flow)
              (countableChoiceBoundaryRawAt 4 flow)
              (countableChoiceBoundaryRawAt 5 flow)
              (countableChoiceBoundaryRawAt 6 flow)
              (countableChoiceBoundaryRawAt 7 flow)
              (countableChoiceBoundaryRawAt 8 flow)
              (countableChoiceBoundaryRawAt 9 flow)
              (countableChoiceBoundaryRawAt 10 flow))
      | false => none

private theorem countableChoiceBoundary_round_trip :
    ∀ x : CountableChoiceBoundaryUp,
      countableChoiceBoundaryFromEventFlow
        (countableChoiceBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk request window readback realSeal finiteWitness localRefusal uniqueReadback transport
      replay provenance name =>
      change
        some
          (countableChoiceBoundaryDecodePacket
            (countableChoiceBoundaryEncodeBHist request)
            (countableChoiceBoundaryEncodeBHist window)
            (countableChoiceBoundaryEncodeBHist readback)
            (countableChoiceBoundaryEncodeBHist realSeal)
            (countableChoiceBoundaryEncodeBHist finiteWitness)
            (countableChoiceBoundaryEncodeBHist localRefusal)
            (countableChoiceBoundaryEncodeBHist uniqueReadback)
            (countableChoiceBoundaryEncodeBHist transport)
            (countableChoiceBoundaryEncodeBHist replay)
            (countableChoiceBoundaryEncodeBHist provenance)
            (countableChoiceBoundaryEncodeBHist name)) =
          some
            (CountableChoiceBoundaryUp.mk request window readback realSeal finiteWitness
              localRefusal uniqueReadback transport replay provenance name)
      unfold countableChoiceBoundaryDecodePacket
      rw [countableChoiceBoundary_decode_encode_bhist request,
        countableChoiceBoundary_decode_encode_bhist window,
        countableChoiceBoundary_decode_encode_bhist readback,
        countableChoiceBoundary_decode_encode_bhist realSeal,
        countableChoiceBoundary_decode_encode_bhist finiteWitness,
        countableChoiceBoundary_decode_encode_bhist localRefusal,
        countableChoiceBoundary_decode_encode_bhist uniqueReadback,
        countableChoiceBoundary_decode_encode_bhist transport,
        countableChoiceBoundary_decode_encode_bhist replay,
        countableChoiceBoundary_decode_encode_bhist provenance,
        countableChoiceBoundary_decode_encode_bhist name]

private theorem countableChoiceBoundaryToEventFlow_injective
    {x y : CountableChoiceBoundaryUp} :
    countableChoiceBoundaryToEventFlow x =
      countableChoiceBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      countableChoiceBoundaryFromEventFlow
          (countableChoiceBoundaryToEventFlow x) =
        countableChoiceBoundaryFromEventFlow
          (countableChoiceBoundaryToEventFlow y) :=
    congrArg countableChoiceBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (countableChoiceBoundary_round_trip x).symm
      (Eq.trans hread (countableChoiceBoundary_round_trip y)))

instance countableChoiceBoundaryBHistCarrier :
    BHistCarrier CountableChoiceBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := countableChoiceBoundaryToEventFlow
  fromEventFlow := countableChoiceBoundaryFromEventFlow

instance countableChoiceBoundaryChapterTasteGate :
    ChapterTasteGate CountableChoiceBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      countableChoiceBoundaryFromEventFlow
        (countableChoiceBoundaryToEventFlow x) = some x
    exact countableChoiceBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (countableChoiceBoundaryToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CountableChoiceBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  countableChoiceBoundaryChapterTasteGate

theorem CountableChoiceBoundaryTasteGate_single_carrier_alignment :
    (forall h : BHist,
      countableChoiceBoundaryDecodeBHist (countableChoiceBoundaryEncodeBHist h) = h) ∧
      (forall x : CountableChoiceBoundaryUp,
        countableChoiceBoundaryFromEventFlow (countableChoiceBoundaryToEventFlow x) = some x) ∧
      (forall x y : CountableChoiceBoundaryUp,
        countableChoiceBoundaryToEventFlow x = countableChoiceBoundaryToEventFlow y -> x = y) ∧
      countableChoiceBoundaryFields
        (CountableChoiceBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact countableChoiceBoundary_decode_encode_bhist
  constructor
  · exact countableChoiceBoundary_round_trip
  constructor
  · intro x y heq
    exact countableChoiceBoundaryToEventFlow_injective heq
  · rfl

end BEDC.Derived.CountableChoiceBoundaryUp.TasteGate
