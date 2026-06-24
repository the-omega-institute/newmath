import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RationalIntervalSequenceUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RationalIntervalSequenceUp : Type where
  | mk
      (endpoint lower upper nesting width stream readback realSeal transport replay provenance
        name : BHist) :
      RationalIntervalSequenceUp
  deriving DecidableEq

def rationalIntervalSequenceEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: rationalIntervalSequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: rationalIntervalSequenceEncodeBHist h

def rationalIntervalSequenceDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (rationalIntervalSequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (rationalIntervalSequenceDecodeBHist tail)

private theorem rationalIntervalSequence_decode_encode :
    forall h : BHist,
      rationalIntervalSequenceDecodeBHist (rationalIntervalSequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def rationalIntervalSequenceFields : RationalIntervalSequenceUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RationalIntervalSequenceUp.mk endpoint lower upper nesting width stream readback realSeal
      transport replay provenance name =>
      [endpoint, lower, upper, nesting, width, stream, readback, realSeal, transport, replay,
        provenance, name]

def rationalIntervalSequenceToEventFlow : RationalIntervalSequenceUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (rationalIntervalSequenceFields x).map rationalIntervalSequenceEncodeBHist

def rationalIntervalSequenceEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => rationalIntervalSequenceEventAt index rest

def rationalIntervalSequenceFromEventFlow :
    EventFlow -> Option RationalIntervalSequenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      some
        (RationalIntervalSequenceUp.mk
          (rationalIntervalSequenceDecodeBHist (rationalIntervalSequenceEventAt 0 flow))
          (rationalIntervalSequenceDecodeBHist (rationalIntervalSequenceEventAt 1 flow))
          (rationalIntervalSequenceDecodeBHist (rationalIntervalSequenceEventAt 2 flow))
          (rationalIntervalSequenceDecodeBHist (rationalIntervalSequenceEventAt 3 flow))
          (rationalIntervalSequenceDecodeBHist (rationalIntervalSequenceEventAt 4 flow))
          (rationalIntervalSequenceDecodeBHist (rationalIntervalSequenceEventAt 5 flow))
          (rationalIntervalSequenceDecodeBHist (rationalIntervalSequenceEventAt 6 flow))
          (rationalIntervalSequenceDecodeBHist (rationalIntervalSequenceEventAt 7 flow))
          (rationalIntervalSequenceDecodeBHist (rationalIntervalSequenceEventAt 8 flow))
          (rationalIntervalSequenceDecodeBHist (rationalIntervalSequenceEventAt 9 flow))
          (rationalIntervalSequenceDecodeBHist (rationalIntervalSequenceEventAt 10 flow))
          (rationalIntervalSequenceDecodeBHist (rationalIntervalSequenceEventAt 11 flow)))

private theorem rationalIntervalSequence_round_trip :
    forall x : RationalIntervalSequenceUp,
      rationalIntervalSequenceFromEventFlow
        (rationalIntervalSequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk endpoint lower upper nesting width stream readback realSeal transport replay provenance
      name =>
      change
        some
          (RationalIntervalSequenceUp.mk
            (rationalIntervalSequenceDecodeBHist
              (rationalIntervalSequenceEncodeBHist endpoint))
            (rationalIntervalSequenceDecodeBHist (rationalIntervalSequenceEncodeBHist lower))
            (rationalIntervalSequenceDecodeBHist (rationalIntervalSequenceEncodeBHist upper))
            (rationalIntervalSequenceDecodeBHist
              (rationalIntervalSequenceEncodeBHist nesting))
            (rationalIntervalSequenceDecodeBHist (rationalIntervalSequenceEncodeBHist width))
            (rationalIntervalSequenceDecodeBHist (rationalIntervalSequenceEncodeBHist stream))
            (rationalIntervalSequenceDecodeBHist
              (rationalIntervalSequenceEncodeBHist readback))
            (rationalIntervalSequenceDecodeBHist
              (rationalIntervalSequenceEncodeBHist realSeal))
            (rationalIntervalSequenceDecodeBHist
              (rationalIntervalSequenceEncodeBHist transport))
            (rationalIntervalSequenceDecodeBHist (rationalIntervalSequenceEncodeBHist replay))
            (rationalIntervalSequenceDecodeBHist
              (rationalIntervalSequenceEncodeBHist provenance))
            (rationalIntervalSequenceDecodeBHist (rationalIntervalSequenceEncodeBHist name))) =
          some
            (RationalIntervalSequenceUp.mk endpoint lower upper nesting width stream readback
              realSeal transport replay provenance name)
      rw [rationalIntervalSequence_decode_encode endpoint,
        rationalIntervalSequence_decode_encode lower,
        rationalIntervalSequence_decode_encode upper,
        rationalIntervalSequence_decode_encode nesting,
        rationalIntervalSequence_decode_encode width,
        rationalIntervalSequence_decode_encode stream,
        rationalIntervalSequence_decode_encode readback,
        rationalIntervalSequence_decode_encode realSeal,
        rationalIntervalSequence_decode_encode transport,
        rationalIntervalSequence_decode_encode replay,
        rationalIntervalSequence_decode_encode provenance,
        rationalIntervalSequence_decode_encode name]

private theorem rationalIntervalSequenceToEventFlow_injective
    {x y : RationalIntervalSequenceUp} :
    rationalIntervalSequenceToEventFlow x =
      rationalIntervalSequenceToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      rationalIntervalSequenceFromEventFlow (rationalIntervalSequenceToEventFlow x) =
        rationalIntervalSequenceFromEventFlow (rationalIntervalSequenceToEventFlow y) :=
    congrArg rationalIntervalSequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (rationalIntervalSequence_round_trip x).symm
      (Eq.trans hread (rationalIntervalSequence_round_trip y)))

instance rationalIntervalSequenceBHistCarrier :
    BHistCarrier RationalIntervalSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := rationalIntervalSequenceToEventFlow
  fromEventFlow := rationalIntervalSequenceFromEventFlow

instance rationalIntervalSequenceChapterTasteGate :
    ChapterTasteGate RationalIntervalSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change rationalIntervalSequenceFromEventFlow
      (rationalIntervalSequenceToEventFlow x) = some x
    exact rationalIntervalSequence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (rationalIntervalSequenceToEventFlow_injective heq)

theorem RationalIntervalSequenceTasteGate_single_carrier_alignment :
    (forall h : BHist,
      rationalIntervalSequenceDecodeBHist (rationalIntervalSequenceEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RationalIntervalSequenceUp) ∧
        Nonempty (ChapterTasteGate RationalIntervalSequenceUp) ∧
          rationalIntervalSequenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨rationalIntervalSequence_decode_encode,
      ⟨rationalIntervalSequenceBHistCarrier⟩,
      ⟨rationalIntervalSequenceChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.RationalIntervalSequenceUp.TasteGate
