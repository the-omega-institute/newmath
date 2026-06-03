import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NestedIntervalCauchyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NestedIntervalCauchyUp : Type where
  | mk (I D W S R E H C P N : BHist) : NestedIntervalCauchyUp
  deriving DecidableEq

def nestedIntervalCauchyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: nestedIntervalCauchyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: nestedIntervalCauchyEncodeBHist h

def nestedIntervalCauchyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (nestedIntervalCauchyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (nestedIntervalCauchyDecodeBHist tail)

private theorem nestedIntervalCauchy_decode_encode_bhist :
    ∀ h : BHist, nestedIntervalCauchyDecodeBHist (nestedIntervalCauchyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def nestedIntervalCauchyToEventFlow : NestedIntervalCauchyUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | NestedIntervalCauchyUp.mk I D W S R E H C P N =>
      [nestedIntervalCauchyEncodeBHist I,
        nestedIntervalCauchyEncodeBHist D,
        nestedIntervalCauchyEncodeBHist W,
        nestedIntervalCauchyEncodeBHist S,
        nestedIntervalCauchyEncodeBHist R,
        nestedIntervalCauchyEncodeBHist E,
        nestedIntervalCauchyEncodeBHist H,
        nestedIntervalCauchyEncodeBHist C,
        nestedIntervalCauchyEncodeBHist P,
        nestedIntervalCauchyEncodeBHist N]

private def nestedIntervalCauchyEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => nestedIntervalCauchyEventAtDefault index rest

def nestedIntervalCauchyFromEventFlow (ef : EventFlow) : Option NestedIntervalCauchyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (NestedIntervalCauchyUp.mk
      (nestedIntervalCauchyDecodeBHist (nestedIntervalCauchyEventAtDefault 0 ef))
      (nestedIntervalCauchyDecodeBHist (nestedIntervalCauchyEventAtDefault 1 ef))
      (nestedIntervalCauchyDecodeBHist (nestedIntervalCauchyEventAtDefault 2 ef))
      (nestedIntervalCauchyDecodeBHist (nestedIntervalCauchyEventAtDefault 3 ef))
      (nestedIntervalCauchyDecodeBHist (nestedIntervalCauchyEventAtDefault 4 ef))
      (nestedIntervalCauchyDecodeBHist (nestedIntervalCauchyEventAtDefault 5 ef))
      (nestedIntervalCauchyDecodeBHist (nestedIntervalCauchyEventAtDefault 6 ef))
      (nestedIntervalCauchyDecodeBHist (nestedIntervalCauchyEventAtDefault 7 ef))
      (nestedIntervalCauchyDecodeBHist (nestedIntervalCauchyEventAtDefault 8 ef))
      (nestedIntervalCauchyDecodeBHist (nestedIntervalCauchyEventAtDefault 9 ef)))

private theorem nestedIntervalCauchy_round_trip :
    ∀ x : NestedIntervalCauchyUp,
      nestedIntervalCauchyFromEventFlow (nestedIntervalCauchyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I D W S R E H C P N =>
      change
        some
          (NestedIntervalCauchyUp.mk
            (nestedIntervalCauchyDecodeBHist (nestedIntervalCauchyEncodeBHist I))
            (nestedIntervalCauchyDecodeBHist (nestedIntervalCauchyEncodeBHist D))
            (nestedIntervalCauchyDecodeBHist (nestedIntervalCauchyEncodeBHist W))
            (nestedIntervalCauchyDecodeBHist (nestedIntervalCauchyEncodeBHist S))
            (nestedIntervalCauchyDecodeBHist (nestedIntervalCauchyEncodeBHist R))
            (nestedIntervalCauchyDecodeBHist (nestedIntervalCauchyEncodeBHist E))
            (nestedIntervalCauchyDecodeBHist (nestedIntervalCauchyEncodeBHist H))
            (nestedIntervalCauchyDecodeBHist (nestedIntervalCauchyEncodeBHist C))
            (nestedIntervalCauchyDecodeBHist (nestedIntervalCauchyEncodeBHist P))
            (nestedIntervalCauchyDecodeBHist (nestedIntervalCauchyEncodeBHist N))) =
          some (NestedIntervalCauchyUp.mk I D W S R E H C P N)
      rw [nestedIntervalCauchy_decode_encode_bhist I,
        nestedIntervalCauchy_decode_encode_bhist D,
        nestedIntervalCauchy_decode_encode_bhist W,
        nestedIntervalCauchy_decode_encode_bhist S,
        nestedIntervalCauchy_decode_encode_bhist R,
        nestedIntervalCauchy_decode_encode_bhist E,
        nestedIntervalCauchy_decode_encode_bhist H,
        nestedIntervalCauchy_decode_encode_bhist C,
        nestedIntervalCauchy_decode_encode_bhist P,
        nestedIntervalCauchy_decode_encode_bhist N]

private theorem nestedIntervalCauchyToEventFlow_injective
    {x y : NestedIntervalCauchyUp} :
    nestedIntervalCauchyToEventFlow x = nestedIntervalCauchyToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      nestedIntervalCauchyFromEventFlow (nestedIntervalCauchyToEventFlow x) =
        nestedIntervalCauchyFromEventFlow (nestedIntervalCauchyToEventFlow y) :=
    congrArg nestedIntervalCauchyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (nestedIntervalCauchy_round_trip x).symm
      (Eq.trans hread (nestedIntervalCauchy_round_trip y)))

instance nestedIntervalCauchyBHistCarrier : BHistCarrier NestedIntervalCauchyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := nestedIntervalCauchyToEventFlow
  fromEventFlow := nestedIntervalCauchyFromEventFlow

instance nestedIntervalCauchyChapterTasteGate : ChapterTasteGate NestedIntervalCauchyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change nestedIntervalCauchyFromEventFlow (nestedIntervalCauchyToEventFlow x) = some x
    exact nestedIntervalCauchy_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (nestedIntervalCauchyToEventFlow_injective heq)

def taste_gate : ChapterTasteGate NestedIntervalCauchyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  nestedIntervalCauchyChapterTasteGate

theorem NestedIntervalCauchyTasteGate_single_carrier_alignment :
    (∀ h : BHist, nestedIntervalCauchyDecodeBHist (nestedIntervalCauchyEncodeBHist h) = h) ∧
      (∀ x : NestedIntervalCauchyUp,
        nestedIntervalCauchyFromEventFlow (nestedIntervalCauchyToEventFlow x) = some x) ∧
        (∀ x y : NestedIntervalCauchyUp,
          nestedIntervalCauchyToEventFlow x = nestedIntervalCauchyToEventFlow y → x = y) ∧
          nestedIntervalCauchyEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact nestedIntervalCauchy_decode_encode_bhist
  · constructor
    · exact nestedIntervalCauchy_round_trip
    · constructor
      · intro x y heq
        exact nestedIntervalCauchyToEventFlow_injective heq
      · rfl

end BEDC.Derived.NestedIntervalCauchyUp
