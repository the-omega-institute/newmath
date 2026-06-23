import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NestedIntervalCauchySealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NestedIntervalCauchySealUp : Type where
  | mk (I D S R E H C P N : BHist) : NestedIntervalCauchySealUp
  deriving DecidableEq

def nestedIntervalCauchySealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: nestedIntervalCauchySealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: nestedIntervalCauchySealEncodeBHist h

def nestedIntervalCauchySealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (nestedIntervalCauchySealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (nestedIntervalCauchySealDecodeBHist tail)

private theorem nestedIntervalCauchySeal_decode_encode_bhist :
    ∀ h : BHist,
      nestedIntervalCauchySealDecodeBHist (nestedIntervalCauchySealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def nestedIntervalCauchySealFields : NestedIntervalCauchySealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NestedIntervalCauchySealUp.mk I D S R E H C P N => [I, D, S, R, E, H, C, P, N]

def nestedIntervalCauchySealToEventFlow : NestedIntervalCauchySealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (nestedIntervalCauchySealFields x).map nestedIntervalCauchySealEncodeBHist

private def nestedIntervalCauchySealEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => nestedIntervalCauchySealEventAtDefault index rest

def nestedIntervalCauchySealFromEventFlow
    (ef : EventFlow) : Option NestedIntervalCauchySealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (NestedIntervalCauchySealUp.mk
      (nestedIntervalCauchySealDecodeBHist (nestedIntervalCauchySealEventAtDefault 0 ef))
      (nestedIntervalCauchySealDecodeBHist (nestedIntervalCauchySealEventAtDefault 1 ef))
      (nestedIntervalCauchySealDecodeBHist (nestedIntervalCauchySealEventAtDefault 2 ef))
      (nestedIntervalCauchySealDecodeBHist (nestedIntervalCauchySealEventAtDefault 3 ef))
      (nestedIntervalCauchySealDecodeBHist (nestedIntervalCauchySealEventAtDefault 4 ef))
      (nestedIntervalCauchySealDecodeBHist (nestedIntervalCauchySealEventAtDefault 5 ef))
      (nestedIntervalCauchySealDecodeBHist (nestedIntervalCauchySealEventAtDefault 6 ef))
      (nestedIntervalCauchySealDecodeBHist (nestedIntervalCauchySealEventAtDefault 7 ef))
      (nestedIntervalCauchySealDecodeBHist (nestedIntervalCauchySealEventAtDefault 8 ef)))

private theorem nestedIntervalCauchySeal_round_trip :
    ∀ x : NestedIntervalCauchySealUp,
      nestedIntervalCauchySealFromEventFlow
          (nestedIntervalCauchySealToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I D S R E H C P N =>
      change
        some
          (NestedIntervalCauchySealUp.mk
            (nestedIntervalCauchySealDecodeBHist (nestedIntervalCauchySealEncodeBHist I))
            (nestedIntervalCauchySealDecodeBHist (nestedIntervalCauchySealEncodeBHist D))
            (nestedIntervalCauchySealDecodeBHist (nestedIntervalCauchySealEncodeBHist S))
            (nestedIntervalCauchySealDecodeBHist (nestedIntervalCauchySealEncodeBHist R))
            (nestedIntervalCauchySealDecodeBHist (nestedIntervalCauchySealEncodeBHist E))
            (nestedIntervalCauchySealDecodeBHist (nestedIntervalCauchySealEncodeBHist H))
            (nestedIntervalCauchySealDecodeBHist (nestedIntervalCauchySealEncodeBHist C))
            (nestedIntervalCauchySealDecodeBHist (nestedIntervalCauchySealEncodeBHist P))
            (nestedIntervalCauchySealDecodeBHist (nestedIntervalCauchySealEncodeBHist N))) =
          some (NestedIntervalCauchySealUp.mk I D S R E H C P N)
      rw [nestedIntervalCauchySeal_decode_encode_bhist I,
        nestedIntervalCauchySeal_decode_encode_bhist D,
        nestedIntervalCauchySeal_decode_encode_bhist S,
        nestedIntervalCauchySeal_decode_encode_bhist R,
        nestedIntervalCauchySeal_decode_encode_bhist E,
        nestedIntervalCauchySeal_decode_encode_bhist H,
        nestedIntervalCauchySeal_decode_encode_bhist C,
        nestedIntervalCauchySeal_decode_encode_bhist P,
        nestedIntervalCauchySeal_decode_encode_bhist N]

private theorem nestedIntervalCauchySealToEventFlow_injective
    {x y : NestedIntervalCauchySealUp} :
    nestedIntervalCauchySealToEventFlow x =
      nestedIntervalCauchySealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      nestedIntervalCauchySealFromEventFlow (nestedIntervalCauchySealToEventFlow x) =
        nestedIntervalCauchySealFromEventFlow (nestedIntervalCauchySealToEventFlow y) :=
    congrArg nestedIntervalCauchySealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (nestedIntervalCauchySeal_round_trip x).symm
      (Eq.trans hread (nestedIntervalCauchySeal_round_trip y)))

instance nestedIntervalCauchySealBHistCarrier :
    BHistCarrier NestedIntervalCauchySealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := nestedIntervalCauchySealToEventFlow
  fromEventFlow := nestedIntervalCauchySealFromEventFlow

instance nestedIntervalCauchySealChapterTasteGate :
    ChapterTasteGate NestedIntervalCauchySealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      nestedIntervalCauchySealFromEventFlow (nestedIntervalCauchySealToEventFlow x) =
        some x
    exact nestedIntervalCauchySeal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (nestedIntervalCauchySealToEventFlow_injective heq)

theorem NestedIntervalCauchySealTasteGate_single_carrier_alignment :
    (forall h : BHist,
      nestedIntervalCauchySealDecodeBHist (nestedIntervalCauchySealEncodeBHist h) = h) ∧
      (forall x : NestedIntervalCauchySealUp,
        nestedIntervalCauchySealFromEventFlow
            (nestedIntervalCauchySealToEventFlow x) =
          some x) ∧
        nestedIntervalCauchySealEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact ⟨nestedIntervalCauchySeal_decode_encode_bhist,
    nestedIntervalCauchySeal_round_trip, rfl⟩

end BEDC.Derived.NestedIntervalCauchySealUp
