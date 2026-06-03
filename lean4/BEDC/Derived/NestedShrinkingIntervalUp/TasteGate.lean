import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NestedShrinkingIntervalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NestedShrinkingIntervalUp : Type where
  | mk (J0 J1 W D R E H C P N : BHist) : NestedShrinkingIntervalUp
  deriving DecidableEq

def nestedShrinkingIntervalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: nestedShrinkingIntervalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: nestedShrinkingIntervalEncodeBHist h

def nestedShrinkingIntervalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (nestedShrinkingIntervalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (nestedShrinkingIntervalDecodeBHist tail)

private theorem nestedShrinkingInterval_decode_encode_bhist :
    ∀ h : BHist, nestedShrinkingIntervalDecodeBHist
      (nestedShrinkingIntervalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def nestedShrinkingIntervalFields : NestedShrinkingIntervalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NestedShrinkingIntervalUp.mk J0 J1 W D R E H C P N =>
      [J0, J1, W, D, R, E, H, C, P, N]

def nestedShrinkingIntervalToEventFlow : NestedShrinkingIntervalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (nestedShrinkingIntervalFields x).map nestedShrinkingIntervalEncodeBHist

private def nestedShrinkingIntervalEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => nestedShrinkingIntervalEventAtDefault index rest

def nestedShrinkingIntervalFromEventFlow : EventFlow → Option NestedShrinkingIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (NestedShrinkingIntervalUp.mk
        (nestedShrinkingIntervalDecodeBHist (nestedShrinkingIntervalEventAtDefault 0 ef))
        (nestedShrinkingIntervalDecodeBHist (nestedShrinkingIntervalEventAtDefault 1 ef))
        (nestedShrinkingIntervalDecodeBHist (nestedShrinkingIntervalEventAtDefault 2 ef))
        (nestedShrinkingIntervalDecodeBHist (nestedShrinkingIntervalEventAtDefault 3 ef))
        (nestedShrinkingIntervalDecodeBHist (nestedShrinkingIntervalEventAtDefault 4 ef))
        (nestedShrinkingIntervalDecodeBHist (nestedShrinkingIntervalEventAtDefault 5 ef))
        (nestedShrinkingIntervalDecodeBHist (nestedShrinkingIntervalEventAtDefault 6 ef))
        (nestedShrinkingIntervalDecodeBHist (nestedShrinkingIntervalEventAtDefault 7 ef))
        (nestedShrinkingIntervalDecodeBHist (nestedShrinkingIntervalEventAtDefault 8 ef))
        (nestedShrinkingIntervalDecodeBHist (nestedShrinkingIntervalEventAtDefault 9 ef)))

private theorem nestedShrinkingInterval_round_trip :
    ∀ x : NestedShrinkingIntervalUp,
      nestedShrinkingIntervalFromEventFlow
        (nestedShrinkingIntervalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk J0 J1 W D R E H C P N =>
      change
        some
          (NestedShrinkingIntervalUp.mk
            (nestedShrinkingIntervalDecodeBHist (nestedShrinkingIntervalEncodeBHist J0))
            (nestedShrinkingIntervalDecodeBHist (nestedShrinkingIntervalEncodeBHist J1))
            (nestedShrinkingIntervalDecodeBHist (nestedShrinkingIntervalEncodeBHist W))
            (nestedShrinkingIntervalDecodeBHist (nestedShrinkingIntervalEncodeBHist D))
            (nestedShrinkingIntervalDecodeBHist (nestedShrinkingIntervalEncodeBHist R))
            (nestedShrinkingIntervalDecodeBHist (nestedShrinkingIntervalEncodeBHist E))
            (nestedShrinkingIntervalDecodeBHist (nestedShrinkingIntervalEncodeBHist H))
            (nestedShrinkingIntervalDecodeBHist (nestedShrinkingIntervalEncodeBHist C))
            (nestedShrinkingIntervalDecodeBHist (nestedShrinkingIntervalEncodeBHist P))
            (nestedShrinkingIntervalDecodeBHist (nestedShrinkingIntervalEncodeBHist N))) =
          some (NestedShrinkingIntervalUp.mk J0 J1 W D R E H C P N)
      rw [nestedShrinkingInterval_decode_encode_bhist J0,
        nestedShrinkingInterval_decode_encode_bhist J1,
        nestedShrinkingInterval_decode_encode_bhist W,
        nestedShrinkingInterval_decode_encode_bhist D,
        nestedShrinkingInterval_decode_encode_bhist R,
        nestedShrinkingInterval_decode_encode_bhist E,
        nestedShrinkingInterval_decode_encode_bhist H,
        nestedShrinkingInterval_decode_encode_bhist C,
        nestedShrinkingInterval_decode_encode_bhist P,
        nestedShrinkingInterval_decode_encode_bhist N]

private theorem nestedShrinkingIntervalToEventFlow_injective
    {x y : NestedShrinkingIntervalUp} :
    nestedShrinkingIntervalToEventFlow x = nestedShrinkingIntervalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      nestedShrinkingIntervalFromEventFlow (nestedShrinkingIntervalToEventFlow x) =
        nestedShrinkingIntervalFromEventFlow (nestedShrinkingIntervalToEventFlow y) :=
    congrArg nestedShrinkingIntervalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (nestedShrinkingInterval_round_trip x).symm
      (Eq.trans hread (nestedShrinkingInterval_round_trip y)))

instance nestedShrinkingIntervalBHistCarrier : BHistCarrier NestedShrinkingIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := nestedShrinkingIntervalToEventFlow
  fromEventFlow := nestedShrinkingIntervalFromEventFlow

instance nestedShrinkingIntervalChapterTasteGate :
    ChapterTasteGate NestedShrinkingIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change nestedShrinkingIntervalFromEventFlow
      (nestedShrinkingIntervalToEventFlow x) = some x
    exact nestedShrinkingInterval_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (nestedShrinkingIntervalToEventFlow_injective heq)

theorem NestedShrinkingIntervalTasteGate_single_carrier_alignment :
    (∀ h : BHist, nestedShrinkingIntervalDecodeBHist
      (nestedShrinkingIntervalEncodeBHist h) = h) ∧
      (∀ x : NestedShrinkingIntervalUp,
        nestedShrinkingIntervalFromEventFlow
          (nestedShrinkingIntervalToEventFlow x) = some x) ∧
        (∀ x y : NestedShrinkingIntervalUp,
          nestedShrinkingIntervalToEventFlow x = nestedShrinkingIntervalToEventFlow y →
            x = y) ∧
          nestedShrinkingIntervalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨nestedShrinkingInterval_decode_encode_bhist,
      nestedShrinkingInterval_round_trip,
      (fun _ _ heq => nestedShrinkingIntervalToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.NestedShrinkingIntervalUp
