import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedOrderIntervalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedOrderIntervalUp : Type where
  | mk (L U G D S R E H C P N : BHist) : LocatedOrderIntervalUp
  deriving DecidableEq

def locatedOrderIntervalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedOrderIntervalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedOrderIntervalEncodeBHist h

def locatedOrderIntervalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedOrderIntervalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedOrderIntervalDecodeBHist tail)

private theorem locatedOrderInterval_decode_encode_bhist :
    ∀ h : BHist, locatedOrderIntervalDecodeBHist (locatedOrderIntervalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedOrderIntervalFields : LocatedOrderIntervalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedOrderIntervalUp.mk L U G D S R E H C P N => [L, U, G, D, S, R, E, H, C, P, N]

def locatedOrderIntervalToEventFlow : LocatedOrderIntervalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedOrderIntervalFields x).map locatedOrderIntervalEncodeBHist

private def locatedOrderIntervalEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedOrderIntervalEventAtDefault index rest

def locatedOrderIntervalFromEventFlow (ef : EventFlow) : Option LocatedOrderIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedOrderIntervalUp.mk
      (locatedOrderIntervalDecodeBHist (locatedOrderIntervalEventAtDefault 0 ef))
      (locatedOrderIntervalDecodeBHist (locatedOrderIntervalEventAtDefault 1 ef))
      (locatedOrderIntervalDecodeBHist (locatedOrderIntervalEventAtDefault 2 ef))
      (locatedOrderIntervalDecodeBHist (locatedOrderIntervalEventAtDefault 3 ef))
      (locatedOrderIntervalDecodeBHist (locatedOrderIntervalEventAtDefault 4 ef))
      (locatedOrderIntervalDecodeBHist (locatedOrderIntervalEventAtDefault 5 ef))
      (locatedOrderIntervalDecodeBHist (locatedOrderIntervalEventAtDefault 6 ef))
      (locatedOrderIntervalDecodeBHist (locatedOrderIntervalEventAtDefault 7 ef))
      (locatedOrderIntervalDecodeBHist (locatedOrderIntervalEventAtDefault 8 ef))
      (locatedOrderIntervalDecodeBHist (locatedOrderIntervalEventAtDefault 9 ef))
      (locatedOrderIntervalDecodeBHist (locatedOrderIntervalEventAtDefault 10 ef)))

private theorem locatedOrderInterval_round_trip :
    ∀ x : LocatedOrderIntervalUp,
      locatedOrderIntervalFromEventFlow (locatedOrderIntervalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L U G D S R E H C P N =>
      change
        some
          (LocatedOrderIntervalUp.mk
            (locatedOrderIntervalDecodeBHist (locatedOrderIntervalEncodeBHist L))
            (locatedOrderIntervalDecodeBHist (locatedOrderIntervalEncodeBHist U))
            (locatedOrderIntervalDecodeBHist (locatedOrderIntervalEncodeBHist G))
            (locatedOrderIntervalDecodeBHist (locatedOrderIntervalEncodeBHist D))
            (locatedOrderIntervalDecodeBHist (locatedOrderIntervalEncodeBHist S))
            (locatedOrderIntervalDecodeBHist (locatedOrderIntervalEncodeBHist R))
            (locatedOrderIntervalDecodeBHist (locatedOrderIntervalEncodeBHist E))
            (locatedOrderIntervalDecodeBHist (locatedOrderIntervalEncodeBHist H))
            (locatedOrderIntervalDecodeBHist (locatedOrderIntervalEncodeBHist C))
            (locatedOrderIntervalDecodeBHist (locatedOrderIntervalEncodeBHist P))
            (locatedOrderIntervalDecodeBHist (locatedOrderIntervalEncodeBHist N))) =
          some (LocatedOrderIntervalUp.mk L U G D S R E H C P N)
      rw [locatedOrderInterval_decode_encode_bhist L,
        locatedOrderInterval_decode_encode_bhist U,
        locatedOrderInterval_decode_encode_bhist G,
        locatedOrderInterval_decode_encode_bhist D,
        locatedOrderInterval_decode_encode_bhist S,
        locatedOrderInterval_decode_encode_bhist R,
        locatedOrderInterval_decode_encode_bhist E,
        locatedOrderInterval_decode_encode_bhist H,
        locatedOrderInterval_decode_encode_bhist C,
        locatedOrderInterval_decode_encode_bhist P,
        locatedOrderInterval_decode_encode_bhist N]

private theorem locatedOrderIntervalToEventFlow_injective {x y : LocatedOrderIntervalUp} :
    locatedOrderIntervalToEventFlow x = locatedOrderIntervalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedOrderIntervalFromEventFlow (locatedOrderIntervalToEventFlow x) =
        locatedOrderIntervalFromEventFlow (locatedOrderIntervalToEventFlow y) :=
    congrArg locatedOrderIntervalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (locatedOrderInterval_round_trip x).symm
      (Eq.trans hread (locatedOrderInterval_round_trip y)))

instance locatedOrderIntervalBHistCarrier : BHistCarrier LocatedOrderIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedOrderIntervalToEventFlow
  fromEventFlow := locatedOrderIntervalFromEventFlow

instance locatedOrderIntervalChapterTasteGate : ChapterTasteGate LocatedOrderIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedOrderIntervalFromEventFlow (locatedOrderIntervalToEventFlow x) = some x
    exact locatedOrderInterval_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedOrderIntervalToEventFlow_injective heq)

def taste_gate : ChapterTasteGate LocatedOrderIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedOrderIntervalChapterTasteGate

theorem LocatedOrderIntervalTasteGate_single_carrier_alignment :
    (∀ h : BHist, locatedOrderIntervalDecodeBHist (locatedOrderIntervalEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier LocatedOrderIntervalUp) ∧
        Nonempty (ChapterTasteGate LocatedOrderIntervalUp) ∧
          locatedOrderIntervalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨locatedOrderInterval_decode_encode_bhist, Nonempty.intro locatedOrderIntervalBHistCarrier,
      Nonempty.intro locatedOrderIntervalChapterTasteGate, rfl⟩

end BEDC.Derived.LocatedOrderIntervalUp
