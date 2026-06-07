import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopLocatedCompletionBoundaryUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopLocatedCompletionBoundaryUp : Type where
  | mk (S Q D R L E T H C P N : BHist) : BishopLocatedCompletionBoundaryUp
  deriving DecidableEq

def bishopLocatedCompletionBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopLocatedCompletionBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopLocatedCompletionBoundaryEncodeBHist h

def bishopLocatedCompletionBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopLocatedCompletionBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopLocatedCompletionBoundaryDecodeBHist tail)

private theorem bishopLocatedCompletionBoundary_decode_encode_bhist :
    ∀ h : BHist,
      bishopLocatedCompletionBoundaryDecodeBHist
          (bishopLocatedCompletionBoundaryEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopLocatedCompletionBoundaryToEventFlow :
    BishopLocatedCompletionBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BishopLocatedCompletionBoundaryUp.mk S Q D R L E T H C P N =>
      [bishopLocatedCompletionBoundaryEncodeBHist S,
        bishopLocatedCompletionBoundaryEncodeBHist Q,
        bishopLocatedCompletionBoundaryEncodeBHist D,
        bishopLocatedCompletionBoundaryEncodeBHist R,
        bishopLocatedCompletionBoundaryEncodeBHist L,
        bishopLocatedCompletionBoundaryEncodeBHist E,
        bishopLocatedCompletionBoundaryEncodeBHist T,
        bishopLocatedCompletionBoundaryEncodeBHist H,
        bishopLocatedCompletionBoundaryEncodeBHist C,
        bishopLocatedCompletionBoundaryEncodeBHist P,
        bishopLocatedCompletionBoundaryEncodeBHist N]

private def bishopLocatedCompletionBoundaryEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopLocatedCompletionBoundaryEventAt index rest

def bishopLocatedCompletionBoundaryFromEventFlow :
    EventFlow → Option BishopLocatedCompletionBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (BishopLocatedCompletionBoundaryUp.mk
        (bishopLocatedCompletionBoundaryDecodeBHist
          (bishopLocatedCompletionBoundaryEventAt 0 ef))
        (bishopLocatedCompletionBoundaryDecodeBHist
          (bishopLocatedCompletionBoundaryEventAt 1 ef))
        (bishopLocatedCompletionBoundaryDecodeBHist
          (bishopLocatedCompletionBoundaryEventAt 2 ef))
        (bishopLocatedCompletionBoundaryDecodeBHist
          (bishopLocatedCompletionBoundaryEventAt 3 ef))
        (bishopLocatedCompletionBoundaryDecodeBHist
          (bishopLocatedCompletionBoundaryEventAt 4 ef))
        (bishopLocatedCompletionBoundaryDecodeBHist
          (bishopLocatedCompletionBoundaryEventAt 5 ef))
        (bishopLocatedCompletionBoundaryDecodeBHist
          (bishopLocatedCompletionBoundaryEventAt 6 ef))
        (bishopLocatedCompletionBoundaryDecodeBHist
          (bishopLocatedCompletionBoundaryEventAt 7 ef))
        (bishopLocatedCompletionBoundaryDecodeBHist
          (bishopLocatedCompletionBoundaryEventAt 8 ef))
        (bishopLocatedCompletionBoundaryDecodeBHist
          (bishopLocatedCompletionBoundaryEventAt 9 ef))
        (bishopLocatedCompletionBoundaryDecodeBHist
          (bishopLocatedCompletionBoundaryEventAt 10 ef)))

private theorem bishopLocatedCompletionBoundary_round_trip :
    ∀ x : BishopLocatedCompletionBoundaryUp,
      bishopLocatedCompletionBoundaryFromEventFlow
          (bishopLocatedCompletionBoundaryToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S Q D R L E T H C P N =>
      change
        some
            (BishopLocatedCompletionBoundaryUp.mk
              (bishopLocatedCompletionBoundaryDecodeBHist
                (bishopLocatedCompletionBoundaryEncodeBHist S))
              (bishopLocatedCompletionBoundaryDecodeBHist
                (bishopLocatedCompletionBoundaryEncodeBHist Q))
              (bishopLocatedCompletionBoundaryDecodeBHist
                (bishopLocatedCompletionBoundaryEncodeBHist D))
              (bishopLocatedCompletionBoundaryDecodeBHist
                (bishopLocatedCompletionBoundaryEncodeBHist R))
              (bishopLocatedCompletionBoundaryDecodeBHist
                (bishopLocatedCompletionBoundaryEncodeBHist L))
              (bishopLocatedCompletionBoundaryDecodeBHist
                (bishopLocatedCompletionBoundaryEncodeBHist E))
              (bishopLocatedCompletionBoundaryDecodeBHist
                (bishopLocatedCompletionBoundaryEncodeBHist T))
              (bishopLocatedCompletionBoundaryDecodeBHist
                (bishopLocatedCompletionBoundaryEncodeBHist H))
              (bishopLocatedCompletionBoundaryDecodeBHist
                (bishopLocatedCompletionBoundaryEncodeBHist C))
              (bishopLocatedCompletionBoundaryDecodeBHist
                (bishopLocatedCompletionBoundaryEncodeBHist P))
              (bishopLocatedCompletionBoundaryDecodeBHist
                (bishopLocatedCompletionBoundaryEncodeBHist N))) =
          some (BishopLocatedCompletionBoundaryUp.mk S Q D R L E T H C P N)
      rw [bishopLocatedCompletionBoundary_decode_encode_bhist S,
        bishopLocatedCompletionBoundary_decode_encode_bhist Q,
        bishopLocatedCompletionBoundary_decode_encode_bhist D,
        bishopLocatedCompletionBoundary_decode_encode_bhist R,
        bishopLocatedCompletionBoundary_decode_encode_bhist L,
        bishopLocatedCompletionBoundary_decode_encode_bhist E,
        bishopLocatedCompletionBoundary_decode_encode_bhist T,
        bishopLocatedCompletionBoundary_decode_encode_bhist H,
        bishopLocatedCompletionBoundary_decode_encode_bhist C,
        bishopLocatedCompletionBoundary_decode_encode_bhist P,
        bishopLocatedCompletionBoundary_decode_encode_bhist N]

private theorem bishopLocatedCompletionBoundaryToEventFlow_injective
    {x y : BishopLocatedCompletionBoundaryUp} :
    bishopLocatedCompletionBoundaryToEventFlow x =
      bishopLocatedCompletionBoundaryToEventFlow y →
    x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopLocatedCompletionBoundaryFromEventFlow
          (bishopLocatedCompletionBoundaryToEventFlow x) =
        bishopLocatedCompletionBoundaryFromEventFlow
          (bishopLocatedCompletionBoundaryToEventFlow y) :=
    congrArg bishopLocatedCompletionBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bishopLocatedCompletionBoundary_round_trip x).symm
      (Eq.trans hread (bishopLocatedCompletionBoundary_round_trip y)))

instance bishopLocatedCompletionBoundaryBHistCarrier :
    BHistCarrier BishopLocatedCompletionBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopLocatedCompletionBoundaryToEventFlow
  fromEventFlow := bishopLocatedCompletionBoundaryFromEventFlow

instance bishopLocatedCompletionBoundaryChapterTasteGate :
    ChapterTasteGate BishopLocatedCompletionBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopLocatedCompletionBoundaryFromEventFlow
          (bishopLocatedCompletionBoundaryToEventFlow x) =
        some x
    exact bishopLocatedCompletionBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bishopLocatedCompletionBoundaryToEventFlow_injective heq)

theorem BishopLocatedCompletionBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      bishopLocatedCompletionBoundaryDecodeBHist
          (bishopLocatedCompletionBoundaryEncodeBHist h) =
        h) ∧
      (∀ x : BishopLocatedCompletionBoundaryUp,
        bishopLocatedCompletionBoundaryFromEventFlow
            (bishopLocatedCompletionBoundaryToEventFlow x) =
          some x) ∧
        bishopLocatedCompletionBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨bishopLocatedCompletionBoundary_decode_encode_bhist,
      bishopLocatedCompletionBoundary_round_trip,
      rfl⟩

end BEDC.Derived.BishopLocatedCompletionBoundaryUp.TasteGate
