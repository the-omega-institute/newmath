import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedApartnessCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedApartnessCompletionUp : Type where
  | mk (A B U V G S R D E H C P N : BHist) : LocatedApartnessCompletionUp
  deriving DecidableEq

def locatedApartnessCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedApartnessCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedApartnessCompletionEncodeBHist h

def locatedApartnessCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedApartnessCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedApartnessCompletionDecodeBHist tail)

private theorem locatedApartnessCompletionDecodeEncode :
    ∀ h : BHist,
      locatedApartnessCompletionDecodeBHist
        (locatedApartnessCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedApartnessCompletionFields : LocatedApartnessCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedApartnessCompletionUp.mk A B U V G S R D E H C P N =>
      [A, B, U, V, G, S, R, D, E, H, C, P, N]

def locatedApartnessCompletionToEventFlow : LocatedApartnessCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedApartnessCompletionFields x).map locatedApartnessCompletionEncodeBHist

private def locatedApartnessCompletionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedApartnessCompletionEventAtDefault index rest

def locatedApartnessCompletionFromEventFlow :
    EventFlow → Option LocatedApartnessCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (LocatedApartnessCompletionUp.mk
        (locatedApartnessCompletionDecodeBHist
          (locatedApartnessCompletionEventAtDefault 0 ef))
        (locatedApartnessCompletionDecodeBHist
          (locatedApartnessCompletionEventAtDefault 1 ef))
        (locatedApartnessCompletionDecodeBHist
          (locatedApartnessCompletionEventAtDefault 2 ef))
        (locatedApartnessCompletionDecodeBHist
          (locatedApartnessCompletionEventAtDefault 3 ef))
        (locatedApartnessCompletionDecodeBHist
          (locatedApartnessCompletionEventAtDefault 4 ef))
        (locatedApartnessCompletionDecodeBHist
          (locatedApartnessCompletionEventAtDefault 5 ef))
        (locatedApartnessCompletionDecodeBHist
          (locatedApartnessCompletionEventAtDefault 6 ef))
        (locatedApartnessCompletionDecodeBHist
          (locatedApartnessCompletionEventAtDefault 7 ef))
        (locatedApartnessCompletionDecodeBHist
          (locatedApartnessCompletionEventAtDefault 8 ef))
        (locatedApartnessCompletionDecodeBHist
          (locatedApartnessCompletionEventAtDefault 9 ef))
        (locatedApartnessCompletionDecodeBHist
          (locatedApartnessCompletionEventAtDefault 10 ef))
        (locatedApartnessCompletionDecodeBHist
          (locatedApartnessCompletionEventAtDefault 11 ef))
        (locatedApartnessCompletionDecodeBHist
          (locatedApartnessCompletionEventAtDefault 12 ef)))

private theorem locatedApartnessCompletionRoundTrip :
    ∀ x : LocatedApartnessCompletionUp,
      locatedApartnessCompletionFromEventFlow
        (locatedApartnessCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A B U V G S R D E H C P N =>
      change
        some
          (LocatedApartnessCompletionUp.mk
            (locatedApartnessCompletionDecodeBHist
              (locatedApartnessCompletionEncodeBHist A))
            (locatedApartnessCompletionDecodeBHist
              (locatedApartnessCompletionEncodeBHist B))
            (locatedApartnessCompletionDecodeBHist
              (locatedApartnessCompletionEncodeBHist U))
            (locatedApartnessCompletionDecodeBHist
              (locatedApartnessCompletionEncodeBHist V))
            (locatedApartnessCompletionDecodeBHist
              (locatedApartnessCompletionEncodeBHist G))
            (locatedApartnessCompletionDecodeBHist
              (locatedApartnessCompletionEncodeBHist S))
            (locatedApartnessCompletionDecodeBHist
              (locatedApartnessCompletionEncodeBHist R))
            (locatedApartnessCompletionDecodeBHist
              (locatedApartnessCompletionEncodeBHist D))
            (locatedApartnessCompletionDecodeBHist
              (locatedApartnessCompletionEncodeBHist E))
            (locatedApartnessCompletionDecodeBHist
              (locatedApartnessCompletionEncodeBHist H))
            (locatedApartnessCompletionDecodeBHist
              (locatedApartnessCompletionEncodeBHist C))
            (locatedApartnessCompletionDecodeBHist
              (locatedApartnessCompletionEncodeBHist P))
            (locatedApartnessCompletionDecodeBHist
              (locatedApartnessCompletionEncodeBHist N))) =
          some (LocatedApartnessCompletionUp.mk A B U V G S R D E H C P N)
      rw [locatedApartnessCompletionDecodeEncode A,
        locatedApartnessCompletionDecodeEncode B,
        locatedApartnessCompletionDecodeEncode U,
        locatedApartnessCompletionDecodeEncode V,
        locatedApartnessCompletionDecodeEncode G,
        locatedApartnessCompletionDecodeEncode S,
        locatedApartnessCompletionDecodeEncode R,
        locatedApartnessCompletionDecodeEncode D,
        locatedApartnessCompletionDecodeEncode E,
        locatedApartnessCompletionDecodeEncode H,
        locatedApartnessCompletionDecodeEncode C,
        locatedApartnessCompletionDecodeEncode P,
        locatedApartnessCompletionDecodeEncode N]

private theorem locatedApartnessCompletionToEventFlow_injective
    {x y : LocatedApartnessCompletionUp} :
    locatedApartnessCompletionToEventFlow x =
      locatedApartnessCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedApartnessCompletionFromEventFlow
          (locatedApartnessCompletionToEventFlow x) =
        locatedApartnessCompletionFromEventFlow
          (locatedApartnessCompletionToEventFlow y) :=
    congrArg locatedApartnessCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (locatedApartnessCompletionRoundTrip x).symm
      (Eq.trans hread (locatedApartnessCompletionRoundTrip y)))

instance locatedApartnessCompletionBHistCarrier :
    BHistCarrier LocatedApartnessCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedApartnessCompletionToEventFlow
  fromEventFlow := locatedApartnessCompletionFromEventFlow

instance locatedApartnessCompletionChapterTasteGate :
    ChapterTasteGate LocatedApartnessCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      locatedApartnessCompletionFromEventFlow
          (locatedApartnessCompletionToEventFlow x) =
        some x
    exact locatedApartnessCompletionRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedApartnessCompletionToEventFlow_injective heq)

theorem LocatedApartnessCompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      locatedApartnessCompletionDecodeBHist
        (locatedApartnessCompletionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier LocatedApartnessCompletionUp) ∧
        Nonempty (ChapterTasteGate LocatedApartnessCompletionUp) ∧
          locatedApartnessCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨locatedApartnessCompletionDecodeEncode,
      ⟨locatedApartnessCompletionBHistCarrier⟩,
      ⟨locatedApartnessCompletionChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.LocatedApartnessCompletionUp
