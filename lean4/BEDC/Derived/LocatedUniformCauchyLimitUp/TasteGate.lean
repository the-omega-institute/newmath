import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedUniformCauchyLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedUniformCauchyLimitUp : Type where
  | mk (U M S R D E H C P N : BHist) : LocatedUniformCauchyLimitUp
  deriving DecidableEq

def locatedUniformCauchyLimitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedUniformCauchyLimitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedUniformCauchyLimitEncodeBHist h

def locatedUniformCauchyLimitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedUniformCauchyLimitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedUniformCauchyLimitDecodeBHist tail)

private theorem LocatedUniformCauchyLimitTasteGate_decode_encode :
    ∀ h : BHist,
      locatedUniformCauchyLimitDecodeBHist (locatedUniformCauchyLimitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedUniformCauchyLimitToEventFlow :
    LocatedUniformCauchyLimitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedUniformCauchyLimitUp.mk U M S R D E H C P N =>
      [locatedUniformCauchyLimitEncodeBHist U,
        locatedUniformCauchyLimitEncodeBHist M,
        locatedUniformCauchyLimitEncodeBHist S,
        locatedUniformCauchyLimitEncodeBHist R,
        locatedUniformCauchyLimitEncodeBHist D,
        locatedUniformCauchyLimitEncodeBHist E,
        locatedUniformCauchyLimitEncodeBHist H,
        locatedUniformCauchyLimitEncodeBHist C,
        locatedUniformCauchyLimitEncodeBHist P,
        locatedUniformCauchyLimitEncodeBHist N]

private def locatedUniformCauchyLimitEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedUniformCauchyLimitEventAtDefault index rest

def locatedUniformCauchyLimitFromEventFlow
    (ef : EventFlow) : Option LocatedUniformCauchyLimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedUniformCauchyLimitUp.mk
      (locatedUniformCauchyLimitDecodeBHist (locatedUniformCauchyLimitEventAtDefault 0 ef))
      (locatedUniformCauchyLimitDecodeBHist (locatedUniformCauchyLimitEventAtDefault 1 ef))
      (locatedUniformCauchyLimitDecodeBHist (locatedUniformCauchyLimitEventAtDefault 2 ef))
      (locatedUniformCauchyLimitDecodeBHist (locatedUniformCauchyLimitEventAtDefault 3 ef))
      (locatedUniformCauchyLimitDecodeBHist (locatedUniformCauchyLimitEventAtDefault 4 ef))
      (locatedUniformCauchyLimitDecodeBHist (locatedUniformCauchyLimitEventAtDefault 5 ef))
      (locatedUniformCauchyLimitDecodeBHist (locatedUniformCauchyLimitEventAtDefault 6 ef))
      (locatedUniformCauchyLimitDecodeBHist (locatedUniformCauchyLimitEventAtDefault 7 ef))
      (locatedUniformCauchyLimitDecodeBHist (locatedUniformCauchyLimitEventAtDefault 8 ef))
      (locatedUniformCauchyLimitDecodeBHist (locatedUniformCauchyLimitEventAtDefault 9 ef)))

private theorem LocatedUniformCauchyLimitTasteGate_round_trip :
    ∀ x : LocatedUniformCauchyLimitUp,
      locatedUniformCauchyLimitFromEventFlow
        (locatedUniformCauchyLimitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk U M S R D E H C P N =>
      change
        some
          (LocatedUniformCauchyLimitUp.mk
            (locatedUniformCauchyLimitDecodeBHist
              (locatedUniformCauchyLimitEncodeBHist U))
            (locatedUniformCauchyLimitDecodeBHist
              (locatedUniformCauchyLimitEncodeBHist M))
            (locatedUniformCauchyLimitDecodeBHist
              (locatedUniformCauchyLimitEncodeBHist S))
            (locatedUniformCauchyLimitDecodeBHist
              (locatedUniformCauchyLimitEncodeBHist R))
            (locatedUniformCauchyLimitDecodeBHist
              (locatedUniformCauchyLimitEncodeBHist D))
            (locatedUniformCauchyLimitDecodeBHist
              (locatedUniformCauchyLimitEncodeBHist E))
            (locatedUniformCauchyLimitDecodeBHist
              (locatedUniformCauchyLimitEncodeBHist H))
            (locatedUniformCauchyLimitDecodeBHist
              (locatedUniformCauchyLimitEncodeBHist C))
            (locatedUniformCauchyLimitDecodeBHist
              (locatedUniformCauchyLimitEncodeBHist P))
            (locatedUniformCauchyLimitDecodeBHist
              (locatedUniformCauchyLimitEncodeBHist N))) =
          some (LocatedUniformCauchyLimitUp.mk U M S R D E H C P N)
      rw [LocatedUniformCauchyLimitTasteGate_decode_encode U,
        LocatedUniformCauchyLimitTasteGate_decode_encode M,
        LocatedUniformCauchyLimitTasteGate_decode_encode S,
        LocatedUniformCauchyLimitTasteGate_decode_encode R,
        LocatedUniformCauchyLimitTasteGate_decode_encode D,
        LocatedUniformCauchyLimitTasteGate_decode_encode E,
        LocatedUniformCauchyLimitTasteGate_decode_encode H,
        LocatedUniformCauchyLimitTasteGate_decode_encode C,
        LocatedUniformCauchyLimitTasteGate_decode_encode P,
        LocatedUniformCauchyLimitTasteGate_decode_encode N]

private theorem LocatedUniformCauchyLimitTasteGate_toEventFlow_injective
    {x y : LocatedUniformCauchyLimitUp} :
    locatedUniformCauchyLimitToEventFlow x =
      locatedUniformCauchyLimitToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedUniformCauchyLimitFromEventFlow
          (locatedUniformCauchyLimitToEventFlow x) =
        locatedUniformCauchyLimitFromEventFlow
          (locatedUniformCauchyLimitToEventFlow y) :=
    congrArg locatedUniformCauchyLimitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LocatedUniformCauchyLimitTasteGate_round_trip x).symm
      (Eq.trans hread (LocatedUniformCauchyLimitTasteGate_round_trip y)))

instance locatedUniformCauchyLimitBHistCarrier :
    BHistCarrier LocatedUniformCauchyLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedUniformCauchyLimitToEventFlow
  fromEventFlow := locatedUniformCauchyLimitFromEventFlow

instance locatedUniformCauchyLimitChapterTasteGate :
    ChapterTasteGate LocatedUniformCauchyLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      locatedUniformCauchyLimitFromEventFlow
        (locatedUniformCauchyLimitToEventFlow x) = some x
    exact LocatedUniformCauchyLimitTasteGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LocatedUniformCauchyLimitTasteGate_toEventFlow_injective heq)

theorem LocatedUniformCauchyLimitTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      locatedUniformCauchyLimitDecodeBHist (locatedUniformCauchyLimitEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier LocatedUniformCauchyLimitUp) ∧
        Nonempty (ChapterTasteGate LocatedUniformCauchyLimitUp) ∧
          locatedUniformCauchyLimitEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨LocatedUniformCauchyLimitTasteGate_decode_encode,
      ⟨locatedUniformCauchyLimitBHistCarrier⟩,
      ⟨locatedUniformCauchyLimitChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.LocatedUniformCauchyLimitUp
