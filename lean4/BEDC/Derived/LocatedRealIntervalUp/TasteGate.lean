import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedRealIntervalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedRealIntervalUp : Type where
  | mk (L U rho Delta Lambda M Q H C P N : BHist) : LocatedRealIntervalUp
  deriving DecidableEq

def locatedRealIntervalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedRealIntervalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedRealIntervalEncodeBHist h

def locatedRealIntervalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedRealIntervalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedRealIntervalDecodeBHist tail)

private theorem locatedRealInterval_decode_encode :
    ∀ h : BHist,
      locatedRealIntervalDecodeBHist
          (locatedRealIntervalEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedRealIntervalFields :
    LocatedRealIntervalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedRealIntervalUp.mk L U rho Delta Lambda M Q H C P N =>
      [L, U, rho, Delta, Lambda, M, Q, H, C, P, N]

def locatedRealIntervalToEventFlow :
    LocatedRealIntervalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      List.map locatedRealIntervalEncodeBHist
        (locatedRealIntervalFields x)

private def locatedRealIntervalRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedRealIntervalRawAt index rest

def locatedRealIntervalFromEventFlow
    (flow : EventFlow) : Option LocatedRealIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedRealIntervalUp.mk
      (locatedRealIntervalDecodeBHist (locatedRealIntervalRawAt 0 flow))
      (locatedRealIntervalDecodeBHist (locatedRealIntervalRawAt 1 flow))
      (locatedRealIntervalDecodeBHist (locatedRealIntervalRawAt 2 flow))
      (locatedRealIntervalDecodeBHist (locatedRealIntervalRawAt 3 flow))
      (locatedRealIntervalDecodeBHist (locatedRealIntervalRawAt 4 flow))
      (locatedRealIntervalDecodeBHist (locatedRealIntervalRawAt 5 flow))
      (locatedRealIntervalDecodeBHist (locatedRealIntervalRawAt 6 flow))
      (locatedRealIntervalDecodeBHist (locatedRealIntervalRawAt 7 flow))
      (locatedRealIntervalDecodeBHist (locatedRealIntervalRawAt 8 flow))
      (locatedRealIntervalDecodeBHist (locatedRealIntervalRawAt 9 flow))
      (locatedRealIntervalDecodeBHist (locatedRealIntervalRawAt 10 flow)))

private theorem locatedRealInterval_round_trip :
    ∀ x : LocatedRealIntervalUp,
      locatedRealIntervalFromEventFlow
          (locatedRealIntervalToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L U rho Delta Lambda M Q H C P N =>
      change
        some
          (LocatedRealIntervalUp.mk
            (locatedRealIntervalDecodeBHist
              (locatedRealIntervalEncodeBHist L))
            (locatedRealIntervalDecodeBHist
              (locatedRealIntervalEncodeBHist U))
            (locatedRealIntervalDecodeBHist
              (locatedRealIntervalEncodeBHist rho))
            (locatedRealIntervalDecodeBHist
              (locatedRealIntervalEncodeBHist Delta))
            (locatedRealIntervalDecodeBHist
              (locatedRealIntervalEncodeBHist Lambda))
            (locatedRealIntervalDecodeBHist
              (locatedRealIntervalEncodeBHist M))
            (locatedRealIntervalDecodeBHist
              (locatedRealIntervalEncodeBHist Q))
            (locatedRealIntervalDecodeBHist
              (locatedRealIntervalEncodeBHist H))
            (locatedRealIntervalDecodeBHist
              (locatedRealIntervalEncodeBHist C))
            (locatedRealIntervalDecodeBHist
              (locatedRealIntervalEncodeBHist P))
            (locatedRealIntervalDecodeBHist
              (locatedRealIntervalEncodeBHist N))) =
          some (LocatedRealIntervalUp.mk L U rho Delta Lambda M Q H C P N)
      rw [locatedRealInterval_decode_encode L,
        locatedRealInterval_decode_encode U,
        locatedRealInterval_decode_encode rho,
        locatedRealInterval_decode_encode Delta,
        locatedRealInterval_decode_encode Lambda,
        locatedRealInterval_decode_encode M,
        locatedRealInterval_decode_encode Q,
        locatedRealInterval_decode_encode H,
        locatedRealInterval_decode_encode C,
        locatedRealInterval_decode_encode P,
        locatedRealInterval_decode_encode N]

private theorem locatedRealIntervalToEventFlow_injective
    {x y : LocatedRealIntervalUp} :
    locatedRealIntervalToEventFlow x =
        locatedRealIntervalToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedRealIntervalFromEventFlow
          (locatedRealIntervalToEventFlow x) =
        locatedRealIntervalFromEventFlow
          (locatedRealIntervalToEventFlow y) :=
    congrArg locatedRealIntervalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (locatedRealInterval_round_trip x).symm
      (Eq.trans hread (locatedRealInterval_round_trip y)))

instance locatedRealIntervalBHistCarrier :
    BHistCarrier LocatedRealIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedRealIntervalToEventFlow
  fromEventFlow := locatedRealIntervalFromEventFlow

instance locatedRealIntervalChapterTasteGate :
    ChapterTasteGate LocatedRealIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      locatedRealIntervalFromEventFlow
          (locatedRealIntervalToEventFlow x) =
        some x
    exact locatedRealInterval_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedRealIntervalToEventFlow_injective heq)

def taste_gate : ChapterTasteGate LocatedRealIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedRealIntervalChapterTasteGate

theorem LocatedRealIntervalTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      locatedRealIntervalDecodeBHist
          (locatedRealIntervalEncodeBHist h) =
        h) ∧
      (∀ x : LocatedRealIntervalUp,
        locatedRealIntervalFromEventFlow
            (locatedRealIntervalToEventFlow x) =
          some x) ∧
        (∀ x y : LocatedRealIntervalUp,
          locatedRealIntervalToEventFlow x =
              locatedRealIntervalToEventFlow y →
            x = y) ∧
          locatedRealIntervalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨locatedRealInterval_decode_encode,
      locatedRealInterval_round_trip,
      by
        intro x y heq
        exact locatedRealIntervalToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.LocatedRealIntervalUp
