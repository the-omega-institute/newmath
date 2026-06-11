import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyLocatedLimitUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyLocatedLimitUp : Type where
  | mk (W D Q I A R H C P N : BHist) : RegularCauchyLocatedLimitUp
  deriving DecidableEq

def regularCauchyLocatedLimitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyLocatedLimitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyLocatedLimitEncodeBHist h

def regularCauchyLocatedLimitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyLocatedLimitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyLocatedLimitDecodeBHist tail)

private theorem regularCauchyLocatedLimit_decode_encode :
    ∀ h : BHist,
      regularCauchyLocatedLimitDecodeBHist (regularCauchyLocatedLimitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyLocatedLimitToEventFlow :
    RegularCauchyLocatedLimitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyLocatedLimitUp.mk W D Q I A R H C P N =>
      [regularCauchyLocatedLimitEncodeBHist W,
        regularCauchyLocatedLimitEncodeBHist D,
        regularCauchyLocatedLimitEncodeBHist Q,
        regularCauchyLocatedLimitEncodeBHist I,
        regularCauchyLocatedLimitEncodeBHist A,
        regularCauchyLocatedLimitEncodeBHist R,
        regularCauchyLocatedLimitEncodeBHist H,
        regularCauchyLocatedLimitEncodeBHist C,
        regularCauchyLocatedLimitEncodeBHist P,
        regularCauchyLocatedLimitEncodeBHist N]

private def regularCauchyLocatedLimitEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyLocatedLimitEventAt index rest

def regularCauchyLocatedLimitFromEventFlow :
    EventFlow → Option RegularCauchyLocatedLimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (RegularCauchyLocatedLimitUp.mk
        (regularCauchyLocatedLimitDecodeBHist
          (regularCauchyLocatedLimitEventAt 0 ef))
        (regularCauchyLocatedLimitDecodeBHist
          (regularCauchyLocatedLimitEventAt 1 ef))
        (regularCauchyLocatedLimitDecodeBHist
          (regularCauchyLocatedLimitEventAt 2 ef))
        (regularCauchyLocatedLimitDecodeBHist
          (regularCauchyLocatedLimitEventAt 3 ef))
        (regularCauchyLocatedLimitDecodeBHist
          (regularCauchyLocatedLimitEventAt 4 ef))
        (regularCauchyLocatedLimitDecodeBHist
          (regularCauchyLocatedLimitEventAt 5 ef))
        (regularCauchyLocatedLimitDecodeBHist
          (regularCauchyLocatedLimitEventAt 6 ef))
        (regularCauchyLocatedLimitDecodeBHist
          (regularCauchyLocatedLimitEventAt 7 ef))
        (regularCauchyLocatedLimitDecodeBHist
          (regularCauchyLocatedLimitEventAt 8 ef))
        (regularCauchyLocatedLimitDecodeBHist
          (regularCauchyLocatedLimitEventAt 9 ef)))

private theorem regularCauchyLocatedLimit_round_trip :
    ∀ x : RegularCauchyLocatedLimitUp,
      regularCauchyLocatedLimitFromEventFlow
          (regularCauchyLocatedLimitToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk W D Q I A R H C P N =>
      change
        some
            (RegularCauchyLocatedLimitUp.mk
              (regularCauchyLocatedLimitDecodeBHist
                (regularCauchyLocatedLimitEncodeBHist W))
              (regularCauchyLocatedLimitDecodeBHist
                (regularCauchyLocatedLimitEncodeBHist D))
              (regularCauchyLocatedLimitDecodeBHist
                (regularCauchyLocatedLimitEncodeBHist Q))
              (regularCauchyLocatedLimitDecodeBHist
                (regularCauchyLocatedLimitEncodeBHist I))
              (regularCauchyLocatedLimitDecodeBHist
                (regularCauchyLocatedLimitEncodeBHist A))
              (regularCauchyLocatedLimitDecodeBHist
                (regularCauchyLocatedLimitEncodeBHist R))
              (regularCauchyLocatedLimitDecodeBHist
                (regularCauchyLocatedLimitEncodeBHist H))
              (regularCauchyLocatedLimitDecodeBHist
                (regularCauchyLocatedLimitEncodeBHist C))
              (regularCauchyLocatedLimitDecodeBHist
                (regularCauchyLocatedLimitEncodeBHist P))
              (regularCauchyLocatedLimitDecodeBHist
                (regularCauchyLocatedLimitEncodeBHist N))) =
          some (RegularCauchyLocatedLimitUp.mk W D Q I A R H C P N)
      rw [regularCauchyLocatedLimit_decode_encode W,
        regularCauchyLocatedLimit_decode_encode D,
        regularCauchyLocatedLimit_decode_encode Q,
        regularCauchyLocatedLimit_decode_encode I,
        regularCauchyLocatedLimit_decode_encode A,
        regularCauchyLocatedLimit_decode_encode R,
        regularCauchyLocatedLimit_decode_encode H,
        regularCauchyLocatedLimit_decode_encode C,
        regularCauchyLocatedLimit_decode_encode P,
        regularCauchyLocatedLimit_decode_encode N]

private theorem regularCauchyLocatedLimitToEventFlow_injective
    {x y : RegularCauchyLocatedLimitUp} :
    regularCauchyLocatedLimitToEventFlow x =
      regularCauchyLocatedLimitToEventFlow y →
    x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyLocatedLimitFromEventFlow
          (regularCauchyLocatedLimitToEventFlow x) =
        regularCauchyLocatedLimitFromEventFlow
          (regularCauchyLocatedLimitToEventFlow y) :=
    congrArg regularCauchyLocatedLimitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyLocatedLimit_round_trip x).symm
      (Eq.trans hread (regularCauchyLocatedLimit_round_trip y)))

instance regularCauchyLocatedLimitBHistCarrier :
    BHistCarrier RegularCauchyLocatedLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyLocatedLimitToEventFlow
  fromEventFlow := regularCauchyLocatedLimitFromEventFlow

instance regularCauchyLocatedLimitChapterTasteGate :
    ChapterTasteGate RegularCauchyLocatedLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyLocatedLimitFromEventFlow
          (regularCauchyLocatedLimitToEventFlow x) =
        some x
    exact regularCauchyLocatedLimit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyLocatedLimitToEventFlow_injective heq)

theorem RegularCauchyLocatedLimitTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyLocatedLimitDecodeBHist (regularCauchyLocatedLimitEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyLocatedLimitUp,
        regularCauchyLocatedLimitFromEventFlow (regularCauchyLocatedLimitToEventFlow x) =
          some x) ∧
        (∀ x y : RegularCauchyLocatedLimitUp,
          regularCauchyLocatedLimitToEventFlow x =
            regularCauchyLocatedLimitToEventFlow y →
          x = y) ∧ regularCauchyLocatedLimitEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨regularCauchyLocatedLimit_decode_encode,
      regularCauchyLocatedLimit_round_trip,
      fun x y heq => regularCauchyLocatedLimitToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.RegularCauchyLocatedLimitUp.TasteGate
