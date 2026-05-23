import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularLocatedCauchyRealUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularLocatedCauchyRealUp : Type where
  | mk (S Q D M L E H C P N : BHist) : RegularLocatedCauchyRealUp
  deriving DecidableEq

def regularLocatedCauchyRealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularLocatedCauchyRealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularLocatedCauchyRealEncodeBHist h

def regularLocatedCauchyRealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularLocatedCauchyRealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularLocatedCauchyRealDecodeBHist tail)

private theorem regularLocatedCauchyReal_decode_encode :
    ∀ h : BHist,
      regularLocatedCauchyRealDecodeBHist
          (regularLocatedCauchyRealEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularLocatedCauchyRealFields :
    RegularLocatedCauchyRealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularLocatedCauchyRealUp.mk S Q D M L E H C P N => [S, Q, D, M, L, E, H, C, P, N]

def regularLocatedCauchyRealToEventFlow :
    RegularLocatedCauchyRealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      List.map regularLocatedCauchyRealEncodeBHist
        (regularLocatedCauchyRealFields x)

private def regularLocatedCauchyRealRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularLocatedCauchyRealRawAt index rest

def regularLocatedCauchyRealFromEventFlow
    (flow : EventFlow) : Option RegularLocatedCauchyRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularLocatedCauchyRealUp.mk
      (regularLocatedCauchyRealDecodeBHist (regularLocatedCauchyRealRawAt 0 flow))
      (regularLocatedCauchyRealDecodeBHist (regularLocatedCauchyRealRawAt 1 flow))
      (regularLocatedCauchyRealDecodeBHist (regularLocatedCauchyRealRawAt 2 flow))
      (regularLocatedCauchyRealDecodeBHist (regularLocatedCauchyRealRawAt 3 flow))
      (regularLocatedCauchyRealDecodeBHist (regularLocatedCauchyRealRawAt 4 flow))
      (regularLocatedCauchyRealDecodeBHist (regularLocatedCauchyRealRawAt 5 flow))
      (regularLocatedCauchyRealDecodeBHist (regularLocatedCauchyRealRawAt 6 flow))
      (regularLocatedCauchyRealDecodeBHist (regularLocatedCauchyRealRawAt 7 flow))
      (regularLocatedCauchyRealDecodeBHist (regularLocatedCauchyRealRawAt 8 flow))
      (regularLocatedCauchyRealDecodeBHist (regularLocatedCauchyRealRawAt 9 flow)))

private theorem regularLocatedCauchyReal_round_trip :
    ∀ x : RegularLocatedCauchyRealUp,
      regularLocatedCauchyRealFromEventFlow
          (regularLocatedCauchyRealToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S Q D M L E H C P N =>
      change
        some
          (RegularLocatedCauchyRealUp.mk
            (regularLocatedCauchyRealDecodeBHist
              (regularLocatedCauchyRealEncodeBHist S))
            (regularLocatedCauchyRealDecodeBHist
              (regularLocatedCauchyRealEncodeBHist Q))
            (regularLocatedCauchyRealDecodeBHist
              (regularLocatedCauchyRealEncodeBHist D))
            (regularLocatedCauchyRealDecodeBHist
              (regularLocatedCauchyRealEncodeBHist M))
            (regularLocatedCauchyRealDecodeBHist
              (regularLocatedCauchyRealEncodeBHist L))
            (regularLocatedCauchyRealDecodeBHist
              (regularLocatedCauchyRealEncodeBHist E))
            (regularLocatedCauchyRealDecodeBHist
              (regularLocatedCauchyRealEncodeBHist H))
            (regularLocatedCauchyRealDecodeBHist
              (regularLocatedCauchyRealEncodeBHist C))
            (regularLocatedCauchyRealDecodeBHist
              (regularLocatedCauchyRealEncodeBHist P))
            (regularLocatedCauchyRealDecodeBHist
              (regularLocatedCauchyRealEncodeBHist N))) =
          some (RegularLocatedCauchyRealUp.mk S Q D M L E H C P N)
      rw [regularLocatedCauchyReal_decode_encode S,
        regularLocatedCauchyReal_decode_encode Q,
        regularLocatedCauchyReal_decode_encode D,
        regularLocatedCauchyReal_decode_encode M,
        regularLocatedCauchyReal_decode_encode L,
        regularLocatedCauchyReal_decode_encode E,
        regularLocatedCauchyReal_decode_encode H,
        regularLocatedCauchyReal_decode_encode C,
        regularLocatedCauchyReal_decode_encode P,
        regularLocatedCauchyReal_decode_encode N]

private theorem regularLocatedCauchyRealToEventFlow_injective
    {x y : RegularLocatedCauchyRealUp} :
    regularLocatedCauchyRealToEventFlow x =
        regularLocatedCauchyRealToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularLocatedCauchyRealFromEventFlow
          (regularLocatedCauchyRealToEventFlow x) =
        regularLocatedCauchyRealFromEventFlow
          (regularLocatedCauchyRealToEventFlow y) :=
    congrArg regularLocatedCauchyRealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularLocatedCauchyReal_round_trip x).symm
      (Eq.trans hread (regularLocatedCauchyReal_round_trip y)))

instance regularLocatedCauchyRealBHistCarrier :
    BHistCarrier RegularLocatedCauchyRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularLocatedCauchyRealToEventFlow
  fromEventFlow := regularLocatedCauchyRealFromEventFlow

instance regularLocatedCauchyRealChapterTasteGate :
    ChapterTasteGate RegularLocatedCauchyRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularLocatedCauchyRealFromEventFlow
          (regularLocatedCauchyRealToEventFlow x) =
        some x
    exact regularLocatedCauchyReal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularLocatedCauchyRealToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularLocatedCauchyRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularLocatedCauchyRealChapterTasteGate

theorem RegularLocatedCauchyRealTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularLocatedCauchyRealDecodeBHist
          (regularLocatedCauchyRealEncodeBHist h) =
        h) ∧
      (∀ x : RegularLocatedCauchyRealUp,
        regularLocatedCauchyRealFromEventFlow
            (regularLocatedCauchyRealToEventFlow x) =
          some x) ∧
        (∀ x y : RegularLocatedCauchyRealUp,
          regularLocatedCauchyRealToEventFlow x =
              regularLocatedCauchyRealToEventFlow y →
            x = y) ∧
          regularLocatedCauchyRealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨regularLocatedCauchyReal_decode_encode,
      regularLocatedCauchyReal_round_trip,
      by
        intro x y heq
        exact regularLocatedCauchyRealToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.RegularLocatedCauchyRealUp.TasteGate
