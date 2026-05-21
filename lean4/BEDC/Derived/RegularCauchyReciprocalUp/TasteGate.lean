import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyReciprocalUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyReciprocalUp : Type where
  | mk (Q A M W D B T E H C P N : BHist) : RegularCauchyReciprocalUp
  deriving DecidableEq

def regularCauchyReciprocalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyReciprocalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyReciprocalEncodeBHist h

def regularCauchyReciprocalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyReciprocalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyReciprocalDecodeBHist tail)

private theorem regularCauchyReciprocal_decode_encode :
    ∀ h : BHist,
      regularCauchyReciprocalDecodeBHist
          (regularCauchyReciprocalEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyReciprocalFields :
    RegularCauchyReciprocalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyReciprocalUp.mk Q A M W D B T E H C P N =>
      [Q, A, M, W, D, B, T, E, H, C, P, N]

def regularCauchyReciprocalToEventFlow :
    RegularCauchyReciprocalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      List.map regularCauchyReciprocalEncodeBHist
        (regularCauchyReciprocalFields x)

private def regularCauchyReciprocalRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyReciprocalRawAt index rest

def regularCauchyReciprocalFromEventFlow
    (flow : EventFlow) : Option RegularCauchyReciprocalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyReciprocalUp.mk
      (regularCauchyReciprocalDecodeBHist (regularCauchyReciprocalRawAt 0 flow))
      (regularCauchyReciprocalDecodeBHist (regularCauchyReciprocalRawAt 1 flow))
      (regularCauchyReciprocalDecodeBHist (regularCauchyReciprocalRawAt 2 flow))
      (regularCauchyReciprocalDecodeBHist (regularCauchyReciprocalRawAt 3 flow))
      (regularCauchyReciprocalDecodeBHist (regularCauchyReciprocalRawAt 4 flow))
      (regularCauchyReciprocalDecodeBHist (regularCauchyReciprocalRawAt 5 flow))
      (regularCauchyReciprocalDecodeBHist (regularCauchyReciprocalRawAt 6 flow))
      (regularCauchyReciprocalDecodeBHist (regularCauchyReciprocalRawAt 7 flow))
      (regularCauchyReciprocalDecodeBHist (regularCauchyReciprocalRawAt 8 flow))
      (regularCauchyReciprocalDecodeBHist (regularCauchyReciprocalRawAt 9 flow))
      (regularCauchyReciprocalDecodeBHist (regularCauchyReciprocalRawAt 10 flow))
      (regularCauchyReciprocalDecodeBHist (regularCauchyReciprocalRawAt 11 flow)))

private theorem regularCauchyReciprocal_round_trip :
    ∀ x : RegularCauchyReciprocalUp,
      regularCauchyReciprocalFromEventFlow
          (regularCauchyReciprocalToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q A M W D B T E H C P N =>
      change
        some
          (RegularCauchyReciprocalUp.mk
            (regularCauchyReciprocalDecodeBHist
              (regularCauchyReciprocalEncodeBHist Q))
            (regularCauchyReciprocalDecodeBHist
              (regularCauchyReciprocalEncodeBHist A))
            (regularCauchyReciprocalDecodeBHist
              (regularCauchyReciprocalEncodeBHist M))
            (regularCauchyReciprocalDecodeBHist
              (regularCauchyReciprocalEncodeBHist W))
            (regularCauchyReciprocalDecodeBHist
              (regularCauchyReciprocalEncodeBHist D))
            (regularCauchyReciprocalDecodeBHist
              (regularCauchyReciprocalEncodeBHist B))
            (regularCauchyReciprocalDecodeBHist
              (regularCauchyReciprocalEncodeBHist T))
            (regularCauchyReciprocalDecodeBHist
              (regularCauchyReciprocalEncodeBHist E))
            (regularCauchyReciprocalDecodeBHist
              (regularCauchyReciprocalEncodeBHist H))
            (regularCauchyReciprocalDecodeBHist
              (regularCauchyReciprocalEncodeBHist C))
            (regularCauchyReciprocalDecodeBHist
              (regularCauchyReciprocalEncodeBHist P))
            (regularCauchyReciprocalDecodeBHist
              (regularCauchyReciprocalEncodeBHist N))) =
          some (RegularCauchyReciprocalUp.mk Q A M W D B T E H C P N)
      rw [regularCauchyReciprocal_decode_encode Q,
        regularCauchyReciprocal_decode_encode A,
        regularCauchyReciprocal_decode_encode M,
        regularCauchyReciprocal_decode_encode W,
        regularCauchyReciprocal_decode_encode D,
        regularCauchyReciprocal_decode_encode B,
        regularCauchyReciprocal_decode_encode T,
        regularCauchyReciprocal_decode_encode E,
        regularCauchyReciprocal_decode_encode H,
        regularCauchyReciprocal_decode_encode C,
        regularCauchyReciprocal_decode_encode P,
        regularCauchyReciprocal_decode_encode N]

private theorem regularCauchyReciprocalToEventFlow_injective
    {x y : RegularCauchyReciprocalUp} :
    regularCauchyReciprocalToEventFlow x =
        regularCauchyReciprocalToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyReciprocalFromEventFlow
          (regularCauchyReciprocalToEventFlow x) =
        regularCauchyReciprocalFromEventFlow
          (regularCauchyReciprocalToEventFlow y) :=
    congrArg regularCauchyReciprocalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyReciprocal_round_trip x).symm
      (Eq.trans hread (regularCauchyReciprocal_round_trip y)))

instance regularCauchyReciprocalBHistCarrier :
    BHistCarrier RegularCauchyReciprocalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyReciprocalToEventFlow
  fromEventFlow := regularCauchyReciprocalFromEventFlow

instance regularCauchyReciprocalChapterTasteGate :
    ChapterTasteGate RegularCauchyReciprocalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyReciprocalFromEventFlow
          (regularCauchyReciprocalToEventFlow x) =
        some x
    exact regularCauchyReciprocal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyReciprocalToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyReciprocalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyReciprocalChapterTasteGate

theorem RegularCauchyReciprocalTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyReciprocalDecodeBHist
          (regularCauchyReciprocalEncodeBHist h) =
        h) ∧
      (∀ x : RegularCauchyReciprocalUp,
        regularCauchyReciprocalFromEventFlow
            (regularCauchyReciprocalToEventFlow x) =
          some x) ∧
        (∀ x y : RegularCauchyReciprocalUp,
          regularCauchyReciprocalToEventFlow x =
              regularCauchyReciprocalToEventFlow y →
            x = y) ∧
          regularCauchyReciprocalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨regularCauchyReciprocal_decode_encode,
      regularCauchyReciprocal_round_trip,
      by
        intro x y heq
        exact regularCauchyReciprocalToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.RegularCauchyReciprocalUp.TasteGate
