import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.QuotientFreeCompletionSealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive QuotientFreeCompletionSealUp : Type where
  | mk (D S R E L H C P N : BHist) : QuotientFreeCompletionSealUp
  deriving DecidableEq

def quotientFreeCompletionSealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: quotientFreeCompletionSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: quotientFreeCompletionSealEncodeBHist h

def quotientFreeCompletionSealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (quotientFreeCompletionSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (quotientFreeCompletionSealDecodeBHist tail)

private theorem quotientFreeCompletionSeal_decode_encode_bhist :
    ∀ h : BHist,
      quotientFreeCompletionSealDecodeBHist
          (quotientFreeCompletionSealEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def quotientFreeCompletionSealFields :
    QuotientFreeCompletionSealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | QuotientFreeCompletionSealUp.mk D S R E L H C P N => [D, S, R, E, L, H, C, P, N]

def quotientFreeCompletionSealToEventFlow :
    QuotientFreeCompletionSealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (quotientFreeCompletionSealFields x).map quotientFreeCompletionSealEncodeBHist

private def quotientFreeCompletionSealEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => quotientFreeCompletionSealEventAt index rest

def quotientFreeCompletionSealFromEventFlow :
    EventFlow → Option QuotientFreeCompletionSealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (QuotientFreeCompletionSealUp.mk
        (quotientFreeCompletionSealDecodeBHist (quotientFreeCompletionSealEventAt 0 ef))
        (quotientFreeCompletionSealDecodeBHist (quotientFreeCompletionSealEventAt 1 ef))
        (quotientFreeCompletionSealDecodeBHist (quotientFreeCompletionSealEventAt 2 ef))
        (quotientFreeCompletionSealDecodeBHist (quotientFreeCompletionSealEventAt 3 ef))
        (quotientFreeCompletionSealDecodeBHist (quotientFreeCompletionSealEventAt 4 ef))
        (quotientFreeCompletionSealDecodeBHist (quotientFreeCompletionSealEventAt 5 ef))
        (quotientFreeCompletionSealDecodeBHist (quotientFreeCompletionSealEventAt 6 ef))
        (quotientFreeCompletionSealDecodeBHist (quotientFreeCompletionSealEventAt 7 ef))
        (quotientFreeCompletionSealDecodeBHist (quotientFreeCompletionSealEventAt 8 ef)))

private theorem quotientFreeCompletionSeal_round_trip :
    ∀ x : QuotientFreeCompletionSealUp,
      quotientFreeCompletionSealFromEventFlow (quotientFreeCompletionSealToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D S R E L H C P N =>
      change
        some
          (QuotientFreeCompletionSealUp.mk
            (quotientFreeCompletionSealDecodeBHist
              (quotientFreeCompletionSealEncodeBHist D))
            (quotientFreeCompletionSealDecodeBHist
              (quotientFreeCompletionSealEncodeBHist S))
            (quotientFreeCompletionSealDecodeBHist
              (quotientFreeCompletionSealEncodeBHist R))
            (quotientFreeCompletionSealDecodeBHist
              (quotientFreeCompletionSealEncodeBHist E))
            (quotientFreeCompletionSealDecodeBHist
              (quotientFreeCompletionSealEncodeBHist L))
            (quotientFreeCompletionSealDecodeBHist
              (quotientFreeCompletionSealEncodeBHist H))
            (quotientFreeCompletionSealDecodeBHist
              (quotientFreeCompletionSealEncodeBHist C))
            (quotientFreeCompletionSealDecodeBHist
              (quotientFreeCompletionSealEncodeBHist P))
            (quotientFreeCompletionSealDecodeBHist
              (quotientFreeCompletionSealEncodeBHist N))) =
          some (QuotientFreeCompletionSealUp.mk D S R E L H C P N)
      rw [quotientFreeCompletionSeal_decode_encode_bhist D,
        quotientFreeCompletionSeal_decode_encode_bhist S,
        quotientFreeCompletionSeal_decode_encode_bhist R,
        quotientFreeCompletionSeal_decode_encode_bhist E,
        quotientFreeCompletionSeal_decode_encode_bhist L,
        quotientFreeCompletionSeal_decode_encode_bhist H,
        quotientFreeCompletionSeal_decode_encode_bhist C,
        quotientFreeCompletionSeal_decode_encode_bhist P,
        quotientFreeCompletionSeal_decode_encode_bhist N]

private theorem quotientFreeCompletionSealToEventFlow_injective
    {x y : QuotientFreeCompletionSealUp} :
    quotientFreeCompletionSealToEventFlow x = quotientFreeCompletionSealToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      quotientFreeCompletionSealFromEventFlow (quotientFreeCompletionSealToEventFlow x) =
        quotientFreeCompletionSealFromEventFlow (quotientFreeCompletionSealToEventFlow y) :=
    congrArg quotientFreeCompletionSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (quotientFreeCompletionSeal_round_trip x).symm
      (Eq.trans hread (quotientFreeCompletionSeal_round_trip y)))

instance quotientFreeCompletionSealBHistCarrier :
    BHistCarrier QuotientFreeCompletionSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := quotientFreeCompletionSealToEventFlow
  fromEventFlow := quotientFreeCompletionSealFromEventFlow

instance quotientFreeCompletionSealChapterTasteGate :
    ChapterTasteGate QuotientFreeCompletionSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      quotientFreeCompletionSealFromEventFlow (quotientFreeCompletionSealToEventFlow x) =
        some x
    exact quotientFreeCompletionSeal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (quotientFreeCompletionSealToEventFlow_injective heq)

theorem QuotientFreeCompletionSealTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      quotientFreeCompletionSealDecodeBHist (quotientFreeCompletionSealEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier QuotientFreeCompletionSealUp) ∧
        Nonempty (ChapterTasteGate QuotientFreeCompletionSealUp) ∧
          quotientFreeCompletionSealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  constructor
  · exact quotientFreeCompletionSeal_decode_encode_bhist
  · constructor
    · exact Nonempty.intro quotientFreeCompletionSealBHistCarrier
    · constructor
      · exact Nonempty.intro quotientFreeCompletionSealChapterTasteGate
      · rfl

end BEDC.Derived.QuotientFreeCompletionSealUp
