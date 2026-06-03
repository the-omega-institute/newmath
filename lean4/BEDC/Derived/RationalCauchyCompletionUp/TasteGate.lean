import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RationalCauchyCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RationalCauchyCompletionUp : Type where
  | mk (Q D S R M E H C P N : BHist) : RationalCauchyCompletionUp
  deriving DecidableEq

def rationalCauchyCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: rationalCauchyCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: rationalCauchyCompletionEncodeBHist h

def rationalCauchyCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (rationalCauchyCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (rationalCauchyCompletionDecodeBHist tail)

private theorem RationalCauchyCompletionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      rationalCauchyCompletionDecodeBHist (rationalCauchyCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def rationalCauchyCompletionFields : RationalCauchyCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RationalCauchyCompletionUp.mk Q D S R M E H C P N => [Q, D, S, R, M, E, H, C, P, N]

def rationalCauchyCompletionToEventFlow : RationalCauchyCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (rationalCauchyCompletionFields x).map rationalCauchyCompletionEncodeBHist

private def rationalCauchyCompletionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => rationalCauchyCompletionEventAt index rest

def rationalCauchyCompletionFromEventFlow (ef : EventFlow) :
    Option RationalCauchyCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RationalCauchyCompletionUp.mk
      (rationalCauchyCompletionDecodeBHist (rationalCauchyCompletionEventAt 0 ef))
      (rationalCauchyCompletionDecodeBHist (rationalCauchyCompletionEventAt 1 ef))
      (rationalCauchyCompletionDecodeBHist (rationalCauchyCompletionEventAt 2 ef))
      (rationalCauchyCompletionDecodeBHist (rationalCauchyCompletionEventAt 3 ef))
      (rationalCauchyCompletionDecodeBHist (rationalCauchyCompletionEventAt 4 ef))
      (rationalCauchyCompletionDecodeBHist (rationalCauchyCompletionEventAt 5 ef))
      (rationalCauchyCompletionDecodeBHist (rationalCauchyCompletionEventAt 6 ef))
      (rationalCauchyCompletionDecodeBHist (rationalCauchyCompletionEventAt 7 ef))
      (rationalCauchyCompletionDecodeBHist (rationalCauchyCompletionEventAt 8 ef))
      (rationalCauchyCompletionDecodeBHist (rationalCauchyCompletionEventAt 9 ef)))

private theorem RationalCauchyCompletionTasteGate_single_carrier_alignment_round_trip
    (x : RationalCauchyCompletionUp) :
    rationalCauchyCompletionFromEventFlow (rationalCauchyCompletionToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk Q D S R M E H C P N =>
      change
        some
          (RationalCauchyCompletionUp.mk
            (rationalCauchyCompletionDecodeBHist (rationalCauchyCompletionEncodeBHist Q))
            (rationalCauchyCompletionDecodeBHist (rationalCauchyCompletionEncodeBHist D))
            (rationalCauchyCompletionDecodeBHist (rationalCauchyCompletionEncodeBHist S))
            (rationalCauchyCompletionDecodeBHist (rationalCauchyCompletionEncodeBHist R))
            (rationalCauchyCompletionDecodeBHist (rationalCauchyCompletionEncodeBHist M))
            (rationalCauchyCompletionDecodeBHist (rationalCauchyCompletionEncodeBHist E))
            (rationalCauchyCompletionDecodeBHist (rationalCauchyCompletionEncodeBHist H))
            (rationalCauchyCompletionDecodeBHist (rationalCauchyCompletionEncodeBHist C))
            (rationalCauchyCompletionDecodeBHist (rationalCauchyCompletionEncodeBHist P))
            (rationalCauchyCompletionDecodeBHist (rationalCauchyCompletionEncodeBHist N))) =
          some (RationalCauchyCompletionUp.mk Q D S R M E H C P N)
      rw [RationalCauchyCompletionTasteGate_single_carrier_alignment_decode_encode Q,
        RationalCauchyCompletionTasteGate_single_carrier_alignment_decode_encode D,
        RationalCauchyCompletionTasteGate_single_carrier_alignment_decode_encode S,
        RationalCauchyCompletionTasteGate_single_carrier_alignment_decode_encode R,
        RationalCauchyCompletionTasteGate_single_carrier_alignment_decode_encode M,
        RationalCauchyCompletionTasteGate_single_carrier_alignment_decode_encode E,
        RationalCauchyCompletionTasteGate_single_carrier_alignment_decode_encode H,
        RationalCauchyCompletionTasteGate_single_carrier_alignment_decode_encode C,
        RationalCauchyCompletionTasteGate_single_carrier_alignment_decode_encode P,
        RationalCauchyCompletionTasteGate_single_carrier_alignment_decode_encode N]

private theorem RationalCauchyCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RationalCauchyCompletionUp} :
    rationalCauchyCompletionToEventFlow x = rationalCauchyCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      rationalCauchyCompletionFromEventFlow (rationalCauchyCompletionToEventFlow x) =
        rationalCauchyCompletionFromEventFlow (rationalCauchyCompletionToEventFlow y) :=
    congrArg rationalCauchyCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RationalCauchyCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RationalCauchyCompletionTasteGate_single_carrier_alignment_round_trip y)))

instance rationalCauchyCompletionBHistCarrier : BHistCarrier RationalCauchyCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := rationalCauchyCompletionToEventFlow
  fromEventFlow := rationalCauchyCompletionFromEventFlow

instance rationalCauchyCompletionChapterTasteGate :
    ChapterTasteGate RationalCauchyCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      rationalCauchyCompletionFromEventFlow (rationalCauchyCompletionToEventFlow x) =
        some x
    exact RationalCauchyCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RationalCauchyCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem RationalCauchyCompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      rationalCauchyCompletionDecodeBHist (rationalCauchyCompletionEncodeBHist h) = h) ∧
      (∀ x : RationalCauchyCompletionUp,
        rationalCauchyCompletionFromEventFlow (rationalCauchyCompletionToEventFlow x) =
          some x) ∧
      (∀ x y : RationalCauchyCompletionUp,
        rationalCauchyCompletionToEventFlow x = rationalCauchyCompletionToEventFlow y →
          x = y) ∧
      rationalCauchyCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RationalCauchyCompletionTasteGate_single_carrier_alignment_decode_encode,
      RationalCauchyCompletionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RationalCauchyCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RationalCauchyCompletionUp
