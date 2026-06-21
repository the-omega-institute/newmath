import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopCauchyCriterionCompletionUp : Type where
  | mk (Q M W R D E L H C P N : BHist) : BishopCauchyCriterionCompletionUp
  deriving DecidableEq

namespace BishopCauchyCriterionCompletionUp

def bishopCauchyCriterionCompletionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopCauchyCriterionCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopCauchyCriterionCompletionEncodeBHist h

def bishopCauchyCriterionCompletionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopCauchyCriterionCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopCauchyCriterionCompletionDecodeBHist tail)

private theorem BishopCauchyCriterionCompletionTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      bishopCauchyCriterionCompletionDecodeBHist
          (bishopCauchyCriterionCompletionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def bishopCauchyCriterionCompletionFields :
    BishopCauchyCriterionCompletionUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopCauchyCriterionCompletionUp.mk Q M W R D E L H C P N =>
      [Q, M, W, R, D, E, L, H, C, P, N]

def bishopCauchyCriterionCompletionToEventFlow :
    BishopCauchyCriterionCompletionUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (bishopCauchyCriterionCompletionFields x).map
        bishopCauchyCriterionCompletionEncodeBHist

private def bishopCauchyCriterionCompletionEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      bishopCauchyCriterionCompletionEventAtDefault index rest

def bishopCauchyCriterionCompletionFromEventFlow
    (flow : EventFlow) : Option BishopCauchyCriterionCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopCauchyCriterionCompletionUp.mk
      (bishopCauchyCriterionCompletionDecodeBHist
        (bishopCauchyCriterionCompletionEventAtDefault 0 flow))
      (bishopCauchyCriterionCompletionDecodeBHist
        (bishopCauchyCriterionCompletionEventAtDefault 1 flow))
      (bishopCauchyCriterionCompletionDecodeBHist
        (bishopCauchyCriterionCompletionEventAtDefault 2 flow))
      (bishopCauchyCriterionCompletionDecodeBHist
        (bishopCauchyCriterionCompletionEventAtDefault 3 flow))
      (bishopCauchyCriterionCompletionDecodeBHist
        (bishopCauchyCriterionCompletionEventAtDefault 4 flow))
      (bishopCauchyCriterionCompletionDecodeBHist
        (bishopCauchyCriterionCompletionEventAtDefault 5 flow))
      (bishopCauchyCriterionCompletionDecodeBHist
        (bishopCauchyCriterionCompletionEventAtDefault 6 flow))
      (bishopCauchyCriterionCompletionDecodeBHist
        (bishopCauchyCriterionCompletionEventAtDefault 7 flow))
      (bishopCauchyCriterionCompletionDecodeBHist
        (bishopCauchyCriterionCompletionEventAtDefault 8 flow))
      (bishopCauchyCriterionCompletionDecodeBHist
        (bishopCauchyCriterionCompletionEventAtDefault 9 flow))
      (bishopCauchyCriterionCompletionDecodeBHist
        (bishopCauchyCriterionCompletionEventAtDefault 10 flow)))

private theorem BishopCauchyCriterionCompletionTasteGate_single_carrier_alignment_round_trip
    (x : BishopCauchyCriterionCompletionUp) :
    bishopCauchyCriterionCompletionFromEventFlow
        (bishopCauchyCriterionCompletionToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk Q M W R D E L H C P N =>
      change
        some
            (BishopCauchyCriterionCompletionUp.mk
              (bishopCauchyCriterionCompletionDecodeBHist
                (bishopCauchyCriterionCompletionEncodeBHist Q))
              (bishopCauchyCriterionCompletionDecodeBHist
                (bishopCauchyCriterionCompletionEncodeBHist M))
              (bishopCauchyCriterionCompletionDecodeBHist
                (bishopCauchyCriterionCompletionEncodeBHist W))
              (bishopCauchyCriterionCompletionDecodeBHist
                (bishopCauchyCriterionCompletionEncodeBHist R))
              (bishopCauchyCriterionCompletionDecodeBHist
                (bishopCauchyCriterionCompletionEncodeBHist D))
              (bishopCauchyCriterionCompletionDecodeBHist
                (bishopCauchyCriterionCompletionEncodeBHist E))
              (bishopCauchyCriterionCompletionDecodeBHist
                (bishopCauchyCriterionCompletionEncodeBHist L))
              (bishopCauchyCriterionCompletionDecodeBHist
                (bishopCauchyCriterionCompletionEncodeBHist H))
              (bishopCauchyCriterionCompletionDecodeBHist
                (bishopCauchyCriterionCompletionEncodeBHist C))
              (bishopCauchyCriterionCompletionDecodeBHist
                (bishopCauchyCriterionCompletionEncodeBHist P))
              (bishopCauchyCriterionCompletionDecodeBHist
                (bishopCauchyCriterionCompletionEncodeBHist N))) =
          some (BishopCauchyCriterionCompletionUp.mk Q M W R D E L H C P N)
      rw [BishopCauchyCriterionCompletionTasteGate_single_carrier_alignment_decode_encode Q,
        BishopCauchyCriterionCompletionTasteGate_single_carrier_alignment_decode_encode M,
        BishopCauchyCriterionCompletionTasteGate_single_carrier_alignment_decode_encode W,
        BishopCauchyCriterionCompletionTasteGate_single_carrier_alignment_decode_encode R,
        BishopCauchyCriterionCompletionTasteGate_single_carrier_alignment_decode_encode D,
        BishopCauchyCriterionCompletionTasteGate_single_carrier_alignment_decode_encode E,
        BishopCauchyCriterionCompletionTasteGate_single_carrier_alignment_decode_encode L,
        BishopCauchyCriterionCompletionTasteGate_single_carrier_alignment_decode_encode H,
        BishopCauchyCriterionCompletionTasteGate_single_carrier_alignment_decode_encode C,
        BishopCauchyCriterionCompletionTasteGate_single_carrier_alignment_decode_encode P,
        BishopCauchyCriterionCompletionTasteGate_single_carrier_alignment_decode_encode N]

private theorem BishopCauchyCriterionCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopCauchyCriterionCompletionUp} :
    bishopCauchyCriterionCompletionToEventFlow x =
        bishopCauchyCriterionCompletionToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopCauchyCriterionCompletionFromEventFlow
          (bishopCauchyCriterionCompletionToEventFlow x) =
        bishopCauchyCriterionCompletionFromEventFlow
          (bishopCauchyCriterionCompletionToEventFlow y) :=
    congrArg bishopCauchyCriterionCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopCauchyCriterionCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopCauchyCriterionCompletionTasteGate_single_carrier_alignment_round_trip y)))

instance bishopCauchyCriterionCompletionBHistCarrier :
    BHistCarrier BishopCauchyCriterionCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopCauchyCriterionCompletionToEventFlow
  fromEventFlow := bishopCauchyCriterionCompletionFromEventFlow

instance bishopCauchyCriterionCompletionChapterTasteGate :
    ChapterTasteGate BishopCauchyCriterionCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopCauchyCriterionCompletionFromEventFlow
          (bishopCauchyCriterionCompletionToEventFlow x) =
        some x
    exact BishopCauchyCriterionCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BishopCauchyCriterionCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

theorem BishopCauchyCriterionCompletionTasteGate_single_carrier_alignment :
    (forall h : BHist,
      bishopCauchyCriterionCompletionDecodeBHist
          (bishopCauchyCriterionCompletionEncodeBHist h) =
        h) /\
      Nonempty (BHistCarrier BishopCauchyCriterionCompletionUp) /\
        Nonempty (ChapterTasteGate BishopCauchyCriterionCompletionUp) /\
          bishopCauchyCriterionCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨BishopCauchyCriterionCompletionTasteGate_single_carrier_alignment_decode_encode,
      ⟨bishopCauchyCriterionCompletionBHistCarrier⟩,
      ⟨bishopCauchyCriterionCompletionChapterTasteGate⟩,
      rfl⟩

end BishopCauchyCriterionCompletionUp
end BEDC.Derived
