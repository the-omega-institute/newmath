import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopRealUniformCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopRealUniformCompletionUp : Type where
  | mk (R U J T S D Q H C P N : BHist) : BishopRealUniformCompletionUp
  deriving DecidableEq

def bishopRealUniformCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopRealUniformCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopRealUniformCompletionEncodeBHist h

def bishopRealUniformCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopRealUniformCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopRealUniformCompletionDecodeBHist tail)

private theorem BishopRealUniformCompletionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      bishopRealUniformCompletionDecodeBHist (bishopRealUniformCompletionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopRealUniformCompletionFields :
    BishopRealUniformCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopRealUniformCompletionUp.mk R U J T S D Q H C P N =>
      [R, U, J, T, S, D, Q, H, C, P, N]

def bishopRealUniformCompletionToEventFlow :
    BishopRealUniformCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (bishopRealUniformCompletionFields x).map
        bishopRealUniformCompletionEncodeBHist

private def bishopRealUniformCompletionEventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      bishopRealUniformCompletionEventAt index rest

def bishopRealUniformCompletionFromEventFlow (ef : EventFlow) :
    Option BishopRealUniformCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopRealUniformCompletionUp.mk
      (bishopRealUniformCompletionDecodeBHist
        (bishopRealUniformCompletionEventAt 0 ef))
      (bishopRealUniformCompletionDecodeBHist
        (bishopRealUniformCompletionEventAt 1 ef))
      (bishopRealUniformCompletionDecodeBHist
        (bishopRealUniformCompletionEventAt 2 ef))
      (bishopRealUniformCompletionDecodeBHist
        (bishopRealUniformCompletionEventAt 3 ef))
      (bishopRealUniformCompletionDecodeBHist
        (bishopRealUniformCompletionEventAt 4 ef))
      (bishopRealUniformCompletionDecodeBHist
        (bishopRealUniformCompletionEventAt 5 ef))
      (bishopRealUniformCompletionDecodeBHist
        (bishopRealUniformCompletionEventAt 6 ef))
      (bishopRealUniformCompletionDecodeBHist
        (bishopRealUniformCompletionEventAt 7 ef))
      (bishopRealUniformCompletionDecodeBHist
        (bishopRealUniformCompletionEventAt 8 ef))
      (bishopRealUniformCompletionDecodeBHist
        (bishopRealUniformCompletionEventAt 9 ef))
      (bishopRealUniformCompletionDecodeBHist
        (bishopRealUniformCompletionEventAt 10 ef)))

private theorem BishopRealUniformCompletionTasteGate_single_carrier_alignment_round_trip
    (x : BishopRealUniformCompletionUp) :
    bishopRealUniformCompletionFromEventFlow
        (bishopRealUniformCompletionToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk R U J T S D Q H C P N =>
      change
        some
          (BishopRealUniformCompletionUp.mk
            (bishopRealUniformCompletionDecodeBHist
              (bishopRealUniformCompletionEncodeBHist R))
            (bishopRealUniformCompletionDecodeBHist
              (bishopRealUniformCompletionEncodeBHist U))
            (bishopRealUniformCompletionDecodeBHist
              (bishopRealUniformCompletionEncodeBHist J))
            (bishopRealUniformCompletionDecodeBHist
              (bishopRealUniformCompletionEncodeBHist T))
            (bishopRealUniformCompletionDecodeBHist
              (bishopRealUniformCompletionEncodeBHist S))
            (bishopRealUniformCompletionDecodeBHist
              (bishopRealUniformCompletionEncodeBHist D))
            (bishopRealUniformCompletionDecodeBHist
              (bishopRealUniformCompletionEncodeBHist Q))
            (bishopRealUniformCompletionDecodeBHist
              (bishopRealUniformCompletionEncodeBHist H))
            (bishopRealUniformCompletionDecodeBHist
              (bishopRealUniformCompletionEncodeBHist C))
            (bishopRealUniformCompletionDecodeBHist
              (bishopRealUniformCompletionEncodeBHist P))
            (bishopRealUniformCompletionDecodeBHist
              (bishopRealUniformCompletionEncodeBHist N))) =
          some (BishopRealUniformCompletionUp.mk R U J T S D Q H C P N)
      rw [BishopRealUniformCompletionTasteGate_single_carrier_alignment_decode_encode R,
        BishopRealUniformCompletionTasteGate_single_carrier_alignment_decode_encode U,
        BishopRealUniformCompletionTasteGate_single_carrier_alignment_decode_encode J,
        BishopRealUniformCompletionTasteGate_single_carrier_alignment_decode_encode T,
        BishopRealUniformCompletionTasteGate_single_carrier_alignment_decode_encode S,
        BishopRealUniformCompletionTasteGate_single_carrier_alignment_decode_encode D,
        BishopRealUniformCompletionTasteGate_single_carrier_alignment_decode_encode Q,
        BishopRealUniformCompletionTasteGate_single_carrier_alignment_decode_encode H,
        BishopRealUniformCompletionTasteGate_single_carrier_alignment_decode_encode C,
        BishopRealUniformCompletionTasteGate_single_carrier_alignment_decode_encode P,
        BishopRealUniformCompletionTasteGate_single_carrier_alignment_decode_encode N]

private theorem BishopRealUniformCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopRealUniformCompletionUp} :
    bishopRealUniformCompletionToEventFlow x =
        bishopRealUniformCompletionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopRealUniformCompletionFromEventFlow
          (bishopRealUniformCompletionToEventFlow x) =
        bishopRealUniformCompletionFromEventFlow
          (bishopRealUniformCompletionToEventFlow y) :=
    congrArg bishopRealUniformCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopRealUniformCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopRealUniformCompletionTasteGate_single_carrier_alignment_round_trip y)))

instance bishopRealUniformCompletionBHistCarrier :
    BHistCarrier BishopRealUniformCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopRealUniformCompletionToEventFlow
  fromEventFlow := bishopRealUniformCompletionFromEventFlow

instance bishopRealUniformCompletionChapterTasteGate :
    ChapterTasteGate BishopRealUniformCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopRealUniformCompletionFromEventFlow
          (bishopRealUniformCompletionToEventFlow x) =
        some x
    exact BishopRealUniformCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BishopRealUniformCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem BishopRealUniformCompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        bishopRealUniformCompletionDecodeBHist
            (bishopRealUniformCompletionEncodeBHist h) =
          h) ∧
      (∀ x : BishopRealUniformCompletionUp,
        bishopRealUniformCompletionFromEventFlow
            (bishopRealUniformCompletionToEventFlow x) =
          some x) ∧
      (∀ x y : BishopRealUniformCompletionUp,
        bishopRealUniformCompletionToEventFlow x =
            bishopRealUniformCompletionToEventFlow y →
          x = y) ∧
      bishopRealUniformCompletionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨BishopRealUniformCompletionTasteGate_single_carrier_alignment_decode_encode,
      BishopRealUniformCompletionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        BishopRealUniformCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.BishopRealUniformCompletionUp
