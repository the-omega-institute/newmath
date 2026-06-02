import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopRealCompletionUp
namespace TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopRealCompletionUp : Type where
  | mk (D S Q L E H C P N : BHist) : BishopRealCompletionUp
  deriving DecidableEq

def bishopRealCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopRealCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopRealCompletionEncodeBHist h

def bishopRealCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopRealCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopRealCompletionDecodeBHist tail)

private theorem BishopRealCompletionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      bishopRealCompletionDecodeBHist (bishopRealCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopRealCompletionFields : BishopRealCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopRealCompletionUp.mk D S Q L E H C P N => [D, S, Q, L, E, H, C, P, N]

def bishopRealCompletionToEventFlow : BishopRealCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bishopRealCompletionFields x).map bishopRealCompletionEncodeBHist

private def bishopRealCompletionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopRealCompletionEventAt index rest

def bishopRealCompletionFromEventFlow (ef : EventFlow) :
    Option BishopRealCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopRealCompletionUp.mk
      (bishopRealCompletionDecodeBHist (bishopRealCompletionEventAt 0 ef))
      (bishopRealCompletionDecodeBHist (bishopRealCompletionEventAt 1 ef))
      (bishopRealCompletionDecodeBHist (bishopRealCompletionEventAt 2 ef))
      (bishopRealCompletionDecodeBHist (bishopRealCompletionEventAt 3 ef))
      (bishopRealCompletionDecodeBHist (bishopRealCompletionEventAt 4 ef))
      (bishopRealCompletionDecodeBHist (bishopRealCompletionEventAt 5 ef))
      (bishopRealCompletionDecodeBHist (bishopRealCompletionEventAt 6 ef))
      (bishopRealCompletionDecodeBHist (bishopRealCompletionEventAt 7 ef))
      (bishopRealCompletionDecodeBHist (bishopRealCompletionEventAt 8 ef)))

private theorem BishopRealCompletionTasteGate_single_carrier_alignment_round_trip
    (x : BishopRealCompletionUp) :
    bishopRealCompletionFromEventFlow (bishopRealCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk D S Q L E H C P N =>
      change
        some
          (BishopRealCompletionUp.mk
            (bishopRealCompletionDecodeBHist (bishopRealCompletionEncodeBHist D))
            (bishopRealCompletionDecodeBHist (bishopRealCompletionEncodeBHist S))
            (bishopRealCompletionDecodeBHist (bishopRealCompletionEncodeBHist Q))
            (bishopRealCompletionDecodeBHist (bishopRealCompletionEncodeBHist L))
            (bishopRealCompletionDecodeBHist (bishopRealCompletionEncodeBHist E))
            (bishopRealCompletionDecodeBHist (bishopRealCompletionEncodeBHist H))
            (bishopRealCompletionDecodeBHist (bishopRealCompletionEncodeBHist C))
            (bishopRealCompletionDecodeBHist (bishopRealCompletionEncodeBHist P))
            (bishopRealCompletionDecodeBHist (bishopRealCompletionEncodeBHist N))) =
          some (BishopRealCompletionUp.mk D S Q L E H C P N)
      rw [BishopRealCompletionTasteGate_single_carrier_alignment_decode_encode D,
        BishopRealCompletionTasteGate_single_carrier_alignment_decode_encode S,
        BishopRealCompletionTasteGate_single_carrier_alignment_decode_encode Q,
        BishopRealCompletionTasteGate_single_carrier_alignment_decode_encode L,
        BishopRealCompletionTasteGate_single_carrier_alignment_decode_encode E,
        BishopRealCompletionTasteGate_single_carrier_alignment_decode_encode H,
        BishopRealCompletionTasteGate_single_carrier_alignment_decode_encode C,
        BishopRealCompletionTasteGate_single_carrier_alignment_decode_encode P,
        BishopRealCompletionTasteGate_single_carrier_alignment_decode_encode N]

private theorem BishopRealCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopRealCompletionUp} :
    bishopRealCompletionToEventFlow x = bishopRealCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopRealCompletionFromEventFlow (bishopRealCompletionToEventFlow x) =
        bishopRealCompletionFromEventFlow (bishopRealCompletionToEventFlow y) :=
    congrArg bishopRealCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BishopRealCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopRealCompletionTasteGate_single_carrier_alignment_round_trip y)))

instance bishopRealCompletionBHistCarrier : BHistCarrier BishopRealCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopRealCompletionToEventFlow
  fromEventFlow := bishopRealCompletionFromEventFlow

instance bishopRealCompletionChapterTasteGate :
    ChapterTasteGate BishopRealCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopRealCompletionFromEventFlow
      (bishopRealCompletionToEventFlow x) = some x
    exact BishopRealCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BishopRealCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem BishopRealCompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist, bishopRealCompletionDecodeBHist (bishopRealCompletionEncodeBHist h) = h) ∧
      (∀ x : BishopRealCompletionUp,
        bishopRealCompletionFromEventFlow (bishopRealCompletionToEventFlow x) = some x) ∧
        (∀ x y : BishopRealCompletionUp,
          bishopRealCompletionToEventFlow x = bishopRealCompletionToEventFlow y → x = y) ∧
          bishopRealCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨BishopRealCompletionTasteGate_single_carrier_alignment_decode_encode,
      BishopRealCompletionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        BishopRealCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end TasteGate
end BEDC.Derived.BishopRealCompletionUp
