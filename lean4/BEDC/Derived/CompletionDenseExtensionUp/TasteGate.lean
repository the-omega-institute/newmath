import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompletionDenseExtensionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompletionDenseExtensionUp : Type where
  | mk (S D Q M F U W R A H C P N : BHist) : CompletionDenseExtensionUp
  deriving DecidableEq

def completionDenseExtensionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: completionDenseExtensionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: completionDenseExtensionEncodeBHist h

def completionDenseExtensionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (completionDenseExtensionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (completionDenseExtensionDecodeBHist tail)

private theorem CompletionDenseExtensionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      completionDenseExtensionDecodeBHist (completionDenseExtensionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def completionDenseExtensionFields : CompletionDenseExtensionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompletionDenseExtensionUp.mk S D Q M F U W R A H C P N =>
      [S, D, Q, M, F, U, W, R, A, H, C, P, N]

def completionDenseExtensionToEventFlow : CompletionDenseExtensionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (completionDenseExtensionFields x).map completionDenseExtensionEncodeBHist

private def completionDenseExtensionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => completionDenseExtensionEventAt index rest

def completionDenseExtensionFromEventFlow (ef : EventFlow) :
    Option CompletionDenseExtensionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompletionDenseExtensionUp.mk
      (completionDenseExtensionDecodeBHist (completionDenseExtensionEventAt 0 ef))
      (completionDenseExtensionDecodeBHist (completionDenseExtensionEventAt 1 ef))
      (completionDenseExtensionDecodeBHist (completionDenseExtensionEventAt 2 ef))
      (completionDenseExtensionDecodeBHist (completionDenseExtensionEventAt 3 ef))
      (completionDenseExtensionDecodeBHist (completionDenseExtensionEventAt 4 ef))
      (completionDenseExtensionDecodeBHist (completionDenseExtensionEventAt 5 ef))
      (completionDenseExtensionDecodeBHist (completionDenseExtensionEventAt 6 ef))
      (completionDenseExtensionDecodeBHist (completionDenseExtensionEventAt 7 ef))
      (completionDenseExtensionDecodeBHist (completionDenseExtensionEventAt 8 ef))
      (completionDenseExtensionDecodeBHist (completionDenseExtensionEventAt 9 ef))
      (completionDenseExtensionDecodeBHist (completionDenseExtensionEventAt 10 ef))
      (completionDenseExtensionDecodeBHist (completionDenseExtensionEventAt 11 ef))
      (completionDenseExtensionDecodeBHist (completionDenseExtensionEventAt 12 ef)))

private theorem CompletionDenseExtensionTasteGate_single_carrier_alignment_round_trip
    (x : CompletionDenseExtensionUp) :
    completionDenseExtensionFromEventFlow (completionDenseExtensionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S D Q M F U W R A H C P N =>
      change
        some
          (CompletionDenseExtensionUp.mk
            (completionDenseExtensionDecodeBHist (completionDenseExtensionEncodeBHist S))
            (completionDenseExtensionDecodeBHist (completionDenseExtensionEncodeBHist D))
            (completionDenseExtensionDecodeBHist (completionDenseExtensionEncodeBHist Q))
            (completionDenseExtensionDecodeBHist (completionDenseExtensionEncodeBHist M))
            (completionDenseExtensionDecodeBHist (completionDenseExtensionEncodeBHist F))
            (completionDenseExtensionDecodeBHist (completionDenseExtensionEncodeBHist U))
            (completionDenseExtensionDecodeBHist (completionDenseExtensionEncodeBHist W))
            (completionDenseExtensionDecodeBHist (completionDenseExtensionEncodeBHist R))
            (completionDenseExtensionDecodeBHist (completionDenseExtensionEncodeBHist A))
            (completionDenseExtensionDecodeBHist (completionDenseExtensionEncodeBHist H))
            (completionDenseExtensionDecodeBHist (completionDenseExtensionEncodeBHist C))
            (completionDenseExtensionDecodeBHist (completionDenseExtensionEncodeBHist P))
            (completionDenseExtensionDecodeBHist (completionDenseExtensionEncodeBHist N))) =
          some (CompletionDenseExtensionUp.mk S D Q M F U W R A H C P N)
      rw [CompletionDenseExtensionTasteGate_single_carrier_alignment_decode_encode S,
        CompletionDenseExtensionTasteGate_single_carrier_alignment_decode_encode D,
        CompletionDenseExtensionTasteGate_single_carrier_alignment_decode_encode Q,
        CompletionDenseExtensionTasteGate_single_carrier_alignment_decode_encode M,
        CompletionDenseExtensionTasteGate_single_carrier_alignment_decode_encode F,
        CompletionDenseExtensionTasteGate_single_carrier_alignment_decode_encode U,
        CompletionDenseExtensionTasteGate_single_carrier_alignment_decode_encode W,
        CompletionDenseExtensionTasteGate_single_carrier_alignment_decode_encode R,
        CompletionDenseExtensionTasteGate_single_carrier_alignment_decode_encode A,
        CompletionDenseExtensionTasteGate_single_carrier_alignment_decode_encode H,
        CompletionDenseExtensionTasteGate_single_carrier_alignment_decode_encode C,
        CompletionDenseExtensionTasteGate_single_carrier_alignment_decode_encode P,
        CompletionDenseExtensionTasteGate_single_carrier_alignment_decode_encode N]

private theorem CompletionDenseExtensionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompletionDenseExtensionUp} :
    completionDenseExtensionToEventFlow x = completionDenseExtensionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      completionDenseExtensionFromEventFlow (completionDenseExtensionToEventFlow x) =
        completionDenseExtensionFromEventFlow (completionDenseExtensionToEventFlow y) :=
    congrArg completionDenseExtensionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CompletionDenseExtensionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CompletionDenseExtensionTasteGate_single_carrier_alignment_round_trip y)))

instance completionDenseExtensionBHistCarrier : BHistCarrier CompletionDenseExtensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := completionDenseExtensionToEventFlow
  fromEventFlow := completionDenseExtensionFromEventFlow

instance completionDenseExtensionChapterTasteGate :
    ChapterTasteGate CompletionDenseExtensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change completionDenseExtensionFromEventFlow (completionDenseExtensionToEventFlow x) = some x
    exact CompletionDenseExtensionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CompletionDenseExtensionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CompletionDenseExtensionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        completionDenseExtensionDecodeBHist (completionDenseExtensionEncodeBHist h) = h) ∧
      (∀ x : CompletionDenseExtensionUp,
        completionDenseExtensionFromEventFlow (completionDenseExtensionToEventFlow x) = some x) ∧
        (∀ x y : CompletionDenseExtensionUp,
          completionDenseExtensionToEventFlow x = completionDenseExtensionToEventFlow y → x = y) ∧
          completionDenseExtensionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CompletionDenseExtensionTasteGate_single_carrier_alignment_decode_encode,
      CompletionDenseExtensionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CompletionDenseExtensionTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CompletionDenseExtensionUp
