import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyProductCompletionFusionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyProductCompletionFusionUp : Type where
  | mk (Q J S D R E H C P N : BHist) : CauchyProductCompletionFusionUp
  deriving DecidableEq

def cauchyProductCompletionFusionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyProductCompletionFusionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyProductCompletionFusionEncodeBHist h

def cauchyProductCompletionFusionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyProductCompletionFusionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyProductCompletionFusionDecodeBHist tail)

private theorem CauchyProductCompletionFusionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyProductCompletionFusionDecodeBHist
        (cauchyProductCompletionFusionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyProductCompletionFusionFields :
    CauchyProductCompletionFusionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyProductCompletionFusionUp.mk Q J S D R E H C P N => [Q, J, S, D, R, E, H, C, P, N]

def cauchyProductCompletionFusionToEventFlow :
    CauchyProductCompletionFusionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (cauchyProductCompletionFusionFields x).map cauchyProductCompletionFusionEncodeBHist

private def cauchyProductCompletionFusionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyProductCompletionFusionEventAtDefault index rest

def cauchyProductCompletionFusionFromEventFlow
    (ef : EventFlow) : Option CauchyProductCompletionFusionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyProductCompletionFusionUp.mk
      (cauchyProductCompletionFusionDecodeBHist
        (cauchyProductCompletionFusionEventAtDefault 0 ef))
      (cauchyProductCompletionFusionDecodeBHist
        (cauchyProductCompletionFusionEventAtDefault 1 ef))
      (cauchyProductCompletionFusionDecodeBHist
        (cauchyProductCompletionFusionEventAtDefault 2 ef))
      (cauchyProductCompletionFusionDecodeBHist
        (cauchyProductCompletionFusionEventAtDefault 3 ef))
      (cauchyProductCompletionFusionDecodeBHist
        (cauchyProductCompletionFusionEventAtDefault 4 ef))
      (cauchyProductCompletionFusionDecodeBHist
        (cauchyProductCompletionFusionEventAtDefault 5 ef))
      (cauchyProductCompletionFusionDecodeBHist
        (cauchyProductCompletionFusionEventAtDefault 6 ef))
      (cauchyProductCompletionFusionDecodeBHist
        (cauchyProductCompletionFusionEventAtDefault 7 ef))
      (cauchyProductCompletionFusionDecodeBHist
        (cauchyProductCompletionFusionEventAtDefault 8 ef))
      (cauchyProductCompletionFusionDecodeBHist
        (cauchyProductCompletionFusionEventAtDefault 9 ef)))

private theorem CauchyProductCompletionFusionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyProductCompletionFusionUp,
      cauchyProductCompletionFusionFromEventFlow
        (cauchyProductCompletionFusionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q J S D R E H C P N =>
      change
        some
          (CauchyProductCompletionFusionUp.mk
            (cauchyProductCompletionFusionDecodeBHist
              (cauchyProductCompletionFusionEncodeBHist Q))
            (cauchyProductCompletionFusionDecodeBHist
              (cauchyProductCompletionFusionEncodeBHist J))
            (cauchyProductCompletionFusionDecodeBHist
              (cauchyProductCompletionFusionEncodeBHist S))
            (cauchyProductCompletionFusionDecodeBHist
              (cauchyProductCompletionFusionEncodeBHist D))
            (cauchyProductCompletionFusionDecodeBHist
              (cauchyProductCompletionFusionEncodeBHist R))
            (cauchyProductCompletionFusionDecodeBHist
              (cauchyProductCompletionFusionEncodeBHist E))
            (cauchyProductCompletionFusionDecodeBHist
              (cauchyProductCompletionFusionEncodeBHist H))
            (cauchyProductCompletionFusionDecodeBHist
              (cauchyProductCompletionFusionEncodeBHist C))
            (cauchyProductCompletionFusionDecodeBHist
              (cauchyProductCompletionFusionEncodeBHist P))
            (cauchyProductCompletionFusionDecodeBHist
              (cauchyProductCompletionFusionEncodeBHist N))) =
          some (CauchyProductCompletionFusionUp.mk Q J S D R E H C P N)
      rw [CauchyProductCompletionFusionTasteGate_single_carrier_alignment_decode Q,
        CauchyProductCompletionFusionTasteGate_single_carrier_alignment_decode J,
        CauchyProductCompletionFusionTasteGate_single_carrier_alignment_decode S,
        CauchyProductCompletionFusionTasteGate_single_carrier_alignment_decode D,
        CauchyProductCompletionFusionTasteGate_single_carrier_alignment_decode R,
        CauchyProductCompletionFusionTasteGate_single_carrier_alignment_decode E,
        CauchyProductCompletionFusionTasteGate_single_carrier_alignment_decode H,
        CauchyProductCompletionFusionTasteGate_single_carrier_alignment_decode C,
        CauchyProductCompletionFusionTasteGate_single_carrier_alignment_decode P,
        CauchyProductCompletionFusionTasteGate_single_carrier_alignment_decode N]

private theorem CauchyProductCompletionFusionTasteGate_single_carrier_alignment_injective
    {x y : CauchyProductCompletionFusionUp} :
    cauchyProductCompletionFusionToEventFlow x =
      cauchyProductCompletionFusionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyProductCompletionFusionFromEventFlow
          (cauchyProductCompletionFusionToEventFlow x) =
        cauchyProductCompletionFusionFromEventFlow
          (cauchyProductCompletionFusionToEventFlow y) :=
    congrArg cauchyProductCompletionFusionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyProductCompletionFusionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyProductCompletionFusionTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyProductCompletionFusionBHistCarrier :
    BHistCarrier CauchyProductCompletionFusionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyProductCompletionFusionToEventFlow
  fromEventFlow := cauchyProductCompletionFusionFromEventFlow

instance cauchyProductCompletionFusionChapterTasteGate :
    ChapterTasteGate CauchyProductCompletionFusionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyProductCompletionFusionFromEventFlow
          (cauchyProductCompletionFusionToEventFlow x) = some x
    exact CauchyProductCompletionFusionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyProductCompletionFusionTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate CauchyProductCompletionFusionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyProductCompletionFusionChapterTasteGate

theorem CauchyProductCompletionFusionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyProductCompletionFusionDecodeBHist
        (cauchyProductCompletionFusionEncodeBHist h) = h) ∧
      (∀ x : CauchyProductCompletionFusionUp,
        cauchyProductCompletionFusionFromEventFlow
          (cauchyProductCompletionFusionToEventFlow x) = some x) ∧
        (∀ x y : CauchyProductCompletionFusionUp,
          cauchyProductCompletionFusionToEventFlow x =
            cauchyProductCompletionFusionToEventFlow y → x = y) ∧
          cauchyProductCompletionFusionEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CauchyProductCompletionFusionTasteGate_single_carrier_alignment_decode,
      CauchyProductCompletionFusionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CauchyProductCompletionFusionTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.CauchyProductCompletionFusionUp
