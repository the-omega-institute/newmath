import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RiemannIntegrationCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RiemannIntegrationCompletionUp : Type where
  | mk (I G S Q R E H C P N : BHist) : RiemannIntegrationCompletionUp

def riemannIntegrationCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: riemannIntegrationCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: riemannIntegrationCompletionEncodeBHist h

def riemannIntegrationCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (riemannIntegrationCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (riemannIntegrationCompletionDecodeBHist tail)

private theorem RiemannIntegrationCompletionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      riemannIntegrationCompletionDecodeBHist
        (riemannIntegrationCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def riemannIntegrationCompletionToEventFlow :
    RiemannIntegrationCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RiemannIntegrationCompletionUp.mk I G S Q R E H C P N =>
      ([
        I, G, S, Q, R, E, H, C, P, N
      ] : List BHist).map riemannIntegrationCompletionEncodeBHist

private def riemannIntegrationCompletionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => riemannIntegrationCompletionEventAtDefault index rest

def riemannIntegrationCompletionFromEventFlow
    (ef : EventFlow) : Option RiemannIntegrationCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RiemannIntegrationCompletionUp.mk
      (riemannIntegrationCompletionDecodeBHist
        (riemannIntegrationCompletionEventAtDefault 0 ef))
      (riemannIntegrationCompletionDecodeBHist
        (riemannIntegrationCompletionEventAtDefault 1 ef))
      (riemannIntegrationCompletionDecodeBHist
        (riemannIntegrationCompletionEventAtDefault 2 ef))
      (riemannIntegrationCompletionDecodeBHist
        (riemannIntegrationCompletionEventAtDefault 3 ef))
      (riemannIntegrationCompletionDecodeBHist
        (riemannIntegrationCompletionEventAtDefault 4 ef))
      (riemannIntegrationCompletionDecodeBHist
        (riemannIntegrationCompletionEventAtDefault 5 ef))
      (riemannIntegrationCompletionDecodeBHist
        (riemannIntegrationCompletionEventAtDefault 6 ef))
      (riemannIntegrationCompletionDecodeBHist
        (riemannIntegrationCompletionEventAtDefault 7 ef))
      (riemannIntegrationCompletionDecodeBHist
        (riemannIntegrationCompletionEventAtDefault 8 ef))
      (riemannIntegrationCompletionDecodeBHist
        (riemannIntegrationCompletionEventAtDefault 9 ef)))

private theorem RiemannIntegrationCompletionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RiemannIntegrationCompletionUp,
      riemannIntegrationCompletionFromEventFlow
        (riemannIntegrationCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I G S Q R E H C P N =>
      change
        some
          (RiemannIntegrationCompletionUp.mk
            (riemannIntegrationCompletionDecodeBHist
              (riemannIntegrationCompletionEncodeBHist I))
            (riemannIntegrationCompletionDecodeBHist
              (riemannIntegrationCompletionEncodeBHist G))
            (riemannIntegrationCompletionDecodeBHist
              (riemannIntegrationCompletionEncodeBHist S))
            (riemannIntegrationCompletionDecodeBHist
              (riemannIntegrationCompletionEncodeBHist Q))
            (riemannIntegrationCompletionDecodeBHist
              (riemannIntegrationCompletionEncodeBHist R))
            (riemannIntegrationCompletionDecodeBHist
              (riemannIntegrationCompletionEncodeBHist E))
            (riemannIntegrationCompletionDecodeBHist
              (riemannIntegrationCompletionEncodeBHist H))
            (riemannIntegrationCompletionDecodeBHist
              (riemannIntegrationCompletionEncodeBHist C))
            (riemannIntegrationCompletionDecodeBHist
              (riemannIntegrationCompletionEncodeBHist P))
            (riemannIntegrationCompletionDecodeBHist
              (riemannIntegrationCompletionEncodeBHist N))) =
          some (RiemannIntegrationCompletionUp.mk I G S Q R E H C P N)
      rw [RiemannIntegrationCompletionTasteGate_single_carrier_alignment_decode_encode I,
        RiemannIntegrationCompletionTasteGate_single_carrier_alignment_decode_encode G,
        RiemannIntegrationCompletionTasteGate_single_carrier_alignment_decode_encode S,
        RiemannIntegrationCompletionTasteGate_single_carrier_alignment_decode_encode Q,
        RiemannIntegrationCompletionTasteGate_single_carrier_alignment_decode_encode R,
        RiemannIntegrationCompletionTasteGate_single_carrier_alignment_decode_encode E,
        RiemannIntegrationCompletionTasteGate_single_carrier_alignment_decode_encode H,
        RiemannIntegrationCompletionTasteGate_single_carrier_alignment_decode_encode C,
        RiemannIntegrationCompletionTasteGate_single_carrier_alignment_decode_encode P,
        RiemannIntegrationCompletionTasteGate_single_carrier_alignment_decode_encode N]

private theorem RiemannIntegrationCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RiemannIntegrationCompletionUp} :
    riemannIntegrationCompletionToEventFlow x =
      riemannIntegrationCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      riemannIntegrationCompletionFromEventFlow (riemannIntegrationCompletionToEventFlow x) =
        riemannIntegrationCompletionFromEventFlow (riemannIntegrationCompletionToEventFlow y) :=
    congrArg riemannIntegrationCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RiemannIntegrationCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RiemannIntegrationCompletionTasteGate_single_carrier_alignment_round_trip y)))

instance riemannIntegrationCompletionBHistCarrier :
    BHistCarrier RiemannIntegrationCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := riemannIntegrationCompletionToEventFlow
  fromEventFlow := riemannIntegrationCompletionFromEventFlow

instance riemannIntegrationCompletionChapterTasteGate :
    ChapterTasteGate RiemannIntegrationCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      riemannIntegrationCompletionFromEventFlow
        (riemannIntegrationCompletionToEventFlow x) = some x
    exact RiemannIntegrationCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RiemannIntegrationCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem RiemannIntegrationCompletionTasteGate_single_carrier_alignment :
    (riemannIntegrationCompletionEncodeBHist BHist.Empty = ([] : List BMark)) ∧
      (∀ h : BHist,
        riemannIntegrationCompletionDecodeBHist
          (riemannIntegrationCompletionEncodeBHist h) = h) ∧
        (∀ x : RiemannIntegrationCompletionUp,
          riemannIntegrationCompletionFromEventFlow
            (riemannIntegrationCompletionToEventFlow x) = some x) ∧
          Nonempty (BHistCarrier RiemannIntegrationCompletionUp) ∧
            Nonempty (ChapterTasteGate RiemannIntegrationCompletionUp) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨rfl,
      RiemannIntegrationCompletionTasteGate_single_carrier_alignment_decode_encode,
      RiemannIntegrationCompletionTasteGate_single_carrier_alignment_round_trip,
      ⟨riemannIntegrationCompletionBHistCarrier⟩,
      ⟨riemannIntegrationCompletionChapterTasteGate⟩⟩

end BEDC.Derived.RiemannIntegrationCompletionUp
