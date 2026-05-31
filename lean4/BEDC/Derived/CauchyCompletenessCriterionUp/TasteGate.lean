import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletenessCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletenessCriterionUp : Type where
  | mk (M Mu S R D E H C P N : BHist) : CauchyCompletenessCriterionUp
  deriving DecidableEq

def cauchyCompletenessCriterionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletenessCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletenessCriterionEncodeBHist h

def cauchyCompletenessCriterionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletenessCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletenessCriterionDecodeBHist tail)

private theorem CauchyCompletenessCriterionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyCompletenessCriterionDecodeBHist
        (cauchyCompletenessCriterionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCompletenessCriterionFields :
    CauchyCompletenessCriterionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletenessCriterionUp.mk M Mu S R D E H C P N =>
      [M, Mu, S, R, D, E, H, C, P, N]

def cauchyCompletenessCriterionToEventFlow :
    CauchyCompletenessCriterionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (cauchyCompletenessCriterionFields x).map
      cauchyCompletenessCriterionEncodeBHist

private def cauchyCompletenessCriterionEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      cauchyCompletenessCriterionEventAtDefault index rest

def cauchyCompletenessCriterionFromEventFlow
    (ef : EventFlow) : Option CauchyCompletenessCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyCompletenessCriterionUp.mk
      (cauchyCompletenessCriterionDecodeBHist
        (cauchyCompletenessCriterionEventAtDefault 0 ef))
      (cauchyCompletenessCriterionDecodeBHist
        (cauchyCompletenessCriterionEventAtDefault 1 ef))
      (cauchyCompletenessCriterionDecodeBHist
        (cauchyCompletenessCriterionEventAtDefault 2 ef))
      (cauchyCompletenessCriterionDecodeBHist
        (cauchyCompletenessCriterionEventAtDefault 3 ef))
      (cauchyCompletenessCriterionDecodeBHist
        (cauchyCompletenessCriterionEventAtDefault 4 ef))
      (cauchyCompletenessCriterionDecodeBHist
        (cauchyCompletenessCriterionEventAtDefault 5 ef))
      (cauchyCompletenessCriterionDecodeBHist
        (cauchyCompletenessCriterionEventAtDefault 6 ef))
      (cauchyCompletenessCriterionDecodeBHist
        (cauchyCompletenessCriterionEventAtDefault 7 ef))
      (cauchyCompletenessCriterionDecodeBHist
        (cauchyCompletenessCriterionEventAtDefault 8 ef))
      (cauchyCompletenessCriterionDecodeBHist
        (cauchyCompletenessCriterionEventAtDefault 9 ef)))

private theorem CauchyCompletenessCriterionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyCompletenessCriterionUp,
      cauchyCompletenessCriterionFromEventFlow
        (cauchyCompletenessCriterionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M Mu S R D E H C P N =>
      change
        some
            (CauchyCompletenessCriterionUp.mk
              (cauchyCompletenessCriterionDecodeBHist
                (cauchyCompletenessCriterionEncodeBHist M))
              (cauchyCompletenessCriterionDecodeBHist
                (cauchyCompletenessCriterionEncodeBHist Mu))
              (cauchyCompletenessCriterionDecodeBHist
                (cauchyCompletenessCriterionEncodeBHist S))
              (cauchyCompletenessCriterionDecodeBHist
                (cauchyCompletenessCriterionEncodeBHist R))
              (cauchyCompletenessCriterionDecodeBHist
                (cauchyCompletenessCriterionEncodeBHist D))
              (cauchyCompletenessCriterionDecodeBHist
                (cauchyCompletenessCriterionEncodeBHist E))
              (cauchyCompletenessCriterionDecodeBHist
                (cauchyCompletenessCriterionEncodeBHist H))
              (cauchyCompletenessCriterionDecodeBHist
                (cauchyCompletenessCriterionEncodeBHist C))
              (cauchyCompletenessCriterionDecodeBHist
                (cauchyCompletenessCriterionEncodeBHist P))
              (cauchyCompletenessCriterionDecodeBHist
                (cauchyCompletenessCriterionEncodeBHist N))) =
          some (CauchyCompletenessCriterionUp.mk M Mu S R D E H C P N)
      rw [CauchyCompletenessCriterionTasteGate_single_carrier_alignment_decode_encode M,
        CauchyCompletenessCriterionTasteGate_single_carrier_alignment_decode_encode Mu,
        CauchyCompletenessCriterionTasteGate_single_carrier_alignment_decode_encode S,
        CauchyCompletenessCriterionTasteGate_single_carrier_alignment_decode_encode R,
        CauchyCompletenessCriterionTasteGate_single_carrier_alignment_decode_encode D,
        CauchyCompletenessCriterionTasteGate_single_carrier_alignment_decode_encode E,
        CauchyCompletenessCriterionTasteGate_single_carrier_alignment_decode_encode H,
        CauchyCompletenessCriterionTasteGate_single_carrier_alignment_decode_encode C,
        CauchyCompletenessCriterionTasteGate_single_carrier_alignment_decode_encode P,
        CauchyCompletenessCriterionTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyCompletenessCriterionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyCompletenessCriterionUp} :
    cauchyCompletenessCriterionToEventFlow x =
        cauchyCompletenessCriterionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletenessCriterionFromEventFlow
          (cauchyCompletenessCriterionToEventFlow x) =
        cauchyCompletenessCriterionFromEventFlow
          (cauchyCompletenessCriterionToEventFlow y) :=
    congrArg cauchyCompletenessCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyCompletenessCriterionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyCompletenessCriterionTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyCompletenessCriterionBHistCarrier :
    BHistCarrier CauchyCompletenessCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletenessCriterionToEventFlow
  fromEventFlow := cauchyCompletenessCriterionFromEventFlow

instance cauchyCompletenessCriterionChapterTasteGate :
    ChapterTasteGate CauchyCompletenessCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompletenessCriterionFromEventFlow
        (cauchyCompletenessCriterionToEventFlow x) = some x
    exact CauchyCompletenessCriterionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyCompletenessCriterionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CauchyCompletenessCriterionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        cauchyCompletenessCriterionDecodeBHist
          (cauchyCompletenessCriterionEncodeBHist h) = h) ∧
      (∀ x : CauchyCompletenessCriterionUp,
        cauchyCompletenessCriterionFromEventFlow
          (cauchyCompletenessCriterionToEventFlow x) = some x) ∧
        (∀ x y : CauchyCompletenessCriterionUp,
          cauchyCompletenessCriterionToEventFlow x =
              cauchyCompletenessCriterionToEventFlow y →
            x = y) ∧
          cauchyCompletenessCriterionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CauchyCompletenessCriterionTasteGate_single_carrier_alignment_decode_encode,
      CauchyCompletenessCriterionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CauchyCompletenessCriterionTasteGate_single_carrier_alignment_toEventFlow_injective
          heq),
      rfl⟩

end BEDC.Derived.CauchyCompletenessCriterionUp
