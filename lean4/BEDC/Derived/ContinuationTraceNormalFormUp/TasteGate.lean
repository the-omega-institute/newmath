import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ContinuationTraceNormalFormUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ContinuationTraceNormalFormUp : Type where
  | mk (S T R Q V H C P N : BHist) : ContinuationTraceNormalFormUp
  deriving DecidableEq

def continuationTraceNormalFormEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: continuationTraceNormalFormEncodeBHist h
  | BHist.e1 h => BMark.b1 :: continuationTraceNormalFormEncodeBHist h

def continuationTraceNormalFormDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (continuationTraceNormalFormDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (continuationTraceNormalFormDecodeBHist tail)

private theorem ContinuationTraceNormalFormTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      continuationTraceNormalFormDecodeBHist (continuationTraceNormalFormEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def continuationTraceNormalFormFields :
    ContinuationTraceNormalFormUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ContinuationTraceNormalFormUp.mk S T R Q V H C P N => [S, T, R, Q, V, H, C, P, N]

def continuationTraceNormalFormToEventFlow :
    ContinuationTraceNormalFormUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | token =>
      (continuationTraceNormalFormFields token).map continuationTraceNormalFormEncodeBHist

private def continuationTraceNormalFormEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => continuationTraceNormalFormEventAtDefault index rest

def continuationTraceNormalFormFromEventFlow
    (ef : EventFlow) : Option ContinuationTraceNormalFormUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ContinuationTraceNormalFormUp.mk
      (continuationTraceNormalFormDecodeBHist
        (continuationTraceNormalFormEventAtDefault 0 ef))
      (continuationTraceNormalFormDecodeBHist
        (continuationTraceNormalFormEventAtDefault 1 ef))
      (continuationTraceNormalFormDecodeBHist
        (continuationTraceNormalFormEventAtDefault 2 ef))
      (continuationTraceNormalFormDecodeBHist
        (continuationTraceNormalFormEventAtDefault 3 ef))
      (continuationTraceNormalFormDecodeBHist
        (continuationTraceNormalFormEventAtDefault 4 ef))
      (continuationTraceNormalFormDecodeBHist
        (continuationTraceNormalFormEventAtDefault 5 ef))
      (continuationTraceNormalFormDecodeBHist
        (continuationTraceNormalFormEventAtDefault 6 ef))
      (continuationTraceNormalFormDecodeBHist
        (continuationTraceNormalFormEventAtDefault 7 ef))
      (continuationTraceNormalFormDecodeBHist
        (continuationTraceNormalFormEventAtDefault 8 ef)))

private theorem ContinuationTraceNormalFormTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ContinuationTraceNormalFormUp,
      continuationTraceNormalFormFromEventFlow
        (continuationTraceNormalFormToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk S T R Q V H C P N =>
      change
        some
          (ContinuationTraceNormalFormUp.mk
            (continuationTraceNormalFormDecodeBHist
              (continuationTraceNormalFormEncodeBHist S))
            (continuationTraceNormalFormDecodeBHist
              (continuationTraceNormalFormEncodeBHist T))
            (continuationTraceNormalFormDecodeBHist
              (continuationTraceNormalFormEncodeBHist R))
            (continuationTraceNormalFormDecodeBHist
              (continuationTraceNormalFormEncodeBHist Q))
            (continuationTraceNormalFormDecodeBHist
              (continuationTraceNormalFormEncodeBHist V))
            (continuationTraceNormalFormDecodeBHist
              (continuationTraceNormalFormEncodeBHist H))
            (continuationTraceNormalFormDecodeBHist
              (continuationTraceNormalFormEncodeBHist C))
            (continuationTraceNormalFormDecodeBHist
              (continuationTraceNormalFormEncodeBHist P))
            (continuationTraceNormalFormDecodeBHist
              (continuationTraceNormalFormEncodeBHist N))) =
          some (ContinuationTraceNormalFormUp.mk S T R Q V H C P N)
      rw [ContinuationTraceNormalFormTasteGate_single_carrier_alignment_decode S,
        ContinuationTraceNormalFormTasteGate_single_carrier_alignment_decode T,
        ContinuationTraceNormalFormTasteGate_single_carrier_alignment_decode R,
        ContinuationTraceNormalFormTasteGate_single_carrier_alignment_decode Q,
        ContinuationTraceNormalFormTasteGate_single_carrier_alignment_decode V,
        ContinuationTraceNormalFormTasteGate_single_carrier_alignment_decode H,
        ContinuationTraceNormalFormTasteGate_single_carrier_alignment_decode C,
        ContinuationTraceNormalFormTasteGate_single_carrier_alignment_decode P,
        ContinuationTraceNormalFormTasteGate_single_carrier_alignment_decode N]

private theorem ContinuationTraceNormalFormTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ContinuationTraceNormalFormUp} :
    continuationTraceNormalFormToEventFlow x = continuationTraceNormalFormToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      continuationTraceNormalFormFromEventFlow (continuationTraceNormalFormToEventFlow x) =
        continuationTraceNormalFormFromEventFlow
          (continuationTraceNormalFormToEventFlow y) :=
    congrArg continuationTraceNormalFormFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ContinuationTraceNormalFormTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ContinuationTraceNormalFormTasteGate_single_carrier_alignment_round_trip y)))

private theorem ContinuationTraceNormalFormTasteGate_single_carrier_alignment_fields :
    ∀ x y : ContinuationTraceNormalFormUp,
      continuationTraceNormalFormFields x = continuationTraceNormalFormFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 T1 R1 Q1 V1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 T2 R2 Q2 V2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance continuationTraceNormalFormBHistCarrier :
    BHistCarrier ContinuationTraceNormalFormUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := continuationTraceNormalFormToEventFlow
  fromEventFlow := continuationTraceNormalFormFromEventFlow

instance continuationTraceNormalFormChapterTasteGate :
    ChapterTasteGate ContinuationTraceNormalFormUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      continuationTraceNormalFormFromEventFlow
        (continuationTraceNormalFormToEventFlow x) = some x
    exact ContinuationTraceNormalFormTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (ContinuationTraceNormalFormTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance continuationTraceNormalFormFieldFaithful :
    FieldFaithful ContinuationTraceNormalFormUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := continuationTraceNormalFormFields
  field_faithful := ContinuationTraceNormalFormTasteGate_single_carrier_alignment_fields

theorem ContinuationTraceNormalFormTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      continuationTraceNormalFormDecodeBHist (continuationTraceNormalFormEncodeBHist h) = h) ∧
      (∀ x : ContinuationTraceNormalFormUp,
        continuationTraceNormalFormFromEventFlow
          (continuationTraceNormalFormToEventFlow x) = some x) ∧
        (∀ x y : ContinuationTraceNormalFormUp,
          continuationTraceNormalFormToEventFlow x =
            continuationTraceNormalFormToEventFlow y → x = y) ∧
          continuationTraceNormalFormEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨ContinuationTraceNormalFormTasteGate_single_carrier_alignment_decode,
      ContinuationTraceNormalFormTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        ContinuationTraceNormalFormTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.ContinuationTraceNormalFormUp
