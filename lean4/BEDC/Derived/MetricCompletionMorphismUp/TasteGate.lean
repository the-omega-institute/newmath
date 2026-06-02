import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetricCompletionMorphismUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetricCompletionMorphismUp : Type where
  | mk (S T W R D M H C P N : BHist) : MetricCompletionMorphismUp
  deriving DecidableEq

def metricCompletionMorphismEncodeBHist : BHist → List BMark
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metricCompletionMorphismEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metricCompletionMorphismEncodeBHist h

def metricCompletionMorphismDecodeBHist : List BMark → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metricCompletionMorphismDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metricCompletionMorphismDecodeBHist tail)

private theorem MetricCompletionMorphismTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      metricCompletionMorphismDecodeBHist (metricCompletionMorphismEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metricCompletionMorphismFields : MetricCompletionMorphismUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetricCompletionMorphismUp.mk S T W R D M H C P N => [S, T, W, R, D, M, H, C, P, N]

def metricCompletionMorphismToEventFlow : MetricCompletionMorphismUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (metricCompletionMorphismFields x).map metricCompletionMorphismEncodeBHist

private def metricCompletionMorphismEventAtDefault : Nat → EventFlow → List BMark
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => metricCompletionMorphismEventAtDefault index rest

def metricCompletionMorphismFromEventFlow (ef : EventFlow) :
    Option MetricCompletionMorphismUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MetricCompletionMorphismUp.mk
      (metricCompletionMorphismDecodeBHist (metricCompletionMorphismEventAtDefault 0 ef))
      (metricCompletionMorphismDecodeBHist (metricCompletionMorphismEventAtDefault 1 ef))
      (metricCompletionMorphismDecodeBHist (metricCompletionMorphismEventAtDefault 2 ef))
      (metricCompletionMorphismDecodeBHist (metricCompletionMorphismEventAtDefault 3 ef))
      (metricCompletionMorphismDecodeBHist (metricCompletionMorphismEventAtDefault 4 ef))
      (metricCompletionMorphismDecodeBHist (metricCompletionMorphismEventAtDefault 5 ef))
      (metricCompletionMorphismDecodeBHist (metricCompletionMorphismEventAtDefault 6 ef))
      (metricCompletionMorphismDecodeBHist (metricCompletionMorphismEventAtDefault 7 ef))
      (metricCompletionMorphismDecodeBHist (metricCompletionMorphismEventAtDefault 8 ef))
      (metricCompletionMorphismDecodeBHist (metricCompletionMorphismEventAtDefault 9 ef)))

private theorem MetricCompletionMorphismTasteGate_single_carrier_alignment_round_trip :
    ∀ x : MetricCompletionMorphismUp,
      metricCompletionMorphismFromEventFlow (metricCompletionMorphismToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S T W R D M H C P N =>
      change
        some
          (MetricCompletionMorphismUp.mk
            (metricCompletionMorphismDecodeBHist (metricCompletionMorphismEncodeBHist S))
            (metricCompletionMorphismDecodeBHist (metricCompletionMorphismEncodeBHist T))
            (metricCompletionMorphismDecodeBHist (metricCompletionMorphismEncodeBHist W))
            (metricCompletionMorphismDecodeBHist (metricCompletionMorphismEncodeBHist R))
            (metricCompletionMorphismDecodeBHist (metricCompletionMorphismEncodeBHist D))
            (metricCompletionMorphismDecodeBHist (metricCompletionMorphismEncodeBHist M))
            (metricCompletionMorphismDecodeBHist (metricCompletionMorphismEncodeBHist H))
            (metricCompletionMorphismDecodeBHist (metricCompletionMorphismEncodeBHist C))
            (metricCompletionMorphismDecodeBHist (metricCompletionMorphismEncodeBHist P))
            (metricCompletionMorphismDecodeBHist (metricCompletionMorphismEncodeBHist N))) =
          some (MetricCompletionMorphismUp.mk S T W R D M H C P N)
      rw [MetricCompletionMorphismTasteGate_single_carrier_alignment_decode S,
        MetricCompletionMorphismTasteGate_single_carrier_alignment_decode T,
        MetricCompletionMorphismTasteGate_single_carrier_alignment_decode W,
        MetricCompletionMorphismTasteGate_single_carrier_alignment_decode R,
        MetricCompletionMorphismTasteGate_single_carrier_alignment_decode D,
        MetricCompletionMorphismTasteGate_single_carrier_alignment_decode M,
        MetricCompletionMorphismTasteGate_single_carrier_alignment_decode H,
        MetricCompletionMorphismTasteGate_single_carrier_alignment_decode C,
        MetricCompletionMorphismTasteGate_single_carrier_alignment_decode P,
        MetricCompletionMorphismTasteGate_single_carrier_alignment_decode N]

private theorem MetricCompletionMorphismTasteGate_single_carrier_alignment_injective
    {x y : MetricCompletionMorphismUp} :
    metricCompletionMorphismToEventFlow x = metricCompletionMorphismToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metricCompletionMorphismFromEventFlow (metricCompletionMorphismToEventFlow x) =
        metricCompletionMorphismFromEventFlow (metricCompletionMorphismToEventFlow y) :=
    congrArg metricCompletionMorphismFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (MetricCompletionMorphismTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (MetricCompletionMorphismTasteGate_single_carrier_alignment_round_trip y)))

private theorem MetricCompletionMorphismTasteGate_single_carrier_alignment_fields :
    ∀ x y : MetricCompletionMorphismUp,
      metricCompletionMorphismFields x = metricCompletionMorphismFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 T1 W1 R1 D1 M1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 T2 W2 R2 D2 M2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance metricCompletionMorphismBHistCarrier : BHistCarrier MetricCompletionMorphismUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metricCompletionMorphismToEventFlow
  fromEventFlow := metricCompletionMorphismFromEventFlow

instance metricCompletionMorphismChapterTasteGate :
    ChapterTasteGate MetricCompletionMorphismUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metricCompletionMorphismFromEventFlow (metricCompletionMorphismToEventFlow x) = some x
    exact MetricCompletionMorphismTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MetricCompletionMorphismTasteGate_single_carrier_alignment_injective heq)

instance metricCompletionMorphismFieldFaithful :
    FieldFaithful MetricCompletionMorphismUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metricCompletionMorphismFields
  field_faithful := MetricCompletionMorphismTasteGate_single_carrier_alignment_fields

def taste_gate : ChapterTasteGate MetricCompletionMorphismUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metricCompletionMorphismChapterTasteGate

def taste_gate_witness : FieldFaithful MetricCompletionMorphismUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metricCompletionMorphismFieldFaithful

theorem MetricCompletionMorphismTasteGate_single_carrier_alignment :
    (forall h : BHist,
      metricCompletionMorphismDecodeBHist (metricCompletionMorphismEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier MetricCompletionMorphismUp) ∧
        Nonempty (ChapterTasteGate MetricCompletionMorphismUp) ∧
          metricCompletionMorphismEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact MetricCompletionMorphismTasteGate_single_carrier_alignment_decode
  constructor
  · exact ⟨metricCompletionMorphismBHistCarrier⟩
  constructor
  · exact ⟨metricCompletionMorphismChapterTasteGate⟩
  · rfl

end BEDC.Derived.MetricCompletionMorphismUp
