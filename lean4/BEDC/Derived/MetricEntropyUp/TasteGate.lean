import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetricEntropyUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetricEntropyUp : Type where
  | mk (X epsilon N C M H K P L : BHist) : MetricEntropyUp

def metricEntropyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metricEntropyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metricEntropyEncodeBHist h

def metricEntropyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metricEntropyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metricEntropyDecodeBHist tail)

private theorem MetricEntropyTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      metricEntropyDecodeBHist (metricEntropyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def metricEntropyFields : MetricEntropyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetricEntropyUp.mk X epsilon N C M H K P L =>
      [X, epsilon, N, C, M, H, K, P, L]

def metricEntropyToEventFlow : MetricEntropyUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (metricEntropyFields x).map metricEntropyEncodeBHist

def metricEntropyFromEventFlow : EventFlow → Option MetricEntropyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun eventFlow =>
    match eventFlow with
    | [] => none
    | _ :: [] => none
    | _ :: _ :: [] => none
    | _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
    | X :: epsilon :: N :: C :: M :: H :: K :: P :: L :: [] =>
        some
          (MetricEntropyUp.mk
            (metricEntropyDecodeBHist X)
            (metricEntropyDecodeBHist epsilon)
            (metricEntropyDecodeBHist N)
            (metricEntropyDecodeBHist C)
            (metricEntropyDecodeBHist M)
            (metricEntropyDecodeBHist H)
            (metricEntropyDecodeBHist K)
            (metricEntropyDecodeBHist P)
            (metricEntropyDecodeBHist L))
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ => none

def metricEntropyCarrier : BHistCarrier MetricEntropyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metricEntropyToEventFlow
  fromEventFlow := metricEntropyFromEventFlow

instance metricEntropyBHistCarrier : BHistCarrier MetricEntropyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metricEntropyCarrier

private theorem MetricEntropyTasteGate_single_carrier_alignment_round_trip :
    ∀ x : MetricEntropyUp,
      BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X epsilon N C M H K P L =>
      change
        some
            (MetricEntropyUp.mk
              (metricEntropyDecodeBHist (metricEntropyEncodeBHist X))
              (metricEntropyDecodeBHist (metricEntropyEncodeBHist epsilon))
              (metricEntropyDecodeBHist (metricEntropyEncodeBHist N))
              (metricEntropyDecodeBHist (metricEntropyEncodeBHist C))
              (metricEntropyDecodeBHist (metricEntropyEncodeBHist M))
              (metricEntropyDecodeBHist (metricEntropyEncodeBHist H))
              (metricEntropyDecodeBHist (metricEntropyEncodeBHist K))
              (metricEntropyDecodeBHist (metricEntropyEncodeBHist P))
              (metricEntropyDecodeBHist (metricEntropyEncodeBHist L))) =
          some (MetricEntropyUp.mk X epsilon N C M H K P L)
      rw [MetricEntropyTasteGate_single_carrier_alignment_decode_encode X]
      rw [MetricEntropyTasteGate_single_carrier_alignment_decode_encode epsilon]
      rw [MetricEntropyTasteGate_single_carrier_alignment_decode_encode N]
      rw [MetricEntropyTasteGate_single_carrier_alignment_decode_encode C]
      rw [MetricEntropyTasteGate_single_carrier_alignment_decode_encode M]
      rw [MetricEntropyTasteGate_single_carrier_alignment_decode_encode H]
      rw [MetricEntropyTasteGate_single_carrier_alignment_decode_encode K]
      rw [MetricEntropyTasteGate_single_carrier_alignment_decode_encode P]
      rw [MetricEntropyTasteGate_single_carrier_alignment_decode_encode L]

private theorem MetricEntropyTasteGate_single_carrier_alignment_ToEventFlow_injective
    {x y : MetricEntropyUp} :
    BHistCarrier.toEventFlow x = BHistCarrier.toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x = BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) :=
        (MetricEntropyTasteGate_single_carrier_alignment_round_trip x).symm
      _ = BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow y) :=
        congrArg BHistCarrier.fromEventFlow hxy
      _ = some y := MetricEntropyTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

def metricEntropyGate : @ChapterTasteGate MetricEntropyUp metricEntropyCarrier where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    exact MetricEntropyTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MetricEntropyTasteGate_single_carrier_alignment_ToEventFlow_injective heq)

instance metricEntropyChapterTasteGate : ChapterTasteGate MetricEntropyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metricEntropyGate

theorem MetricEntropyTasteGate_single_carrier_alignment :
    (∀ h : BHist, metricEntropyDecodeBHist (metricEntropyEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier MetricEntropyUp) ∧
        Nonempty (ChapterTasteGate MetricEntropyUp) ∧
          metricEntropyEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨MetricEntropyTasteGate_single_carrier_alignment_decode_encode,
      ⟨⟨metricEntropyCarrier⟩, ⟨⟨metricEntropyGate⟩, rfl⟩⟩⟩

end BEDC.Derived.MetricEntropyUp.TasteGate
