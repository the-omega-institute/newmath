import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetricCompletionKleisliUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetricCompletionKleisliUp : Type where
  | mk (M A L U R E H C P N : BHist) : MetricCompletionKleisliUp
  deriving DecidableEq

def metricCompletionKleisliEncodeBHist : BHist → List BMark
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metricCompletionKleisliEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metricCompletionKleisliEncodeBHist h

def metricCompletionKleisliDecodeBHist : List BMark → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metricCompletionKleisliDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metricCompletionKleisliDecodeBHist tail)

private theorem MetricCompletionKleisliTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      metricCompletionKleisliDecodeBHist (metricCompletionKleisliEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metricCompletionKleisliFields : MetricCompletionKleisliUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetricCompletionKleisliUp.mk M A L U R E H C P N => [M, A, L, U, R, E, H, C, P, N]

def metricCompletionKleisliToEventFlow : MetricCompletionKleisliUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (metricCompletionKleisliFields x).map metricCompletionKleisliEncodeBHist

private def metricCompletionKleisliEventAtDefault : Nat → EventFlow → List BMark
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => metricCompletionKleisliEventAtDefault index rest

def metricCompletionKleisliFromEventFlow (ef : EventFlow) : Option MetricCompletionKleisliUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MetricCompletionKleisliUp.mk
      (metricCompletionKleisliDecodeBHist (metricCompletionKleisliEventAtDefault 0 ef))
      (metricCompletionKleisliDecodeBHist (metricCompletionKleisliEventAtDefault 1 ef))
      (metricCompletionKleisliDecodeBHist (metricCompletionKleisliEventAtDefault 2 ef))
      (metricCompletionKleisliDecodeBHist (metricCompletionKleisliEventAtDefault 3 ef))
      (metricCompletionKleisliDecodeBHist (metricCompletionKleisliEventAtDefault 4 ef))
      (metricCompletionKleisliDecodeBHist (metricCompletionKleisliEventAtDefault 5 ef))
      (metricCompletionKleisliDecodeBHist (metricCompletionKleisliEventAtDefault 6 ef))
      (metricCompletionKleisliDecodeBHist (metricCompletionKleisliEventAtDefault 7 ef))
      (metricCompletionKleisliDecodeBHist (metricCompletionKleisliEventAtDefault 8 ef))
      (metricCompletionKleisliDecodeBHist (metricCompletionKleisliEventAtDefault 9 ef)))

private theorem MetricCompletionKleisliTasteGate_single_carrier_alignment_round_trip :
    ∀ x : MetricCompletionKleisliUp,
      metricCompletionKleisliFromEventFlow (metricCompletionKleisliToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M A L U R E H C P N =>
      change
        some
          (MetricCompletionKleisliUp.mk
            (metricCompletionKleisliDecodeBHist (metricCompletionKleisliEncodeBHist M))
            (metricCompletionKleisliDecodeBHist (metricCompletionKleisliEncodeBHist A))
            (metricCompletionKleisliDecodeBHist (metricCompletionKleisliEncodeBHist L))
            (metricCompletionKleisliDecodeBHist (metricCompletionKleisliEncodeBHist U))
            (metricCompletionKleisliDecodeBHist (metricCompletionKleisliEncodeBHist R))
            (metricCompletionKleisliDecodeBHist (metricCompletionKleisliEncodeBHist E))
            (metricCompletionKleisliDecodeBHist (metricCompletionKleisliEncodeBHist H))
            (metricCompletionKleisliDecodeBHist (metricCompletionKleisliEncodeBHist C))
            (metricCompletionKleisliDecodeBHist (metricCompletionKleisliEncodeBHist P))
            (metricCompletionKleisliDecodeBHist (metricCompletionKleisliEncodeBHist N))) =
          some (MetricCompletionKleisliUp.mk M A L U R E H C P N)
      rw [MetricCompletionKleisliTasteGate_single_carrier_alignment_decode M,
        MetricCompletionKleisliTasteGate_single_carrier_alignment_decode A,
        MetricCompletionKleisliTasteGate_single_carrier_alignment_decode L,
        MetricCompletionKleisliTasteGate_single_carrier_alignment_decode U,
        MetricCompletionKleisliTasteGate_single_carrier_alignment_decode R,
        MetricCompletionKleisliTasteGate_single_carrier_alignment_decode E,
        MetricCompletionKleisliTasteGate_single_carrier_alignment_decode H,
        MetricCompletionKleisliTasteGate_single_carrier_alignment_decode C,
        MetricCompletionKleisliTasteGate_single_carrier_alignment_decode P,
        MetricCompletionKleisliTasteGate_single_carrier_alignment_decode N]

private theorem MetricCompletionKleisliTasteGate_single_carrier_alignment_injective
    {x y : MetricCompletionKleisliUp} :
    metricCompletionKleisliToEventFlow x = metricCompletionKleisliToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metricCompletionKleisliFromEventFlow (metricCompletionKleisliToEventFlow x) =
        metricCompletionKleisliFromEventFlow (metricCompletionKleisliToEventFlow y) :=
    congrArg metricCompletionKleisliFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (MetricCompletionKleisliTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (MetricCompletionKleisliTasteGate_single_carrier_alignment_round_trip y)))

private theorem MetricCompletionKleisliTasteGate_single_carrier_alignment_fields :
    ∀ x y : MetricCompletionKleisliUp,
      metricCompletionKleisliFields x = metricCompletionKleisliFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M1 A1 L1 U1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk M2 A2 L2 U2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance metricCompletionKleisliBHistCarrier : BHistCarrier MetricCompletionKleisliUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metricCompletionKleisliToEventFlow
  fromEventFlow := metricCompletionKleisliFromEventFlow

instance metricCompletionKleisliChapterTasteGate :
    ChapterTasteGate MetricCompletionKleisliUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change metricCompletionKleisliFromEventFlow (metricCompletionKleisliToEventFlow x) = some x
    exact MetricCompletionKleisliTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MetricCompletionKleisliTasteGate_single_carrier_alignment_injective heq)

instance metricCompletionKleisliFieldFaithful : FieldFaithful MetricCompletionKleisliUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metricCompletionKleisliFields
  field_faithful := MetricCompletionKleisliTasteGate_single_carrier_alignment_fields

def taste_gate : ChapterTasteGate MetricCompletionKleisliUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metricCompletionKleisliChapterTasteGate

def taste_gate_witness : FieldFaithful MetricCompletionKleisliUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metricCompletionKleisliFieldFaithful

theorem MetricCompletionKleisliTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      metricCompletionKleisliDecodeBHist (metricCompletionKleisliEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier MetricCompletionKleisliUp) ∧
        Nonempty (ChapterTasteGate MetricCompletionKleisliUp) ∧
          metricCompletionKleisliEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  constructor
  · exact ⟨metricCompletionKleisliBHistCarrier⟩
  constructor
  · exact ⟨metricCompletionKleisliChapterTasteGate⟩
  · rfl

end BEDC.Derived.MetricCompletionKleisliUp
