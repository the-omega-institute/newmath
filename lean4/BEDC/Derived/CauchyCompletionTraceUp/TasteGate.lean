import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionTraceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionTraceUp : Type where
  | mk (source sectionRow replay completion boundary transport provenance name : BHist) :
      CauchyCompletionTraceUp
  deriving DecidableEq

def cauchyCompletionTraceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionTraceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionTraceEncodeBHist h

def cauchyCompletionTraceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionTraceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionTraceDecodeBHist tail)

private theorem CauchyCompletionTraceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, cauchyCompletionTraceDecodeBHist (cauchyCompletionTraceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCompletionTraceFields : CauchyCompletionTraceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionTraceUp.mk source sectionRow replay completion boundary transport provenance name =>
      [source, sectionRow, replay, completion, boundary, transport, provenance, name]

def cauchyCompletionTraceToEventFlow : CauchyCompletionTraceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyCompletionTraceFields x).map cauchyCompletionTraceEncodeBHist

private def cauchyCompletionTraceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyCompletionTraceEventAtDefault index rest

def cauchyCompletionTraceFromEventFlow : EventFlow → Option CauchyCompletionTraceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (CauchyCompletionTraceUp.mk
        (cauchyCompletionTraceDecodeBHist (cauchyCompletionTraceEventAtDefault 0 ef))
        (cauchyCompletionTraceDecodeBHist (cauchyCompletionTraceEventAtDefault 1 ef))
        (cauchyCompletionTraceDecodeBHist (cauchyCompletionTraceEventAtDefault 2 ef))
        (cauchyCompletionTraceDecodeBHist (cauchyCompletionTraceEventAtDefault 3 ef))
        (cauchyCompletionTraceDecodeBHist (cauchyCompletionTraceEventAtDefault 4 ef))
        (cauchyCompletionTraceDecodeBHist (cauchyCompletionTraceEventAtDefault 5 ef))
        (cauchyCompletionTraceDecodeBHist (cauchyCompletionTraceEventAtDefault 6 ef))
        (cauchyCompletionTraceDecodeBHist (cauchyCompletionTraceEventAtDefault 7 ef)))

private theorem CauchyCompletionTraceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyCompletionTraceUp,
      cauchyCompletionTraceFromEventFlow (cauchyCompletionTraceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk source sectionRow replay completion boundary transport provenance name =>
      change
        some
          (CauchyCompletionTraceUp.mk
            (cauchyCompletionTraceDecodeBHist (cauchyCompletionTraceEncodeBHist source))
            (cauchyCompletionTraceDecodeBHist (cauchyCompletionTraceEncodeBHist sectionRow))
            (cauchyCompletionTraceDecodeBHist (cauchyCompletionTraceEncodeBHist replay))
            (cauchyCompletionTraceDecodeBHist (cauchyCompletionTraceEncodeBHist completion))
            (cauchyCompletionTraceDecodeBHist (cauchyCompletionTraceEncodeBHist boundary))
            (cauchyCompletionTraceDecodeBHist (cauchyCompletionTraceEncodeBHist transport))
            (cauchyCompletionTraceDecodeBHist (cauchyCompletionTraceEncodeBHist provenance))
            (cauchyCompletionTraceDecodeBHist (cauchyCompletionTraceEncodeBHist name))) =
          some
            (CauchyCompletionTraceUp.mk source sectionRow replay completion boundary transport
              provenance name)
      rw [CauchyCompletionTraceTasteGate_single_carrier_alignment_decode_encode source,
        CauchyCompletionTraceTasteGate_single_carrier_alignment_decode_encode sectionRow,
        CauchyCompletionTraceTasteGate_single_carrier_alignment_decode_encode replay,
        CauchyCompletionTraceTasteGate_single_carrier_alignment_decode_encode completion,
        CauchyCompletionTraceTasteGate_single_carrier_alignment_decode_encode boundary,
        CauchyCompletionTraceTasteGate_single_carrier_alignment_decode_encode transport,
        CauchyCompletionTraceTasteGate_single_carrier_alignment_decode_encode provenance,
        CauchyCompletionTraceTasteGate_single_carrier_alignment_decode_encode name]

private theorem CauchyCompletionTraceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyCompletionTraceUp} :
    cauchyCompletionTraceToEventFlow x = cauchyCompletionTraceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletionTraceFromEventFlow (cauchyCompletionTraceToEventFlow x) =
        cauchyCompletionTraceFromEventFlow (cauchyCompletionTraceToEventFlow y) :=
    congrArg cauchyCompletionTraceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyCompletionTraceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyCompletionTraceTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyCompletionTraceTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : CauchyCompletionTraceUp,
      cauchyCompletionTraceFields x = cauchyCompletionTraceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk source₁ sectionRow₁ replay₁ completion₁ boundary₁ transport₁ provenance₁ name₁ =>
      cases y with
      | mk source₂ sectionRow₂ replay₂ completion₂ boundary₂ transport₂ provenance₂ name₂ =>
          cases hfields
          rfl

instance cauchyCompletionTraceBHistCarrier : BHistCarrier CauchyCompletionTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionTraceToEventFlow
  fromEventFlow := cauchyCompletionTraceFromEventFlow

instance cauchyCompletionTraceChapterTasteGate :
    ChapterTasteGate CauchyCompletionTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyCompletionTraceFromEventFlow (cauchyCompletionTraceToEventFlow x) = some x
    exact CauchyCompletionTraceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyCompletionTraceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cauchyCompletionTraceFieldFaithful : FieldFaithful CauchyCompletionTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyCompletionTraceFields
  field_faithful := CauchyCompletionTraceTasteGate_single_carrier_alignment_fields_faithful

instance cauchyCompletionTraceNontrivial : Nontrivial CauchyCompletionTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyCompletionTraceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyCompletionTraceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyCompletionTraceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyCompletionTraceChapterTasteGate

theorem CauchyCompletionTraceTasteGate_single_carrier_alignment :
    ChapterTasteGate CauchyCompletionTraceUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact cauchyCompletionTraceChapterTasteGate

end BEDC.Derived.CauchyCompletionTraceUp
