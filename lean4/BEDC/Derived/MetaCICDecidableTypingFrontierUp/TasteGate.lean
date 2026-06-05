import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICDecidableTypingFrontierUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICDecidableTypingFrontierUp : Type where
  | mk
      (infer same structural bounded refusal transport replay provenance name : BHist) :
      MetaCICDecidableTypingFrontierUp
  deriving DecidableEq

def metacicDecidableTypingFrontierEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metacicDecidableTypingFrontierEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metacicDecidableTypingFrontierEncodeBHist h

def metacicDecidableTypingFrontierDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metacicDecidableTypingFrontierDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metacicDecidableTypingFrontierDecodeBHist tail)

private theorem MetaCICDecidableTypingFrontierTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      metacicDecidableTypingFrontierDecodeBHist
        (metacicDecidableTypingFrontierEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metacicDecidableTypingFrontierFields :
    MetaCICDecidableTypingFrontierUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICDecidableTypingFrontierUp.mk infer same structural bounded refusal transport
      replay provenance name =>
      [infer, same, structural, bounded, refusal, transport, replay, provenance, name]

def metacicDecidableTypingFrontierToEventFlow :
    MetaCICDecidableTypingFrontierUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (metacicDecidableTypingFrontierFields x).map
      metacicDecidableTypingFrontierEncodeBHist

private def metacicDecidableTypingFrontierEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      metacicDecidableTypingFrontierEventAtDefault index rest

def metacicDecidableTypingFrontierFromEventFlow
    (ef : EventFlow) : Option MetaCICDecidableTypingFrontierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MetaCICDecidableTypingFrontierUp.mk
      (metacicDecidableTypingFrontierDecodeBHist
        (metacicDecidableTypingFrontierEventAtDefault 0 ef))
      (metacicDecidableTypingFrontierDecodeBHist
        (metacicDecidableTypingFrontierEventAtDefault 1 ef))
      (metacicDecidableTypingFrontierDecodeBHist
        (metacicDecidableTypingFrontierEventAtDefault 2 ef))
      (metacicDecidableTypingFrontierDecodeBHist
        (metacicDecidableTypingFrontierEventAtDefault 3 ef))
      (metacicDecidableTypingFrontierDecodeBHist
        (metacicDecidableTypingFrontierEventAtDefault 4 ef))
      (metacicDecidableTypingFrontierDecodeBHist
        (metacicDecidableTypingFrontierEventAtDefault 5 ef))
      (metacicDecidableTypingFrontierDecodeBHist
        (metacicDecidableTypingFrontierEventAtDefault 6 ef))
      (metacicDecidableTypingFrontierDecodeBHist
        (metacicDecidableTypingFrontierEventAtDefault 7 ef))
      (metacicDecidableTypingFrontierDecodeBHist
        (metacicDecidableTypingFrontierEventAtDefault 8 ef)))

private theorem MetaCICDecidableTypingFrontierTasteGate_single_carrier_alignment_round_trip
    (x : MetaCICDecidableTypingFrontierUp) :
    metacicDecidableTypingFrontierFromEventFlow
      (metacicDecidableTypingFrontierToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk infer same structural bounded refusal transport replay provenance name =>
      change
        some
          (MetaCICDecidableTypingFrontierUp.mk
            (metacicDecidableTypingFrontierDecodeBHist
              (metacicDecidableTypingFrontierEncodeBHist infer))
            (metacicDecidableTypingFrontierDecodeBHist
              (metacicDecidableTypingFrontierEncodeBHist same))
            (metacicDecidableTypingFrontierDecodeBHist
              (metacicDecidableTypingFrontierEncodeBHist structural))
            (metacicDecidableTypingFrontierDecodeBHist
              (metacicDecidableTypingFrontierEncodeBHist bounded))
            (metacicDecidableTypingFrontierDecodeBHist
              (metacicDecidableTypingFrontierEncodeBHist refusal))
            (metacicDecidableTypingFrontierDecodeBHist
              (metacicDecidableTypingFrontierEncodeBHist transport))
            (metacicDecidableTypingFrontierDecodeBHist
              (metacicDecidableTypingFrontierEncodeBHist replay))
            (metacicDecidableTypingFrontierDecodeBHist
              (metacicDecidableTypingFrontierEncodeBHist provenance))
            (metacicDecidableTypingFrontierDecodeBHist
              (metacicDecidableTypingFrontierEncodeBHist name))) =
          some
            (MetaCICDecidableTypingFrontierUp.mk infer same structural bounded refusal
              transport replay provenance name)
      rw [MetaCICDecidableTypingFrontierTasteGate_single_carrier_alignment_decode_encode infer,
        MetaCICDecidableTypingFrontierTasteGate_single_carrier_alignment_decode_encode same,
        MetaCICDecidableTypingFrontierTasteGate_single_carrier_alignment_decode_encode structural,
        MetaCICDecidableTypingFrontierTasteGate_single_carrier_alignment_decode_encode bounded,
        MetaCICDecidableTypingFrontierTasteGate_single_carrier_alignment_decode_encode refusal,
        MetaCICDecidableTypingFrontierTasteGate_single_carrier_alignment_decode_encode transport,
        MetaCICDecidableTypingFrontierTasteGate_single_carrier_alignment_decode_encode replay,
        MetaCICDecidableTypingFrontierTasteGate_single_carrier_alignment_decode_encode provenance,
        MetaCICDecidableTypingFrontierTasteGate_single_carrier_alignment_decode_encode name]

private theorem MetaCICDecidableTypingFrontierTasteGate_single_carrier_alignment_injective
    {x y : MetaCICDecidableTypingFrontierUp} :
    metacicDecidableTypingFrontierToEventFlow x =
      metacicDecidableTypingFrontierToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metacicDecidableTypingFrontierFromEventFlow
          (metacicDecidableTypingFrontierToEventFlow x) =
        metacicDecidableTypingFrontierFromEventFlow
          (metacicDecidableTypingFrontierToEventFlow y) :=
    congrArg metacicDecidableTypingFrontierFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (MetaCICDecidableTypingFrontierTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (MetaCICDecidableTypingFrontierTasteGate_single_carrier_alignment_round_trip y)))

private theorem MetaCICDecidableTypingFrontierTasteGate_single_carrier_alignment_fields :
    ∀ x y : MetaCICDecidableTypingFrontierUp,
      metacicDecidableTypingFrontierFields x =
        metacicDecidableTypingFrontierFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk infer₁ same₁ structural₁ bounded₁ refusal₁ transport₁ replay₁ provenance₁ name₁ =>
      cases y with
      | mk infer₂ same₂ structural₂ bounded₂ refusal₂ transport₂ replay₂ provenance₂ name₂ =>
          cases hfields
          rfl

instance metacicDecidableTypingFrontierBHistCarrier :
    BHistCarrier MetaCICDecidableTypingFrontierUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metacicDecidableTypingFrontierToEventFlow
  fromEventFlow := metacicDecidableTypingFrontierFromEventFlow

instance metacicDecidableTypingFrontierChapterTasteGate :
    ChapterTasteGate MetaCICDecidableTypingFrontierUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metacicDecidableTypingFrontierFromEventFlow
        (metacicDecidableTypingFrontierToEventFlow x) = some x
    exact MetaCICDecidableTypingFrontierTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (MetaCICDecidableTypingFrontierTasteGate_single_carrier_alignment_injective heq)

instance metacicDecidableTypingFrontierFieldFaithful :
    FieldFaithful MetaCICDecidableTypingFrontierUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metacicDecidableTypingFrontierFields
  field_faithful :=
    MetaCICDecidableTypingFrontierTasteGate_single_carrier_alignment_fields

instance metacicDecidableTypingFrontierNontrivial :
    BEDC.Meta.TasteGate.Nontrivial MetaCICDecidableTypingFrontierUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetaCICDecidableTypingFrontierUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MetaCICDecidableTypingFrontierUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def MetaCICDecidableTypingFrontierTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate MetaCICDecidableTypingFrontierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metacicDecidableTypingFrontierChapterTasteGate

theorem MetaCICDecidableTypingFrontierTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      metacicDecidableTypingFrontierDecodeBHist
        (metacicDecidableTypingFrontierEncodeBHist h) = h) ∧
      (∀ x : MetaCICDecidableTypingFrontierUp,
        metacicDecidableTypingFrontierFromEventFlow
          (metacicDecidableTypingFrontierToEventFlow x) = some x) ∧
        (∀ x y : MetaCICDecidableTypingFrontierUp,
          metacicDecidableTypingFrontierToEventFlow x =
            metacicDecidableTypingFrontierToEventFlow y → x = y) ∧
          metacicDecidableTypingFrontierEncodeBHist BHist.Empty =
            ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact MetaCICDecidableTypingFrontierTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact MetaCICDecidableTypingFrontierTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact MetaCICDecidableTypingFrontierTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.MetaCICDecidableTypingFrontierUp
