import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICNormalEndpointCutUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICNormalEndpointCutUp : Type where
  | mk (typed candidate bounded finished obstruction discharge transport replay provenance namecert :
      BHist) : MetaCICNormalEndpointCutUp
  deriving DecidableEq

def metaCICNormalEndpointCutEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaCICNormalEndpointCutEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaCICNormalEndpointCutEncodeBHist h

def metaCICNormalEndpointCutDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaCICNormalEndpointCutDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaCICNormalEndpointCutDecodeBHist tail)

private theorem MetaCICNormalEndpointCutTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      metaCICNormalEndpointCutDecodeBHist
        (metaCICNormalEndpointCutEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metaCICNormalEndpointCutFields : MetaCICNormalEndpointCutUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICNormalEndpointCutUp.mk typed candidate bounded finished obstruction discharge
      transport replay provenance namecert =>
      [typed, candidate, bounded, finished, obstruction, discharge, transport, replay,
        provenance, namecert]

def metaCICNormalEndpointCutToEventFlow : MetaCICNormalEndpointCutUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (metaCICNormalEndpointCutFields x).map metaCICNormalEndpointCutEncodeBHist

private def metaCICNormalEndpointCutEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => metaCICNormalEndpointCutEventAt index rest

def metaCICNormalEndpointCutFromEventFlow
    (ef : EventFlow) : Option MetaCICNormalEndpointCutUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MetaCICNormalEndpointCutUp.mk
      (metaCICNormalEndpointCutDecodeBHist (metaCICNormalEndpointCutEventAt 0 ef))
      (metaCICNormalEndpointCutDecodeBHist (metaCICNormalEndpointCutEventAt 1 ef))
      (metaCICNormalEndpointCutDecodeBHist (metaCICNormalEndpointCutEventAt 2 ef))
      (metaCICNormalEndpointCutDecodeBHist (metaCICNormalEndpointCutEventAt 3 ef))
      (metaCICNormalEndpointCutDecodeBHist (metaCICNormalEndpointCutEventAt 4 ef))
      (metaCICNormalEndpointCutDecodeBHist (metaCICNormalEndpointCutEventAt 5 ef))
      (metaCICNormalEndpointCutDecodeBHist (metaCICNormalEndpointCutEventAt 6 ef))
      (metaCICNormalEndpointCutDecodeBHist (metaCICNormalEndpointCutEventAt 7 ef))
      (metaCICNormalEndpointCutDecodeBHist (metaCICNormalEndpointCutEventAt 8 ef))
      (metaCICNormalEndpointCutDecodeBHist (metaCICNormalEndpointCutEventAt 9 ef)))

private theorem MetaCICNormalEndpointCutTasteGate_single_carrier_alignment_round_trip
    (x : MetaCICNormalEndpointCutUp) :
    metaCICNormalEndpointCutFromEventFlow
      (metaCICNormalEndpointCutToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk typed candidate bounded finished obstruction discharge transport replay provenance namecert =>
      change
        some
          (MetaCICNormalEndpointCutUp.mk
            (metaCICNormalEndpointCutDecodeBHist (metaCICNormalEndpointCutEncodeBHist typed))
            (metaCICNormalEndpointCutDecodeBHist
              (metaCICNormalEndpointCutEncodeBHist candidate))
            (metaCICNormalEndpointCutDecodeBHist (metaCICNormalEndpointCutEncodeBHist bounded))
            (metaCICNormalEndpointCutDecodeBHist
              (metaCICNormalEndpointCutEncodeBHist finished))
            (metaCICNormalEndpointCutDecodeBHist
              (metaCICNormalEndpointCutEncodeBHist obstruction))
            (metaCICNormalEndpointCutDecodeBHist
              (metaCICNormalEndpointCutEncodeBHist discharge))
            (metaCICNormalEndpointCutDecodeBHist
              (metaCICNormalEndpointCutEncodeBHist transport))
            (metaCICNormalEndpointCutDecodeBHist (metaCICNormalEndpointCutEncodeBHist replay))
            (metaCICNormalEndpointCutDecodeBHist
              (metaCICNormalEndpointCutEncodeBHist provenance))
            (metaCICNormalEndpointCutDecodeBHist (metaCICNormalEndpointCutEncodeBHist namecert))) =
          some
            (MetaCICNormalEndpointCutUp.mk typed candidate bounded finished obstruction
              discharge transport replay provenance namecert)
      rw [MetaCICNormalEndpointCutTasteGate_single_carrier_alignment_decode_encode typed,
        MetaCICNormalEndpointCutTasteGate_single_carrier_alignment_decode_encode candidate,
        MetaCICNormalEndpointCutTasteGate_single_carrier_alignment_decode_encode bounded,
        MetaCICNormalEndpointCutTasteGate_single_carrier_alignment_decode_encode finished,
        MetaCICNormalEndpointCutTasteGate_single_carrier_alignment_decode_encode obstruction,
        MetaCICNormalEndpointCutTasteGate_single_carrier_alignment_decode_encode discharge,
        MetaCICNormalEndpointCutTasteGate_single_carrier_alignment_decode_encode transport,
        MetaCICNormalEndpointCutTasteGate_single_carrier_alignment_decode_encode replay,
        MetaCICNormalEndpointCutTasteGate_single_carrier_alignment_decode_encode provenance,
        MetaCICNormalEndpointCutTasteGate_single_carrier_alignment_decode_encode namecert]

private theorem MetaCICNormalEndpointCutTasteGate_single_carrier_alignment_injective
    {x y : MetaCICNormalEndpointCutUp} :
    metaCICNormalEndpointCutToEventFlow x =
      metaCICNormalEndpointCutToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaCICNormalEndpointCutFromEventFlow (metaCICNormalEndpointCutToEventFlow x) =
        metaCICNormalEndpointCutFromEventFlow (metaCICNormalEndpointCutToEventFlow y) :=
    congrArg metaCICNormalEndpointCutFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (MetaCICNormalEndpointCutTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (MetaCICNormalEndpointCutTasteGate_single_carrier_alignment_round_trip y)))

private theorem MetaCICNormalEndpointCutTasteGate_single_carrier_alignment_fields :
    forall x y : MetaCICNormalEndpointCutUp,
      metaCICNormalEndpointCutFields x = metaCICNormalEndpointCutFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk typed₁ candidate₁ bounded₁ finished₁ obstruction₁ discharge₁ transport₁ replay₁ provenance₁ namecert₁ =>
      cases y with
      | mk typed₂ candidate₂ bounded₂ finished₂ obstruction₂ discharge₂ transport₂ replay₂ provenance₂ namecert₂ =>
          cases hfields
          rfl

instance metaCICNormalEndpointCutBHistCarrier : BHistCarrier MetaCICNormalEndpointCutUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaCICNormalEndpointCutToEventFlow
  fromEventFlow := metaCICNormalEndpointCutFromEventFlow

instance metaCICNormalEndpointCutChapterTasteGate :
    ChapterTasteGate MetaCICNormalEndpointCutUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metaCICNormalEndpointCutFromEventFlow
        (metaCICNormalEndpointCutToEventFlow x) = some x
    exact MetaCICNormalEndpointCutTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MetaCICNormalEndpointCutTasteGate_single_carrier_alignment_injective heq)

instance metaCICNormalEndpointCutFieldFaithful :
    FieldFaithful MetaCICNormalEndpointCutUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metaCICNormalEndpointCutFields
  field_faithful := MetaCICNormalEndpointCutTasteGate_single_carrier_alignment_fields

instance metaCICNormalEndpointCutNontrivial :
    BEDC.Meta.TasteGate.Nontrivial MetaCICNormalEndpointCutUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetaCICNormalEndpointCutUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MetaCICNormalEndpointCutUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def MetaCICNormalEndpointCutTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate MetaCICNormalEndpointCutUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metaCICNormalEndpointCutChapterTasteGate

theorem MetaCICNormalEndpointCutTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      metaCICNormalEndpointCutDecodeBHist
        (metaCICNormalEndpointCutEncodeBHist h) = h) ∧
      (∀ x : MetaCICNormalEndpointCutUp,
        metaCICNormalEndpointCutFromEventFlow
          (metaCICNormalEndpointCutToEventFlow x) = some x) ∧
        (∀ x y : MetaCICNormalEndpointCutUp,
          metaCICNormalEndpointCutToEventFlow x =
            metaCICNormalEndpointCutToEventFlow y → x = y) ∧
          metaCICNormalEndpointCutEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact MetaCICNormalEndpointCutTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact MetaCICNormalEndpointCutTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact MetaCICNormalEndpointCutTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.MetaCICNormalEndpointCutUp
