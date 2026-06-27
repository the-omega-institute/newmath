import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICProofSearchFrontierUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICProofSearchFrontierUp : Type where
  | mk (critical discharge normalization bounded candidate evidence obstruction transport replay
      provenance namecert : BHist) : MetaCICProofSearchFrontierUp
  deriving DecidableEq

def metaCICProofSearchFrontierEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaCICProofSearchFrontierEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaCICProofSearchFrontierEncodeBHist h

def metaCICProofSearchFrontierDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaCICProofSearchFrontierDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaCICProofSearchFrontierDecodeBHist tail)

private theorem MetaCICProofSearchFrontierTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      metaCICProofSearchFrontierDecodeBHist
        (metaCICProofSearchFrontierEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metaCICProofSearchFrontierFields : MetaCICProofSearchFrontierUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICProofSearchFrontierUp.mk critical discharge normalization bounded candidate evidence
      obstruction transport replay provenance namecert =>
      [critical, discharge, normalization, bounded, candidate, evidence, obstruction,
        transport, replay, provenance, namecert]

def metaCICProofSearchFrontierToEventFlow :
    MetaCICProofSearchFrontierUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (metaCICProofSearchFrontierFields x).map metaCICProofSearchFrontierEncodeBHist

private def metaCICProofSearchFrontierEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => metaCICProofSearchFrontierEventAt index rest

def metaCICProofSearchFrontierFromEventFlow
    (ef : EventFlow) : Option MetaCICProofSearchFrontierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MetaCICProofSearchFrontierUp.mk
      (metaCICProofSearchFrontierDecodeBHist (metaCICProofSearchFrontierEventAt 0 ef))
      (metaCICProofSearchFrontierDecodeBHist (metaCICProofSearchFrontierEventAt 1 ef))
      (metaCICProofSearchFrontierDecodeBHist (metaCICProofSearchFrontierEventAt 2 ef))
      (metaCICProofSearchFrontierDecodeBHist (metaCICProofSearchFrontierEventAt 3 ef))
      (metaCICProofSearchFrontierDecodeBHist (metaCICProofSearchFrontierEventAt 4 ef))
      (metaCICProofSearchFrontierDecodeBHist (metaCICProofSearchFrontierEventAt 5 ef))
      (metaCICProofSearchFrontierDecodeBHist (metaCICProofSearchFrontierEventAt 6 ef))
      (metaCICProofSearchFrontierDecodeBHist (metaCICProofSearchFrontierEventAt 7 ef))
      (metaCICProofSearchFrontierDecodeBHist (metaCICProofSearchFrontierEventAt 8 ef))
      (metaCICProofSearchFrontierDecodeBHist (metaCICProofSearchFrontierEventAt 9 ef))
      (metaCICProofSearchFrontierDecodeBHist (metaCICProofSearchFrontierEventAt 10 ef)))

private theorem MetaCICProofSearchFrontierTasteGate_single_carrier_alignment_round_trip
    (x : MetaCICProofSearchFrontierUp) :
    metaCICProofSearchFrontierFromEventFlow
      (metaCICProofSearchFrontierToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk critical discharge normalization bounded candidate evidence obstruction transport replay
      provenance namecert =>
      change
        some
          (MetaCICProofSearchFrontierUp.mk
            (metaCICProofSearchFrontierDecodeBHist
              (metaCICProofSearchFrontierEncodeBHist critical))
            (metaCICProofSearchFrontierDecodeBHist
              (metaCICProofSearchFrontierEncodeBHist discharge))
            (metaCICProofSearchFrontierDecodeBHist
              (metaCICProofSearchFrontierEncodeBHist normalization))
            (metaCICProofSearchFrontierDecodeBHist
              (metaCICProofSearchFrontierEncodeBHist bounded))
            (metaCICProofSearchFrontierDecodeBHist
              (metaCICProofSearchFrontierEncodeBHist candidate))
            (metaCICProofSearchFrontierDecodeBHist
              (metaCICProofSearchFrontierEncodeBHist evidence))
            (metaCICProofSearchFrontierDecodeBHist
              (metaCICProofSearchFrontierEncodeBHist obstruction))
            (metaCICProofSearchFrontierDecodeBHist
              (metaCICProofSearchFrontierEncodeBHist transport))
            (metaCICProofSearchFrontierDecodeBHist
              (metaCICProofSearchFrontierEncodeBHist replay))
            (metaCICProofSearchFrontierDecodeBHist
              (metaCICProofSearchFrontierEncodeBHist provenance))
            (metaCICProofSearchFrontierDecodeBHist
              (metaCICProofSearchFrontierEncodeBHist namecert))) =
          some
            (MetaCICProofSearchFrontierUp.mk critical discharge normalization bounded
              candidate evidence obstruction transport replay provenance namecert)
      rw [MetaCICProofSearchFrontierTasteGate_single_carrier_alignment_decode_encode critical,
        MetaCICProofSearchFrontierTasteGate_single_carrier_alignment_decode_encode discharge,
        MetaCICProofSearchFrontierTasteGate_single_carrier_alignment_decode_encode normalization,
        MetaCICProofSearchFrontierTasteGate_single_carrier_alignment_decode_encode bounded,
        MetaCICProofSearchFrontierTasteGate_single_carrier_alignment_decode_encode candidate,
        MetaCICProofSearchFrontierTasteGate_single_carrier_alignment_decode_encode evidence,
        MetaCICProofSearchFrontierTasteGate_single_carrier_alignment_decode_encode obstruction,
        MetaCICProofSearchFrontierTasteGate_single_carrier_alignment_decode_encode transport,
        MetaCICProofSearchFrontierTasteGate_single_carrier_alignment_decode_encode replay,
        MetaCICProofSearchFrontierTasteGate_single_carrier_alignment_decode_encode provenance,
        MetaCICProofSearchFrontierTasteGate_single_carrier_alignment_decode_encode namecert]

private theorem MetaCICProofSearchFrontierTasteGate_single_carrier_alignment_injective
    {x y : MetaCICProofSearchFrontierUp} :
    metaCICProofSearchFrontierToEventFlow x =
      metaCICProofSearchFrontierToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaCICProofSearchFrontierFromEventFlow
          (metaCICProofSearchFrontierToEventFlow x) =
        metaCICProofSearchFrontierFromEventFlow
          (metaCICProofSearchFrontierToEventFlow y) :=
    congrArg metaCICProofSearchFrontierFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (MetaCICProofSearchFrontierTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (MetaCICProofSearchFrontierTasteGate_single_carrier_alignment_round_trip y)))

private theorem MetaCICProofSearchFrontierTasteGate_single_carrier_alignment_fields :
    forall x y : MetaCICProofSearchFrontierUp,
      metaCICProofSearchFrontierFields x = metaCICProofSearchFrontierFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk critical₁ discharge₁ normalization₁ bounded₁ candidate₁ evidence₁ obstruction₁ transport₁ replay₁ provenance₁ namecert₁ =>
      cases y with
      | mk critical₂ discharge₂ normalization₂ bounded₂ candidate₂ evidence₂ obstruction₂ transport₂ replay₂ provenance₂ namecert₂ =>
          cases hfields
          rfl

instance metaCICProofSearchFrontierBHistCarrier :
    BHistCarrier MetaCICProofSearchFrontierUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaCICProofSearchFrontierToEventFlow
  fromEventFlow := metaCICProofSearchFrontierFromEventFlow

instance metaCICProofSearchFrontierChapterTasteGate :
    ChapterTasteGate MetaCICProofSearchFrontierUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metaCICProofSearchFrontierFromEventFlow
        (metaCICProofSearchFrontierToEventFlow x) = some x
    exact MetaCICProofSearchFrontierTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MetaCICProofSearchFrontierTasteGate_single_carrier_alignment_injective heq)

instance metaCICProofSearchFrontierFieldFaithful :
    FieldFaithful MetaCICProofSearchFrontierUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metaCICProofSearchFrontierFields
  field_faithful := MetaCICProofSearchFrontierTasteGate_single_carrier_alignment_fields

instance metaCICProofSearchFrontierNontrivial :
    BEDC.Meta.TasteGate.Nontrivial MetaCICProofSearchFrontierUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetaCICProofSearchFrontierUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MetaCICProofSearchFrontierUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def MetaCICProofSearchFrontierTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate MetaCICProofSearchFrontierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metaCICProofSearchFrontierChapterTasteGate

theorem MetaCICProofSearchFrontierTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      metaCICProofSearchFrontierDecodeBHist
        (metaCICProofSearchFrontierEncodeBHist h) = h) ∧
      (∀ x : MetaCICProofSearchFrontierUp,
        metaCICProofSearchFrontierFromEventFlow
          (metaCICProofSearchFrontierToEventFlow x) = some x) ∧
        (∀ x y : MetaCICProofSearchFrontierUp,
          metaCICProofSearchFrontierToEventFlow x =
            metaCICProofSearchFrontierToEventFlow y → x = y) ∧
          metaCICProofSearchFrontierEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact MetaCICProofSearchFrontierTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact MetaCICProofSearchFrontierTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact MetaCICProofSearchFrontierTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.MetaCICProofSearchFrontierUp
