import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ContourResidueHandoffUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ContourResidueHandoffUp : Type where
  | mk (G F O S Z B H C P N : BHist) : ContourResidueHandoffUp
  deriving DecidableEq

def contourResidueHandoffEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: contourResidueHandoffEncodeBHist h
  | BHist.e1 h => BMark.b1 :: contourResidueHandoffEncodeBHist h

def contourResidueHandoffDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (contourResidueHandoffDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (contourResidueHandoffDecodeBHist tail)

private theorem ContourResidueHandoffTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      contourResidueHandoffDecodeBHist (contourResidueHandoffEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def contourResidueHandoffFields : ContourResidueHandoffUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ContourResidueHandoffUp.mk G F O S Z B H C P N => [G, F, O, S, Z, B, H, C, P, N]

def contourResidueHandoffToEventFlow : ContourResidueHandoffUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (contourResidueHandoffFields x).map contourResidueHandoffEncodeBHist

private def contourResidueHandoffEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => contourResidueHandoffEventAt index rest

def contourResidueHandoffFromEventFlow
    (ef : EventFlow) : Option ContourResidueHandoffUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ContourResidueHandoffUp.mk
      (contourResidueHandoffDecodeBHist (contourResidueHandoffEventAt 0 ef))
      (contourResidueHandoffDecodeBHist (contourResidueHandoffEventAt 1 ef))
      (contourResidueHandoffDecodeBHist (contourResidueHandoffEventAt 2 ef))
      (contourResidueHandoffDecodeBHist (contourResidueHandoffEventAt 3 ef))
      (contourResidueHandoffDecodeBHist (contourResidueHandoffEventAt 4 ef))
      (contourResidueHandoffDecodeBHist (contourResidueHandoffEventAt 5 ef))
      (contourResidueHandoffDecodeBHist (contourResidueHandoffEventAt 6 ef))
      (contourResidueHandoffDecodeBHist (contourResidueHandoffEventAt 7 ef))
      (contourResidueHandoffDecodeBHist (contourResidueHandoffEventAt 8 ef))
      (contourResidueHandoffDecodeBHist (contourResidueHandoffEventAt 9 ef)))

private theorem ContourResidueHandoffTasteGate_single_carrier_alignment_round_trip
    (x : ContourResidueHandoffUp) :
    contourResidueHandoffFromEventFlow (contourResidueHandoffToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk G F O S Z B H C P N =>
      change
        some
          (ContourResidueHandoffUp.mk
            (contourResidueHandoffDecodeBHist (contourResidueHandoffEncodeBHist G))
            (contourResidueHandoffDecodeBHist (contourResidueHandoffEncodeBHist F))
            (contourResidueHandoffDecodeBHist (contourResidueHandoffEncodeBHist O))
            (contourResidueHandoffDecodeBHist (contourResidueHandoffEncodeBHist S))
            (contourResidueHandoffDecodeBHist (contourResidueHandoffEncodeBHist Z))
            (contourResidueHandoffDecodeBHist (contourResidueHandoffEncodeBHist B))
            (contourResidueHandoffDecodeBHist (contourResidueHandoffEncodeBHist H))
            (contourResidueHandoffDecodeBHist (contourResidueHandoffEncodeBHist C))
            (contourResidueHandoffDecodeBHist (contourResidueHandoffEncodeBHist P))
            (contourResidueHandoffDecodeBHist (contourResidueHandoffEncodeBHist N))) =
          some (ContourResidueHandoffUp.mk G F O S Z B H C P N)
      rw [ContourResidueHandoffTasteGate_single_carrier_alignment_decode_encode G,
        ContourResidueHandoffTasteGate_single_carrier_alignment_decode_encode F,
        ContourResidueHandoffTasteGate_single_carrier_alignment_decode_encode O,
        ContourResidueHandoffTasteGate_single_carrier_alignment_decode_encode S,
        ContourResidueHandoffTasteGate_single_carrier_alignment_decode_encode Z,
        ContourResidueHandoffTasteGate_single_carrier_alignment_decode_encode B,
        ContourResidueHandoffTasteGate_single_carrier_alignment_decode_encode H,
        ContourResidueHandoffTasteGate_single_carrier_alignment_decode_encode C,
        ContourResidueHandoffTasteGate_single_carrier_alignment_decode_encode P,
        ContourResidueHandoffTasteGate_single_carrier_alignment_decode_encode N]

private theorem ContourResidueHandoffTasteGate_single_carrier_alignment_injective
    {x y : ContourResidueHandoffUp} :
    contourResidueHandoffToEventFlow x = contourResidueHandoffToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      contourResidueHandoffFromEventFlow (contourResidueHandoffToEventFlow x) =
        contourResidueHandoffFromEventFlow (contourResidueHandoffToEventFlow y) :=
    congrArg contourResidueHandoffFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ContourResidueHandoffTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ContourResidueHandoffTasteGate_single_carrier_alignment_round_trip y)))

private theorem ContourResidueHandoffTasteGate_single_carrier_alignment_fields :
    ∀ x y : ContourResidueHandoffUp,
      contourResidueHandoffFields x = contourResidueHandoffFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk G₁ F₁ O₁ S₁ Z₁ B₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk G₂ F₂ O₂ S₂ Z₂ B₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance contourResidueHandoffBHistCarrier : BHistCarrier ContourResidueHandoffUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := contourResidueHandoffToEventFlow
  fromEventFlow := contourResidueHandoffFromEventFlow

instance contourResidueHandoffChapterTasteGate :
    ChapterTasteGate ContourResidueHandoffUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change contourResidueHandoffFromEventFlow (contourResidueHandoffToEventFlow x) =
      some x
    exact ContourResidueHandoffTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ContourResidueHandoffTasteGate_single_carrier_alignment_injective heq)

instance contourResidueHandoffFieldFaithful : FieldFaithful ContourResidueHandoffUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := contourResidueHandoffFields
  field_faithful := ContourResidueHandoffTasteGate_single_carrier_alignment_fields

instance contourResidueHandoffNontrivial :
    BEDC.Meta.TasteGate.Nontrivial ContourResidueHandoffUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ContourResidueHandoffUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ContourResidueHandoffUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def ContourResidueHandoffTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate ContourResidueHandoffUp :=
  -- BEDC touchpoint anchor: BHist BMark
  contourResidueHandoffChapterTasteGate

theorem ContourResidueHandoffTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      contourResidueHandoffDecodeBHist (contourResidueHandoffEncodeBHist h) = h) ∧
      (∀ x : ContourResidueHandoffUp,
        contourResidueHandoffFromEventFlow (contourResidueHandoffToEventFlow x) =
          some x) ∧
        (∀ x y : ContourResidueHandoffUp,
          contourResidueHandoffToEventFlow x = contourResidueHandoffToEventFlow y →
            x = y) ∧
          contourResidueHandoffEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact ContourResidueHandoffTasteGate_single_carrier_alignment_decode_encode
  constructor
  · exact ContourResidueHandoffTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact ContourResidueHandoffTasteGate_single_carrier_alignment_injective heq
  · rfl

end BEDC.Derived.ContourResidueHandoffUp
