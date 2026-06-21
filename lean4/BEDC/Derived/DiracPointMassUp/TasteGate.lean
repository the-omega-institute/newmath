import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DiracPointMassUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DiracPointMassUp : Type where
  | mk (source point event unit distribution transport replay provenance name : BHist) :
      DiracPointMassUp
  deriving DecidableEq

def diracPointMassEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: diracPointMassEncodeBHist h
  | BHist.e1 h => BMark.b1 :: diracPointMassEncodeBHist h

def diracPointMassDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (diracPointMassDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (diracPointMassDecodeBHist tail)

private theorem DiracPointMassTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, diracPointMassDecodeBHist (diracPointMassEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def diracPointMassFields : DiracPointMassUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DiracPointMassUp.mk source point event unit distribution transport replay provenance name =>
      [source, point, event, unit, distribution, transport, replay, provenance, name]

def diracPointMassToEventFlow : DiracPointMassUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (diracPointMassFields x).map diracPointMassEncodeBHist

private def diracPointMassEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => diracPointMassEventAt index rest

def diracPointMassFromEventFlow : EventFlow → Option DiracPointMassUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      some
        (DiracPointMassUp.mk
          (diracPointMassDecodeBHist (diracPointMassEventAt 0 flow))
          (diracPointMassDecodeBHist (diracPointMassEventAt 1 flow))
          (diracPointMassDecodeBHist (diracPointMassEventAt 2 flow))
          (diracPointMassDecodeBHist (diracPointMassEventAt 3 flow))
          (diracPointMassDecodeBHist (diracPointMassEventAt 4 flow))
          (diracPointMassDecodeBHist (diracPointMassEventAt 5 flow))
          (diracPointMassDecodeBHist (diracPointMassEventAt 6 flow))
          (diracPointMassDecodeBHist (diracPointMassEventAt 7 flow))
          (diracPointMassDecodeBHist (diracPointMassEventAt 8 flow)))

private theorem DiracPointMassTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DiracPointMassUp,
      diracPointMassFromEventFlow (diracPointMassToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source point event unit distribution transport replay provenance name =>
      change
        some
          (DiracPointMassUp.mk
            (diracPointMassDecodeBHist (diracPointMassEncodeBHist source))
            (diracPointMassDecodeBHist (diracPointMassEncodeBHist point))
            (diracPointMassDecodeBHist (diracPointMassEncodeBHist event))
            (diracPointMassDecodeBHist (diracPointMassEncodeBHist unit))
            (diracPointMassDecodeBHist (diracPointMassEncodeBHist distribution))
            (diracPointMassDecodeBHist (diracPointMassEncodeBHist transport))
            (diracPointMassDecodeBHist (diracPointMassEncodeBHist replay))
            (diracPointMassDecodeBHist (diracPointMassEncodeBHist provenance))
            (diracPointMassDecodeBHist (diracPointMassEncodeBHist name))) =
          some
            (DiracPointMassUp.mk source point event unit distribution transport replay
              provenance name)
      rw [DiracPointMassTasteGate_single_carrier_alignment_decode_encode source,
        DiracPointMassTasteGate_single_carrier_alignment_decode_encode point,
        DiracPointMassTasteGate_single_carrier_alignment_decode_encode event,
        DiracPointMassTasteGate_single_carrier_alignment_decode_encode unit,
        DiracPointMassTasteGate_single_carrier_alignment_decode_encode distribution,
        DiracPointMassTasteGate_single_carrier_alignment_decode_encode transport,
        DiracPointMassTasteGate_single_carrier_alignment_decode_encode replay,
        DiracPointMassTasteGate_single_carrier_alignment_decode_encode provenance,
        DiracPointMassTasteGate_single_carrier_alignment_decode_encode name]

private theorem DiracPointMassTasteGate_single_carrier_alignment_injective
    {x y : DiracPointMassUp} :
    diracPointMassToEventFlow x = diracPointMassToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      diracPointMassFromEventFlow (diracPointMassToEventFlow x) =
        diracPointMassFromEventFlow (diracPointMassToEventFlow y) :=
    congrArg diracPointMassFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DiracPointMassTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DiracPointMassTasteGate_single_carrier_alignment_round_trip y)))

private theorem DiracPointMassTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : DiracPointMassUp, diracPointMassFields x = diracPointMassFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk source point event unit distribution transport replay provenance name =>
      cases y with
      | mk source' point' event' unit' distribution' transport' replay' provenance' name' =>
          cases hfields
          rfl

instance diracPointMassBHistCarrier : BHistCarrier DiracPointMassUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := diracPointMassToEventFlow
  fromEventFlow := diracPointMassFromEventFlow

instance diracPointMassChapterTasteGate : ChapterTasteGate DiracPointMassUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change diracPointMassFromEventFlow (diracPointMassToEventFlow x) = some x
    exact DiracPointMassTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DiracPointMassTasteGate_single_carrier_alignment_injective heq)

instance diracPointMassFieldFaithful : FieldFaithful DiracPointMassUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := diracPointMassFields
  field_faithful := DiracPointMassTasteGate_single_carrier_alignment_fields_faithful

instance diracPointMassNontrivial : Nontrivial DiracPointMassUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DiracPointMassUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DiracPointMassUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DiracPointMassUp :=
  -- BEDC touchpoint anchor: BHist BMark
  diracPointMassChapterTasteGate

namespace TasteGate

theorem DiracPointMassTasteGate_single_carrier_alignment :
    (∀ h : BHist, diracPointMassDecodeBHist (diracPointMassEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier DiracPointMassUp) ∧
        Nonempty (ChapterTasteGate DiracPointMassUp) ∧
          diracPointMassEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  constructor
  · exact DiracPointMassTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact ⟨diracPointMassBHistCarrier⟩
    · constructor
      · exact ⟨diracPointMassChapterTasteGate⟩
      · rfl

end TasteGate

end BEDC.Derived.DiracPointMassUp
