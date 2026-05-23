import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ExtendedRealLineUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ExtendedRealLineUp : Type where
  | mk :
      (tag finiteReal lower upper positiveBound nonChoice transport replay provenance name : BHist) →
        ExtendedRealLineUp
  deriving DecidableEq

def extendedRealLineEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: extendedRealLineEncodeBHist h
  | BHist.e1 h => BMark.b1 :: extendedRealLineEncodeBHist h

def extendedRealLineDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (extendedRealLineDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (extendedRealLineDecodeBHist tail)

private theorem ExtendedRealLineTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, extendedRealLineDecodeBHist (extendedRealLineEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def extendedRealLineFields : ExtendedRealLineUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ExtendedRealLineUp.mk tag finiteReal lower upper positiveBound nonChoice transport replay
      provenance name =>
      [tag, finiteReal, lower, upper, positiveBound, nonChoice, transport, replay, provenance,
        name]

def extendedRealLineToEventFlow : ExtendedRealLineUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (extendedRealLineFields x).map extendedRealLineEncodeBHist

def extendedRealLineFromEventFlow : EventFlow → Option ExtendedRealLineUp
  -- BEDC touchpoint anchor: BHist BMark
  | [tag, finiteReal, lower, upper, positiveBound, nonChoice, transport, replay, provenance,
      name] =>
      some
        (ExtendedRealLineUp.mk
          (extendedRealLineDecodeBHist tag)
          (extendedRealLineDecodeBHist finiteReal)
          (extendedRealLineDecodeBHist lower)
          (extendedRealLineDecodeBHist upper)
          (extendedRealLineDecodeBHist positiveBound)
          (extendedRealLineDecodeBHist nonChoice)
          (extendedRealLineDecodeBHist transport)
          (extendedRealLineDecodeBHist replay)
          (extendedRealLineDecodeBHist provenance)
          (extendedRealLineDecodeBHist name))
  | _ => none

private theorem ExtendedRealLineTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ExtendedRealLineUp,
      extendedRealLineFromEventFlow (extendedRealLineToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk tag finiteReal lower upper positiveBound nonChoice transport replay provenance name =>
      change
        some
          (ExtendedRealLineUp.mk
            (extendedRealLineDecodeBHist (extendedRealLineEncodeBHist tag))
            (extendedRealLineDecodeBHist (extendedRealLineEncodeBHist finiteReal))
            (extendedRealLineDecodeBHist (extendedRealLineEncodeBHist lower))
            (extendedRealLineDecodeBHist (extendedRealLineEncodeBHist upper))
            (extendedRealLineDecodeBHist (extendedRealLineEncodeBHist positiveBound))
            (extendedRealLineDecodeBHist (extendedRealLineEncodeBHist nonChoice))
            (extendedRealLineDecodeBHist (extendedRealLineEncodeBHist transport))
            (extendedRealLineDecodeBHist (extendedRealLineEncodeBHist replay))
            (extendedRealLineDecodeBHist (extendedRealLineEncodeBHist provenance))
            (extendedRealLineDecodeBHist (extendedRealLineEncodeBHist name))) =
          some
            (ExtendedRealLineUp.mk tag finiteReal lower upper positiveBound nonChoice
              transport replay provenance name)
      rw [ExtendedRealLineTasteGate_single_carrier_alignment_decode_encode tag,
        ExtendedRealLineTasteGate_single_carrier_alignment_decode_encode finiteReal,
        ExtendedRealLineTasteGate_single_carrier_alignment_decode_encode lower,
        ExtendedRealLineTasteGate_single_carrier_alignment_decode_encode upper,
        ExtendedRealLineTasteGate_single_carrier_alignment_decode_encode positiveBound,
        ExtendedRealLineTasteGate_single_carrier_alignment_decode_encode nonChoice,
        ExtendedRealLineTasteGate_single_carrier_alignment_decode_encode transport,
        ExtendedRealLineTasteGate_single_carrier_alignment_decode_encode replay,
        ExtendedRealLineTasteGate_single_carrier_alignment_decode_encode provenance,
        ExtendedRealLineTasteGate_single_carrier_alignment_decode_encode name]

private theorem ExtendedRealLineTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ExtendedRealLineUp} :
    extendedRealLineToEventFlow x = extendedRealLineToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      extendedRealLineFromEventFlow (extendedRealLineToEventFlow x) =
        extendedRealLineFromEventFlow (extendedRealLineToEventFlow y) :=
    congrArg extendedRealLineFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ExtendedRealLineTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ExtendedRealLineTasteGate_single_carrier_alignment_round_trip y)))

private theorem ExtendedRealLineTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : ExtendedRealLineUp, extendedRealLineFields x = extendedRealLineFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk tag finiteReal lower upper positiveBound nonChoice transport replay provenance name =>
      cases y with
      | mk tag' finiteReal' lower' upper' positiveBound' nonChoice' transport' replay'
          provenance' name' =>
          cases hfields
          rfl

instance extendedRealLineBHistCarrier : BHistCarrier ExtendedRealLineUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := extendedRealLineToEventFlow
  fromEventFlow := extendedRealLineFromEventFlow

instance extendedRealLineChapterTasteGate : ChapterTasteGate ExtendedRealLineUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change extendedRealLineFromEventFlow (extendedRealLineToEventFlow x) = some x
    exact ExtendedRealLineTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ExtendedRealLineTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance extendedRealLineFieldFaithful : FieldFaithful ExtendedRealLineUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := extendedRealLineFields
  field_faithful := ExtendedRealLineTasteGate_single_carrier_alignment_fields_faithful

instance extendedRealLineNontrivial : Nontrivial ExtendedRealLineUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ExtendedRealLineUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ExtendedRealLineUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

theorem ExtendedRealLineTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ExtendedRealLineUp) ∧
      Nonempty (FieldFaithful ExtendedRealLineUp) ∧
        Nonempty (Nontrivial ExtendedRealLineUp) ∧
          (∀ h : BHist, extendedRealLineDecodeBHist (extendedRealLineEncodeBHist h) = h) ∧
            (∀ x : ExtendedRealLineUp,
              extendedRealLineFromEventFlow (extendedRealLineToEventFlow x) = some x) ∧
              extendedRealLineEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨extendedRealLineChapterTasteGate⟩, ⟨extendedRealLineFieldFaithful⟩,
      ⟨extendedRealLineNontrivial⟩,
      ExtendedRealLineTasteGate_single_carrier_alignment_decode_encode,
      ExtendedRealLineTasteGate_single_carrier_alignment_round_trip, rfl⟩

end BEDC.Derived.ExtendedRealLineUp
