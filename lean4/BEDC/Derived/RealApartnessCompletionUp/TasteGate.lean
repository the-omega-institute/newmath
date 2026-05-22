import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealApartnessCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealApartnessCompletionUp : Type where
  | mk (apartness located completion separation transport replay provenance name : BHist) :
      RealApartnessCompletionUp
  deriving DecidableEq

def realApartnessCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realApartnessCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realApartnessCompletionEncodeBHist h

def realApartnessCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realApartnessCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realApartnessCompletionDecodeBHist tail)

private theorem RealApartnessCompletionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      realApartnessCompletionDecodeBHist (realApartnessCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realApartnessCompletionFields : RealApartnessCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealApartnessCompletionUp.mk apartness located completion separation transport replay
      provenance name =>
      [apartness, located, completion, separation, transport, replay, provenance, name]

def realApartnessCompletionToEventFlow : RealApartnessCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realApartnessCompletionFields x).map realApartnessCompletionEncodeBHist

private def realApartnessCompletionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realApartnessCompletionEventAtDefault index rest

def realApartnessCompletionFromEventFlow : EventFlow → Option RealApartnessCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (RealApartnessCompletionUp.mk
        (realApartnessCompletionDecodeBHist (realApartnessCompletionEventAtDefault 0 ef))
        (realApartnessCompletionDecodeBHist (realApartnessCompletionEventAtDefault 1 ef))
        (realApartnessCompletionDecodeBHist (realApartnessCompletionEventAtDefault 2 ef))
        (realApartnessCompletionDecodeBHist (realApartnessCompletionEventAtDefault 3 ef))
        (realApartnessCompletionDecodeBHist (realApartnessCompletionEventAtDefault 4 ef))
        (realApartnessCompletionDecodeBHist (realApartnessCompletionEventAtDefault 5 ef))
        (realApartnessCompletionDecodeBHist (realApartnessCompletionEventAtDefault 6 ef))
        (realApartnessCompletionDecodeBHist (realApartnessCompletionEventAtDefault 7 ef)))

private theorem RealApartnessCompletionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RealApartnessCompletionUp,
      realApartnessCompletionFromEventFlow (realApartnessCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk apartness located completion separation transport replay provenance name =>
      change
        some
          (RealApartnessCompletionUp.mk
            (realApartnessCompletionDecodeBHist (realApartnessCompletionEncodeBHist apartness))
            (realApartnessCompletionDecodeBHist (realApartnessCompletionEncodeBHist located))
            (realApartnessCompletionDecodeBHist (realApartnessCompletionEncodeBHist completion))
            (realApartnessCompletionDecodeBHist (realApartnessCompletionEncodeBHist separation))
            (realApartnessCompletionDecodeBHist (realApartnessCompletionEncodeBHist transport))
            (realApartnessCompletionDecodeBHist (realApartnessCompletionEncodeBHist replay))
            (realApartnessCompletionDecodeBHist (realApartnessCompletionEncodeBHist provenance))
            (realApartnessCompletionDecodeBHist (realApartnessCompletionEncodeBHist name))) =
          some
            (RealApartnessCompletionUp.mk apartness located completion separation transport
              replay provenance name)
      rw [RealApartnessCompletionTasteGate_single_carrier_alignment_decode_encode apartness,
        RealApartnessCompletionTasteGate_single_carrier_alignment_decode_encode located,
        RealApartnessCompletionTasteGate_single_carrier_alignment_decode_encode completion,
        RealApartnessCompletionTasteGate_single_carrier_alignment_decode_encode separation,
        RealApartnessCompletionTasteGate_single_carrier_alignment_decode_encode transport,
        RealApartnessCompletionTasteGate_single_carrier_alignment_decode_encode replay,
        RealApartnessCompletionTasteGate_single_carrier_alignment_decode_encode provenance,
        RealApartnessCompletionTasteGate_single_carrier_alignment_decode_encode name]

private theorem RealApartnessCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealApartnessCompletionUp} :
    realApartnessCompletionToEventFlow x = realApartnessCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realApartnessCompletionFromEventFlow (realApartnessCompletionToEventFlow x) =
        realApartnessCompletionFromEventFlow (realApartnessCompletionToEventFlow y) :=
    congrArg realApartnessCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RealApartnessCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RealApartnessCompletionTasteGate_single_carrier_alignment_round_trip y)))

private theorem RealApartnessCompletionTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : RealApartnessCompletionUp,
      realApartnessCompletionFields x = realApartnessCompletionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk apartness₁ located₁ completion₁ separation₁ transport₁ replay₁ provenance₁ name₁ =>
      cases y with
      | mk apartness₂ located₂ completion₂ separation₂ transport₂ replay₂ provenance₂ name₂ =>
          cases hfields
          rfl

instance realApartnessCompletionBHistCarrier : BHistCarrier RealApartnessCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realApartnessCompletionToEventFlow
  fromEventFlow := realApartnessCompletionFromEventFlow

instance realApartnessCompletionChapterTasteGate :
    ChapterTasteGate RealApartnessCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realApartnessCompletionFromEventFlow (realApartnessCompletionToEventFlow x) = some x
    exact RealApartnessCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealApartnessCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance realApartnessCompletionFieldFaithful : FieldFaithful RealApartnessCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realApartnessCompletionFields
  field_faithful := RealApartnessCompletionTasteGate_single_carrier_alignment_fields_faithful

instance realApartnessCompletionNontrivial : Nontrivial RealApartnessCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealApartnessCompletionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealApartnessCompletionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealApartnessCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realApartnessCompletionChapterTasteGate

theorem RealApartnessCompletionTasteGate_single_carrier_alignment :
    ChapterTasteGate RealApartnessCompletionUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact realApartnessCompletionChapterTasteGate

end BEDC.Derived.RealApartnessCompletionUp
