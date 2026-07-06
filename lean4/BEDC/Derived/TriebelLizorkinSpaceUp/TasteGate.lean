import BEDC.Derived.TriebelLizorkinSpaceUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TriebelLizorkinSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def triebelLizorkinSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: triebelLizorkinSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: triebelLizorkinSpaceEncodeBHist h

def triebelLizorkinSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (triebelLizorkinSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (triebelLizorkinSpaceDecodeBHist tail)

private theorem triebelLizorkinSpace_decode_encode_bhist :
    ∀ h : BHist, triebelLizorkinSpaceDecodeBHist (triebelLizorkinSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def triebelLizorkinSpaceToEventFlow :
    _root_.BEDC.Derived.TriebelLizorkinSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | _root_.BEDC.Derived.TriebelLizorkinSpaceUp.mk
      sobolev holder weakDerivative dyadic regularRational realSeal windowSchedule
      localPosition mixedAggregation besovComparison transport replay provenance localName =>
      [triebelLizorkinSpaceEncodeBHist sobolev,
        triebelLizorkinSpaceEncodeBHist holder,
        triebelLizorkinSpaceEncodeBHist weakDerivative,
        triebelLizorkinSpaceEncodeBHist dyadic,
        triebelLizorkinSpaceEncodeBHist regularRational,
        triebelLizorkinSpaceEncodeBHist realSeal,
        triebelLizorkinSpaceEncodeBHist windowSchedule,
        triebelLizorkinSpaceEncodeBHist localPosition,
        triebelLizorkinSpaceEncodeBHist mixedAggregation,
        triebelLizorkinSpaceEncodeBHist besovComparison,
        triebelLizorkinSpaceEncodeBHist transport,
        triebelLizorkinSpaceEncodeBHist replay,
        triebelLizorkinSpaceEncodeBHist provenance,
        triebelLizorkinSpaceEncodeBHist localName]

private def triebelLizorkinSpaceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => triebelLizorkinSpaceEventAtDefault index rest

def triebelLizorkinSpaceFromEventFlow
    (ef : EventFlow) : Option _root_.BEDC.Derived.TriebelLizorkinSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (_root_.BEDC.Derived.TriebelLizorkinSpaceUp.mk
      (triebelLizorkinSpaceDecodeBHist (triebelLizorkinSpaceEventAtDefault 0 ef))
      (triebelLizorkinSpaceDecodeBHist (triebelLizorkinSpaceEventAtDefault 1 ef))
      (triebelLizorkinSpaceDecodeBHist (triebelLizorkinSpaceEventAtDefault 2 ef))
      (triebelLizorkinSpaceDecodeBHist (triebelLizorkinSpaceEventAtDefault 3 ef))
      (triebelLizorkinSpaceDecodeBHist (triebelLizorkinSpaceEventAtDefault 4 ef))
      (triebelLizorkinSpaceDecodeBHist (triebelLizorkinSpaceEventAtDefault 5 ef))
      (triebelLizorkinSpaceDecodeBHist (triebelLizorkinSpaceEventAtDefault 6 ef))
      (triebelLizorkinSpaceDecodeBHist (triebelLizorkinSpaceEventAtDefault 7 ef))
      (triebelLizorkinSpaceDecodeBHist (triebelLizorkinSpaceEventAtDefault 8 ef))
      (triebelLizorkinSpaceDecodeBHist (triebelLizorkinSpaceEventAtDefault 9 ef))
      (triebelLizorkinSpaceDecodeBHist (triebelLizorkinSpaceEventAtDefault 10 ef))
      (triebelLizorkinSpaceDecodeBHist (triebelLizorkinSpaceEventAtDefault 11 ef))
      (triebelLizorkinSpaceDecodeBHist (triebelLizorkinSpaceEventAtDefault 12 ef))
      (triebelLizorkinSpaceDecodeBHist (triebelLizorkinSpaceEventAtDefault 13 ef)))

private theorem triebelLizorkinSpace_round_trip :
    ∀ x : _root_.BEDC.Derived.TriebelLizorkinSpaceUp,
      triebelLizorkinSpaceFromEventFlow (triebelLizorkinSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk sobolev holder weakDerivative dyadic regularRational realSeal windowSchedule
      localPosition mixedAggregation besovComparison transport replay provenance localName =>
      change
        some
          (_root_.BEDC.Derived.TriebelLizorkinSpaceUp.mk
            (triebelLizorkinSpaceDecodeBHist (triebelLizorkinSpaceEncodeBHist sobolev))
            (triebelLizorkinSpaceDecodeBHist (triebelLizorkinSpaceEncodeBHist holder))
            (triebelLizorkinSpaceDecodeBHist
              (triebelLizorkinSpaceEncodeBHist weakDerivative))
            (triebelLizorkinSpaceDecodeBHist (triebelLizorkinSpaceEncodeBHist dyadic))
            (triebelLizorkinSpaceDecodeBHist
              (triebelLizorkinSpaceEncodeBHist regularRational))
            (triebelLizorkinSpaceDecodeBHist (triebelLizorkinSpaceEncodeBHist realSeal))
            (triebelLizorkinSpaceDecodeBHist
              (triebelLizorkinSpaceEncodeBHist windowSchedule))
            (triebelLizorkinSpaceDecodeBHist
              (triebelLizorkinSpaceEncodeBHist localPosition))
            (triebelLizorkinSpaceDecodeBHist
              (triebelLizorkinSpaceEncodeBHist mixedAggregation))
            (triebelLizorkinSpaceDecodeBHist
              (triebelLizorkinSpaceEncodeBHist besovComparison))
            (triebelLizorkinSpaceDecodeBHist (triebelLizorkinSpaceEncodeBHist transport))
            (triebelLizorkinSpaceDecodeBHist (triebelLizorkinSpaceEncodeBHist replay))
            (triebelLizorkinSpaceDecodeBHist (triebelLizorkinSpaceEncodeBHist provenance))
            (triebelLizorkinSpaceDecodeBHist (triebelLizorkinSpaceEncodeBHist localName))) =
          some
            (_root_.BEDC.Derived.TriebelLizorkinSpaceUp.mk
              sobolev holder weakDerivative dyadic regularRational realSeal windowSchedule
              localPosition mixedAggregation besovComparison transport replay provenance localName)
      rw [triebelLizorkinSpace_decode_encode_bhist sobolev,
        triebelLizorkinSpace_decode_encode_bhist holder,
        triebelLizorkinSpace_decode_encode_bhist weakDerivative,
        triebelLizorkinSpace_decode_encode_bhist dyadic,
        triebelLizorkinSpace_decode_encode_bhist regularRational,
        triebelLizorkinSpace_decode_encode_bhist realSeal,
        triebelLizorkinSpace_decode_encode_bhist windowSchedule,
        triebelLizorkinSpace_decode_encode_bhist localPosition,
        triebelLizorkinSpace_decode_encode_bhist mixedAggregation,
        triebelLizorkinSpace_decode_encode_bhist besovComparison,
        triebelLizorkinSpace_decode_encode_bhist transport,
        triebelLizorkinSpace_decode_encode_bhist replay,
        triebelLizorkinSpace_decode_encode_bhist provenance,
        triebelLizorkinSpace_decode_encode_bhist localName]

private theorem triebelLizorkinSpaceToEventFlow_injective
    {x y : _root_.BEDC.Derived.TriebelLizorkinSpaceUp} :
    triebelLizorkinSpaceToEventFlow x = triebelLizorkinSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      triebelLizorkinSpaceFromEventFlow (triebelLizorkinSpaceToEventFlow x) =
        triebelLizorkinSpaceFromEventFlow (triebelLizorkinSpaceToEventFlow y) :=
    congrArg triebelLizorkinSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (triebelLizorkinSpace_round_trip x).symm
      (Eq.trans hread (triebelLizorkinSpace_round_trip y)))

private def triebelLizorkinSpaceFields :
    _root_.BEDC.Derived.TriebelLizorkinSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | _root_.BEDC.Derived.TriebelLizorkinSpaceUp.mk
      sobolev holder weakDerivative dyadic regularRational realSeal windowSchedule
      localPosition mixedAggregation besovComparison transport replay provenance localName =>
      [sobolev, holder, weakDerivative, dyadic, regularRational, realSeal, windowSchedule,
        localPosition, mixedAggregation, besovComparison, transport, replay, provenance,
        localName]

private theorem triebelLizorkinSpace_field_faithful :
    ∀ x y : _root_.BEDC.Derived.TriebelLizorkinSpaceUp,
      triebelLizorkinSpaceFields x = triebelLizorkinSpaceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk sobolevA holderA weakDerivativeA dyadicA regularRationalA realSealA windowScheduleA
      localPositionA mixedAggregationA besovComparisonA transportA replayA provenanceA localNameA =>
      cases y with
      | mk sobolevB holderB weakDerivativeB dyadicB regularRationalB realSealB
          windowScheduleB localPositionB mixedAggregationB besovComparisonB transportB replayB
          provenanceB localNameB =>
          cases hfields
          rfl

instance triebelLizorkinSpaceBHistCarrier :
    BHistCarrier _root_.BEDC.Derived.TriebelLizorkinSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := triebelLizorkinSpaceToEventFlow
  fromEventFlow := triebelLizorkinSpaceFromEventFlow

instance triebelLizorkinSpaceChapterTasteGate :
    ChapterTasteGate _root_.BEDC.Derived.TriebelLizorkinSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change triebelLizorkinSpaceFromEventFlow (triebelLizorkinSpaceToEventFlow x) = some x
    exact triebelLizorkinSpace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (triebelLizorkinSpaceToEventFlow_injective heq)

instance triebelLizorkinSpaceFieldFaithful :
    FieldFaithful _root_.BEDC.Derived.TriebelLizorkinSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := triebelLizorkinSpaceFields
  field_faithful := triebelLizorkinSpace_field_faithful

instance triebelLizorkinSpaceNontrivial :
    Nontrivial _root_.BEDC.Derived.TriebelLizorkinSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨_root_.BEDC.Derived.TriebelLizorkinSpaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      _root_.BEDC.Derived.TriebelLizorkinSpaceUp.mk (BHist.e1 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem TriebelLizorkinSpaceTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate _root_.BEDC.Derived.TriebelLizorkinSpaceUp) ∧
      Nonempty (FieldFaithful _root_.BEDC.Derived.TriebelLizorkinSpaceUp) ∧
        Nonempty (Nontrivial _root_.BEDC.Derived.TriebelLizorkinSpaceUp) ∧
          (∀ h : BHist, triebelLizorkinSpaceDecodeBHist
            (triebelLizorkinSpaceEncodeBHist h) = h) ∧
            triebelLizorkinSpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨⟨triebelLizorkinSpaceChapterTasteGate⟩,
      ⟨triebelLizorkinSpaceFieldFaithful⟩,
      ⟨triebelLizorkinSpaceNontrivial⟩,
      triebelLizorkinSpace_decode_encode_bhist,
      rfl⟩

end BEDC.Derived.TriebelLizorkinSpaceUp
