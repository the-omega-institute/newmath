import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICDecidableNeutralSpineUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICDecidableNeutralSpineUp : Type where
  | mk :
      (typing sameTerm boundedComparison boundary refusal transport replay provenance
        name : BHist) ->
      MetaCICDecidableNeutralSpineUp
  deriving DecidableEq

def metacicDecidableNeutralSpineEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metacicDecidableNeutralSpineEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metacicDecidableNeutralSpineEncodeBHist h

def metacicDecidableNeutralSpineDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metacicDecidableNeutralSpineDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metacicDecidableNeutralSpineDecodeBHist tail)

private theorem metacicDecidableNeutralSpineDecode_encode_bhist :
    forall h : BHist,
      metacicDecidableNeutralSpineDecodeBHist
        (metacicDecidableNeutralSpineEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def metacicDecidableNeutralSpineToEventFlow :
    MetaCICDecidableNeutralSpineUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICDecidableNeutralSpineUp.mk typing sameTerm boundedComparison boundary refusal
      transport replay provenance name =>
      [[BMark.b0],
        metacicDecidableNeutralSpineEncodeBHist typing,
        [BMark.b1, BMark.b0],
        metacicDecidableNeutralSpineEncodeBHist sameTerm,
        [BMark.b1, BMark.b1, BMark.b0],
        metacicDecidableNeutralSpineEncodeBHist boundedComparison,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metacicDecidableNeutralSpineEncodeBHist boundary,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metacicDecidableNeutralSpineEncodeBHist refusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metacicDecidableNeutralSpineEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metacicDecidableNeutralSpineEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        metacicDecidableNeutralSpineEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        metacicDecidableNeutralSpineEncodeBHist name]

private def metacicDecidableNeutralSpineEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      metacicDecidableNeutralSpineEventAtDefault index rest

def metacicDecidableNeutralSpineFromEventFlow
    (ef : EventFlow) : Option MetaCICDecidableNeutralSpineUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MetaCICDecidableNeutralSpineUp.mk
      (metacicDecidableNeutralSpineDecodeBHist
        (metacicDecidableNeutralSpineEventAtDefault 1 ef))
      (metacicDecidableNeutralSpineDecodeBHist
        (metacicDecidableNeutralSpineEventAtDefault 3 ef))
      (metacicDecidableNeutralSpineDecodeBHist
        (metacicDecidableNeutralSpineEventAtDefault 5 ef))
      (metacicDecidableNeutralSpineDecodeBHist
        (metacicDecidableNeutralSpineEventAtDefault 7 ef))
      (metacicDecidableNeutralSpineDecodeBHist
        (metacicDecidableNeutralSpineEventAtDefault 9 ef))
      (metacicDecidableNeutralSpineDecodeBHist
        (metacicDecidableNeutralSpineEventAtDefault 11 ef))
      (metacicDecidableNeutralSpineDecodeBHist
        (metacicDecidableNeutralSpineEventAtDefault 13 ef))
      (metacicDecidableNeutralSpineDecodeBHist
        (metacicDecidableNeutralSpineEventAtDefault 15 ef))
      (metacicDecidableNeutralSpineDecodeBHist
        (metacicDecidableNeutralSpineEventAtDefault 17 ef)))

private theorem metacicDecidableNeutralSpine_round_trip :
    forall x : MetaCICDecidableNeutralSpineUp,
      metacicDecidableNeutralSpineFromEventFlow
        (metacicDecidableNeutralSpineToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk typing sameTerm boundedComparison boundary refusal transport replay provenance name =>
      change
        some
          (MetaCICDecidableNeutralSpineUp.mk
            (metacicDecidableNeutralSpineDecodeBHist
              (metacicDecidableNeutralSpineEncodeBHist typing))
            (metacicDecidableNeutralSpineDecodeBHist
              (metacicDecidableNeutralSpineEncodeBHist sameTerm))
            (metacicDecidableNeutralSpineDecodeBHist
              (metacicDecidableNeutralSpineEncodeBHist boundedComparison))
            (metacicDecidableNeutralSpineDecodeBHist
              (metacicDecidableNeutralSpineEncodeBHist boundary))
            (metacicDecidableNeutralSpineDecodeBHist
              (metacicDecidableNeutralSpineEncodeBHist refusal))
            (metacicDecidableNeutralSpineDecodeBHist
              (metacicDecidableNeutralSpineEncodeBHist transport))
            (metacicDecidableNeutralSpineDecodeBHist
              (metacicDecidableNeutralSpineEncodeBHist replay))
            (metacicDecidableNeutralSpineDecodeBHist
              (metacicDecidableNeutralSpineEncodeBHist provenance))
            (metacicDecidableNeutralSpineDecodeBHist
              (metacicDecidableNeutralSpineEncodeBHist name))) =
          some
            (MetaCICDecidableNeutralSpineUp.mk typing sameTerm boundedComparison boundary
              refusal transport replay provenance name)
      rw [metacicDecidableNeutralSpineDecode_encode_bhist typing,
        metacicDecidableNeutralSpineDecode_encode_bhist sameTerm,
        metacicDecidableNeutralSpineDecode_encode_bhist boundedComparison,
        metacicDecidableNeutralSpineDecode_encode_bhist boundary,
        metacicDecidableNeutralSpineDecode_encode_bhist refusal,
        metacicDecidableNeutralSpineDecode_encode_bhist transport,
        metacicDecidableNeutralSpineDecode_encode_bhist replay,
        metacicDecidableNeutralSpineDecode_encode_bhist provenance,
        metacicDecidableNeutralSpineDecode_encode_bhist name]

private theorem metacicDecidableNeutralSpineToEventFlow_injective
    {x y : MetaCICDecidableNeutralSpineUp} :
    metacicDecidableNeutralSpineToEventFlow x =
      metacicDecidableNeutralSpineToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metacicDecidableNeutralSpineFromEventFlow
          (metacicDecidableNeutralSpineToEventFlow x) =
        metacicDecidableNeutralSpineFromEventFlow
          (metacicDecidableNeutralSpineToEventFlow y) :=
    congrArg metacicDecidableNeutralSpineFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metacicDecidableNeutralSpine_round_trip x).symm
      (Eq.trans hread (metacicDecidableNeutralSpine_round_trip y)))

def metacicDecidableNeutralSpineFields :
    MetaCICDecidableNeutralSpineUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICDecidableNeutralSpineUp.mk typing sameTerm boundedComparison boundary refusal
      transport replay provenance name =>
      [typing, sameTerm, boundedComparison, boundary, refusal, transport, replay,
        provenance, name]

private theorem metacicDecidableNeutralSpine_fields_faithful :
    forall x y : MetaCICDecidableNeutralSpineUp,
      metacicDecidableNeutralSpineFields x =
        metacicDecidableNeutralSpineFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk typing sameTerm boundedComparison boundary refusal transport replay provenance name =>
      cases y with
      | mk typing' sameTerm' boundedComparison' boundary' refusal' transport' replay'
          provenance' name' =>
          injection hfields with hTyping hRest1
          injection hRest1 with hSameTerm hRest2
          injection hRest2 with hBoundedComparison hRest3
          injection hRest3 with hBoundary hRest4
          injection hRest4 with hRefusal hRest5
          injection hRest5 with hTransport hRest6
          injection hRest6 with hReplay hRest7
          injection hRest7 with hProvenance hRest8
          injection hRest8 with hName _
          subst hTyping
          subst hSameTerm
          subst hBoundedComparison
          subst hBoundary
          subst hRefusal
          subst hTransport
          subst hReplay
          subst hProvenance
          subst hName
          rfl

instance metacicDecidableNeutralSpineBHistCarrier :
    BHistCarrier MetaCICDecidableNeutralSpineUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metacicDecidableNeutralSpineToEventFlow
  fromEventFlow := metacicDecidableNeutralSpineFromEventFlow

instance metacicDecidableNeutralSpineChapterTasteGate :
    ChapterTasteGate MetaCICDecidableNeutralSpineUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metacicDecidableNeutralSpineFromEventFlow
        (metacicDecidableNeutralSpineToEventFlow x) = some x
    exact metacicDecidableNeutralSpine_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metacicDecidableNeutralSpineToEventFlow_injective heq)

instance metacicDecidableNeutralSpineFieldFaithful :
    FieldFaithful MetaCICDecidableNeutralSpineUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metacicDecidableNeutralSpineFields
  field_faithful := metacicDecidableNeutralSpine_fields_faithful

instance metacicDecidableNeutralSpineNontrivial :
    Nontrivial MetaCICDecidableNeutralSpineUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetaCICDecidableNeutralSpineUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MetaCICDecidableNeutralSpineUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem MetaCICDecidableNeutralSpineTasteGate_single_carrier_alignment :
    (forall h : BHist,
      metacicDecidableNeutralSpineDecodeBHist
        (metacicDecidableNeutralSpineEncodeBHist h) = h) /\
      (forall x : MetaCICDecidableNeutralSpineUp,
        metacicDecidableNeutralSpineFromEventFlow
          (metacicDecidableNeutralSpineToEventFlow x) = some x) /\
        (forall x y : MetaCICDecidableNeutralSpineUp,
          metacicDecidableNeutralSpineToEventFlow x =
            metacicDecidableNeutralSpineToEventFlow y -> x = y) /\
          metacicDecidableNeutralSpineFields
              (MetaCICDecidableNeutralSpineUp.mk BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
            [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
              BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact metacicDecidableNeutralSpineDecode_encode_bhist
  · constructor
    · exact metacicDecidableNeutralSpine_round_trip
    · constructor
      · intro x y heq
        exact metacicDecidableNeutralSpineToEventFlow_injective heq
      · rfl

end BEDC.Derived.MetaCICDecidableNeutralSpineUp
