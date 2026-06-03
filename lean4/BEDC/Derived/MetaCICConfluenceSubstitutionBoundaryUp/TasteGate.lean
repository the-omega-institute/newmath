import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICConfluenceSubstitutionBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICConfluenceSubstitutionBoundaryUp : Type where
  | mk (typed redex substitution handoff join obstruction gate transport replay provenance name :
      BHist) : MetaCICConfluenceSubstitutionBoundaryUp
  deriving DecidableEq

def metaCICConfluenceSubstitutionBoundaryEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaCICConfluenceSubstitutionBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaCICConfluenceSubstitutionBoundaryEncodeBHist h

def metaCICConfluenceSubstitutionBoundaryDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaCICConfluenceSubstitutionBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaCICConfluenceSubstitutionBoundaryDecodeBHist tail)

private theorem metaCICConfluenceSubstitutionBoundaryDecode_encode_bhist :
    forall h : BHist,
      metaCICConfluenceSubstitutionBoundaryDecodeBHist
          (metaCICConfluenceSubstitutionBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def metaCICConfluenceSubstitutionBoundaryToEventFlow :
    MetaCICConfluenceSubstitutionBoundaryUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICConfluenceSubstitutionBoundaryUp.mk typed redex substitution handoff join
      obstruction gate transport replay provenance name =>
      [[BMark.b0],
        metaCICConfluenceSubstitutionBoundaryEncodeBHist typed,
        [BMark.b1, BMark.b0],
        metaCICConfluenceSubstitutionBoundaryEncodeBHist redex,
        [BMark.b1, BMark.b1, BMark.b0],
        metaCICConfluenceSubstitutionBoundaryEncodeBHist substitution,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICConfluenceSubstitutionBoundaryEncodeBHist handoff,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICConfluenceSubstitutionBoundaryEncodeBHist join,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICConfluenceSubstitutionBoundaryEncodeBHist obstruction,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICConfluenceSubstitutionBoundaryEncodeBHist gate,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        metaCICConfluenceSubstitutionBoundaryEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        metaCICConfluenceSubstitutionBoundaryEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        metaCICConfluenceSubstitutionBoundaryEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICConfluenceSubstitutionBoundaryEncodeBHist name]

private def metaCICConfluenceSubstitutionBoundaryEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => metaCICConfluenceSubstitutionBoundaryEventAt index rest

def metaCICConfluenceSubstitutionBoundaryFromEventFlow
    (ef : EventFlow) : Option MetaCICConfluenceSubstitutionBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MetaCICConfluenceSubstitutionBoundaryUp.mk
      (metaCICConfluenceSubstitutionBoundaryDecodeBHist
        (metaCICConfluenceSubstitutionBoundaryEventAt 1 ef))
      (metaCICConfluenceSubstitutionBoundaryDecodeBHist
        (metaCICConfluenceSubstitutionBoundaryEventAt 3 ef))
      (metaCICConfluenceSubstitutionBoundaryDecodeBHist
        (metaCICConfluenceSubstitutionBoundaryEventAt 5 ef))
      (metaCICConfluenceSubstitutionBoundaryDecodeBHist
        (metaCICConfluenceSubstitutionBoundaryEventAt 7 ef))
      (metaCICConfluenceSubstitutionBoundaryDecodeBHist
        (metaCICConfluenceSubstitutionBoundaryEventAt 9 ef))
      (metaCICConfluenceSubstitutionBoundaryDecodeBHist
        (metaCICConfluenceSubstitutionBoundaryEventAt 11 ef))
      (metaCICConfluenceSubstitutionBoundaryDecodeBHist
        (metaCICConfluenceSubstitutionBoundaryEventAt 13 ef))
      (metaCICConfluenceSubstitutionBoundaryDecodeBHist
        (metaCICConfluenceSubstitutionBoundaryEventAt 15 ef))
      (metaCICConfluenceSubstitutionBoundaryDecodeBHist
        (metaCICConfluenceSubstitutionBoundaryEventAt 17 ef))
      (metaCICConfluenceSubstitutionBoundaryDecodeBHist
        (metaCICConfluenceSubstitutionBoundaryEventAt 19 ef))
      (metaCICConfluenceSubstitutionBoundaryDecodeBHist
        (metaCICConfluenceSubstitutionBoundaryEventAt 21 ef)))

private theorem metaCICConfluenceSubstitutionBoundary_round_trip :
    forall x : MetaCICConfluenceSubstitutionBoundaryUp,
      metaCICConfluenceSubstitutionBoundaryFromEventFlow
          (metaCICConfluenceSubstitutionBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk typed redex substitution handoff join obstruction gate transport replay provenance name =>
      change
        some
          (MetaCICConfluenceSubstitutionBoundaryUp.mk
            (metaCICConfluenceSubstitutionBoundaryDecodeBHist
              (metaCICConfluenceSubstitutionBoundaryEncodeBHist typed))
            (metaCICConfluenceSubstitutionBoundaryDecodeBHist
              (metaCICConfluenceSubstitutionBoundaryEncodeBHist redex))
            (metaCICConfluenceSubstitutionBoundaryDecodeBHist
              (metaCICConfluenceSubstitutionBoundaryEncodeBHist substitution))
            (metaCICConfluenceSubstitutionBoundaryDecodeBHist
              (metaCICConfluenceSubstitutionBoundaryEncodeBHist handoff))
            (metaCICConfluenceSubstitutionBoundaryDecodeBHist
              (metaCICConfluenceSubstitutionBoundaryEncodeBHist join))
            (metaCICConfluenceSubstitutionBoundaryDecodeBHist
              (metaCICConfluenceSubstitutionBoundaryEncodeBHist obstruction))
            (metaCICConfluenceSubstitutionBoundaryDecodeBHist
              (metaCICConfluenceSubstitutionBoundaryEncodeBHist gate))
            (metaCICConfluenceSubstitutionBoundaryDecodeBHist
              (metaCICConfluenceSubstitutionBoundaryEncodeBHist transport))
            (metaCICConfluenceSubstitutionBoundaryDecodeBHist
              (metaCICConfluenceSubstitutionBoundaryEncodeBHist replay))
            (metaCICConfluenceSubstitutionBoundaryDecodeBHist
              (metaCICConfluenceSubstitutionBoundaryEncodeBHist provenance))
            (metaCICConfluenceSubstitutionBoundaryDecodeBHist
              (metaCICConfluenceSubstitutionBoundaryEncodeBHist name))) =
          some
            (MetaCICConfluenceSubstitutionBoundaryUp.mk typed redex substitution handoff
              join obstruction gate transport replay provenance name)
      rw [metaCICConfluenceSubstitutionBoundaryDecode_encode_bhist typed,
        metaCICConfluenceSubstitutionBoundaryDecode_encode_bhist redex,
        metaCICConfluenceSubstitutionBoundaryDecode_encode_bhist substitution,
        metaCICConfluenceSubstitutionBoundaryDecode_encode_bhist handoff,
        metaCICConfluenceSubstitutionBoundaryDecode_encode_bhist join,
        metaCICConfluenceSubstitutionBoundaryDecode_encode_bhist obstruction,
        metaCICConfluenceSubstitutionBoundaryDecode_encode_bhist gate,
        metaCICConfluenceSubstitutionBoundaryDecode_encode_bhist transport,
        metaCICConfluenceSubstitutionBoundaryDecode_encode_bhist replay,
        metaCICConfluenceSubstitutionBoundaryDecode_encode_bhist provenance,
        metaCICConfluenceSubstitutionBoundaryDecode_encode_bhist name]

private theorem metaCICConfluenceSubstitutionBoundaryToEventFlow_injective
    {x y : MetaCICConfluenceSubstitutionBoundaryUp} :
    metaCICConfluenceSubstitutionBoundaryToEventFlow x =
      metaCICConfluenceSubstitutionBoundaryToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaCICConfluenceSubstitutionBoundaryFromEventFlow
          (metaCICConfluenceSubstitutionBoundaryToEventFlow x) =
        metaCICConfluenceSubstitutionBoundaryFromEventFlow
          (metaCICConfluenceSubstitutionBoundaryToEventFlow y) :=
    congrArg metaCICConfluenceSubstitutionBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metaCICConfluenceSubstitutionBoundary_round_trip x).symm
      (Eq.trans hread (metaCICConfluenceSubstitutionBoundary_round_trip y)))

instance metaCICConfluenceSubstitutionBoundaryBHistCarrier :
    BHistCarrier MetaCICConfluenceSubstitutionBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaCICConfluenceSubstitutionBoundaryToEventFlow
  fromEventFlow := metaCICConfluenceSubstitutionBoundaryFromEventFlow

instance metaCICConfluenceSubstitutionBoundaryChapterTasteGate :
    ChapterTasteGate MetaCICConfluenceSubstitutionBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metaCICConfluenceSubstitutionBoundaryFromEventFlow
          (metaCICConfluenceSubstitutionBoundaryToEventFlow x) = some x
    exact metaCICConfluenceSubstitutionBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metaCICConfluenceSubstitutionBoundaryToEventFlow_injective heq)

instance metaCICConfluenceSubstitutionBoundaryFieldFaithful :
    FieldFaithful MetaCICConfluenceSubstitutionBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | MetaCICConfluenceSubstitutionBoundaryUp.mk typed redex substitution handoff join
        obstruction gate transport replay provenance name =>
        [typed, redex, substitution, handoff, join, obstruction, gate, transport, replay,
          provenance, name]
  field_faithful := by
    intro x y h
    cases x with
    | mk typed₁ redex₁ substitution₁ handoff₁ join₁ obstruction₁ gate₁ transport₁ replay₁
        provenance₁ name₁ =>
        cases y with
        | mk typed₂ redex₂ substitution₂ handoff₂ join₂ obstruction₂ gate₂ transport₂ replay₂
            provenance₂ name₂ =>
            simp only [] at h
            cases h
            rfl

instance metaCICConfluenceSubstitutionBoundaryNontrivial :
    Nontrivial MetaCICConfluenceSubstitutionBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetaCICConfluenceSubstitutionBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      MetaCICConfluenceSubstitutionBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MetaCICConfluenceSubstitutionBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metaCICConfluenceSubstitutionBoundaryChapterTasteGate

theorem MetaCICConfluenceSubstitutionBoundaryTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate MetaCICConfluenceSubstitutionBoundaryUp) ∧
      Nonempty (FieldFaithful MetaCICConfluenceSubstitutionBoundaryUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial MetaCICConfluenceSubstitutionBoundaryUp) ∧
      (∀ h : BHist,
        metaCICConfluenceSubstitutionBoundaryDecodeBHist
            (metaCICConfluenceSubstitutionBoundaryEncodeBHist h) = h) ∧
      (∀ x : MetaCICConfluenceSubstitutionBoundaryUp,
        metaCICConfluenceSubstitutionBoundaryFromEventFlow
            (metaCICConfluenceSubstitutionBoundaryToEventFlow x) = some x) ∧
      metaCICConfluenceSubstitutionBoundaryEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨metaCICConfluenceSubstitutionBoundaryChapterTasteGate⟩
  · constructor
    · exact ⟨metaCICConfluenceSubstitutionBoundaryFieldFaithful⟩
    · constructor
      · exact ⟨metaCICConfluenceSubstitutionBoundaryNontrivial⟩
      · constructor
        · exact metaCICConfluenceSubstitutionBoundaryDecode_encode_bhist
        · constructor
          · exact metaCICConfluenceSubstitutionBoundary_round_trip
          · rfl

end BEDC.Derived.MetaCICConfluenceSubstitutionBoundaryUp
