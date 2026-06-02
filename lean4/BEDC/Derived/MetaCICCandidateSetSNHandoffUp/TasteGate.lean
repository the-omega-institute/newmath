import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICCandidateSetSNHandoffUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICCandidateSetSNHandoffUp : Type where
  | mk (candidate candidateSet typed beta snExport noInfinite transport replay provenance name :
      BHist) : MetaCICCandidateSetSNHandoffUp
  deriving DecidableEq

def metaCICCandidateSetSNHandoffEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaCICCandidateSetSNHandoffEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaCICCandidateSetSNHandoffEncodeBHist h

def metaCICCandidateSetSNHandoffDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaCICCandidateSetSNHandoffDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaCICCandidateSetSNHandoffDecodeBHist tail)

private theorem metaCICCandidateSetSNHandoffDecode_encode_bhist :
    forall h : BHist,
      metaCICCandidateSetSNHandoffDecodeBHist
          (metaCICCandidateSetSNHandoffEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def metaCICCandidateSetSNHandoffToEventFlow : MetaCICCandidateSetSNHandoffUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICCandidateSetSNHandoffUp.mk candidate candidateSet typed beta snExport noInfinite
      transport replay provenance name =>
      [[BMark.b0],
        metaCICCandidateSetSNHandoffEncodeBHist candidate,
        [BMark.b1, BMark.b0],
        metaCICCandidateSetSNHandoffEncodeBHist candidateSet,
        [BMark.b1, BMark.b1, BMark.b0],
        metaCICCandidateSetSNHandoffEncodeBHist typed,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICCandidateSetSNHandoffEncodeBHist beta,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICCandidateSetSNHandoffEncodeBHist snExport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICCandidateSetSNHandoffEncodeBHist noInfinite,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICCandidateSetSNHandoffEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        metaCICCandidateSetSNHandoffEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        metaCICCandidateSetSNHandoffEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        metaCICCandidateSetSNHandoffEncodeBHist name]

private def metaCICCandidateSetSNHandoffEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => metaCICCandidateSetSNHandoffEventAt index rest

def metaCICCandidateSetSNHandoffFromEventFlow
    (ef : EventFlow) : Option MetaCICCandidateSetSNHandoffUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MetaCICCandidateSetSNHandoffUp.mk
      (metaCICCandidateSetSNHandoffDecodeBHist (metaCICCandidateSetSNHandoffEventAt 1 ef))
      (metaCICCandidateSetSNHandoffDecodeBHist (metaCICCandidateSetSNHandoffEventAt 3 ef))
      (metaCICCandidateSetSNHandoffDecodeBHist (metaCICCandidateSetSNHandoffEventAt 5 ef))
      (metaCICCandidateSetSNHandoffDecodeBHist (metaCICCandidateSetSNHandoffEventAt 7 ef))
      (metaCICCandidateSetSNHandoffDecodeBHist (metaCICCandidateSetSNHandoffEventAt 9 ef))
      (metaCICCandidateSetSNHandoffDecodeBHist (metaCICCandidateSetSNHandoffEventAt 11 ef))
      (metaCICCandidateSetSNHandoffDecodeBHist (metaCICCandidateSetSNHandoffEventAt 13 ef))
      (metaCICCandidateSetSNHandoffDecodeBHist (metaCICCandidateSetSNHandoffEventAt 15 ef))
      (metaCICCandidateSetSNHandoffDecodeBHist (metaCICCandidateSetSNHandoffEventAt 17 ef))
      (metaCICCandidateSetSNHandoffDecodeBHist (metaCICCandidateSetSNHandoffEventAt 19 ef)))

private theorem metaCICCandidateSetSNHandoff_round_trip :
    forall x : MetaCICCandidateSetSNHandoffUp,
      metaCICCandidateSetSNHandoffFromEventFlow
          (metaCICCandidateSetSNHandoffToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk candidate candidateSet typed beta snExport noInfinite transport replay provenance name =>
      change
        some
          (MetaCICCandidateSetSNHandoffUp.mk
            (metaCICCandidateSetSNHandoffDecodeBHist
              (metaCICCandidateSetSNHandoffEncodeBHist candidate))
            (metaCICCandidateSetSNHandoffDecodeBHist
              (metaCICCandidateSetSNHandoffEncodeBHist candidateSet))
            (metaCICCandidateSetSNHandoffDecodeBHist
              (metaCICCandidateSetSNHandoffEncodeBHist typed))
            (metaCICCandidateSetSNHandoffDecodeBHist
              (metaCICCandidateSetSNHandoffEncodeBHist beta))
            (metaCICCandidateSetSNHandoffDecodeBHist
              (metaCICCandidateSetSNHandoffEncodeBHist snExport))
            (metaCICCandidateSetSNHandoffDecodeBHist
              (metaCICCandidateSetSNHandoffEncodeBHist noInfinite))
            (metaCICCandidateSetSNHandoffDecodeBHist
              (metaCICCandidateSetSNHandoffEncodeBHist transport))
            (metaCICCandidateSetSNHandoffDecodeBHist
              (metaCICCandidateSetSNHandoffEncodeBHist replay))
            (metaCICCandidateSetSNHandoffDecodeBHist
              (metaCICCandidateSetSNHandoffEncodeBHist provenance))
            (metaCICCandidateSetSNHandoffDecodeBHist
              (metaCICCandidateSetSNHandoffEncodeBHist name))) =
          some
            (MetaCICCandidateSetSNHandoffUp.mk candidate candidateSet typed beta snExport
              noInfinite transport replay provenance name)
      rw [metaCICCandidateSetSNHandoffDecode_encode_bhist candidate,
        metaCICCandidateSetSNHandoffDecode_encode_bhist candidateSet,
        metaCICCandidateSetSNHandoffDecode_encode_bhist typed,
        metaCICCandidateSetSNHandoffDecode_encode_bhist beta,
        metaCICCandidateSetSNHandoffDecode_encode_bhist snExport,
        metaCICCandidateSetSNHandoffDecode_encode_bhist noInfinite,
        metaCICCandidateSetSNHandoffDecode_encode_bhist transport,
        metaCICCandidateSetSNHandoffDecode_encode_bhist replay,
        metaCICCandidateSetSNHandoffDecode_encode_bhist provenance,
        metaCICCandidateSetSNHandoffDecode_encode_bhist name]

private theorem metaCICCandidateSetSNHandoffToEventFlow_injective
    {x y : MetaCICCandidateSetSNHandoffUp} :
    metaCICCandidateSetSNHandoffToEventFlow x =
      metaCICCandidateSetSNHandoffToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaCICCandidateSetSNHandoffFromEventFlow
          (metaCICCandidateSetSNHandoffToEventFlow x) =
        metaCICCandidateSetSNHandoffFromEventFlow
          (metaCICCandidateSetSNHandoffToEventFlow y) :=
    congrArg metaCICCandidateSetSNHandoffFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metaCICCandidateSetSNHandoff_round_trip x).symm
      (Eq.trans hread (metaCICCandidateSetSNHandoff_round_trip y)))

instance metaCICCandidateSetSNHandoffBHistCarrier :
    BHistCarrier MetaCICCandidateSetSNHandoffUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaCICCandidateSetSNHandoffToEventFlow
  fromEventFlow := metaCICCandidateSetSNHandoffFromEventFlow

instance metaCICCandidateSetSNHandoffChapterTasteGate :
    ChapterTasteGate MetaCICCandidateSetSNHandoffUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metaCICCandidateSetSNHandoffFromEventFlow
          (metaCICCandidateSetSNHandoffToEventFlow x) = some x
    exact metaCICCandidateSetSNHandoff_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metaCICCandidateSetSNHandoffToEventFlow_injective heq)

instance metaCICCandidateSetSNHandoffFieldFaithful :
    FieldFaithful MetaCICCandidateSetSNHandoffUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | MetaCICCandidateSetSNHandoffUp.mk candidate candidateSet typed beta snExport noInfinite
        transport replay provenance name =>
        [candidate, candidateSet, typed, beta, snExport, noInfinite, transport, replay,
          provenance, name]
  field_faithful := by
    intro x y h
    cases x with
    | mk candidate₁ candidateSet₁ typed₁ beta₁ snExport₁ noInfinite₁ transport₁ replay₁
        provenance₁ name₁ =>
        cases y with
        | mk candidate₂ candidateSet₂ typed₂ beta₂ snExport₂ noInfinite₂ transport₂ replay₂
            provenance₂ name₂ =>
            simp only [] at h
            cases h
            rfl

instance metaCICCandidateSetSNHandoffNontrivial :
    Nontrivial MetaCICCandidateSetSNHandoffUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetaCICCandidateSetSNHandoffUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MetaCICCandidateSetSNHandoffUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MetaCICCandidateSetSNHandoffUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metaCICCandidateSetSNHandoffChapterTasteGate

theorem MetaCICCandidateSetSNHandoffTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate MetaCICCandidateSetSNHandoffUp) ∧
      Nonempty (FieldFaithful MetaCICCandidateSetSNHandoffUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial MetaCICCandidateSetSNHandoffUp) ∧
      (∀ h : BHist,
        metaCICCandidateSetSNHandoffDecodeBHist
            (metaCICCandidateSetSNHandoffEncodeBHist h) = h) ∧
      (∀ x : MetaCICCandidateSetSNHandoffUp,
        metaCICCandidateSetSNHandoffFromEventFlow
            (metaCICCandidateSetSNHandoffToEventFlow x) = some x) ∧
      metaCICCandidateSetSNHandoffEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨metaCICCandidateSetSNHandoffChapterTasteGate⟩
  · constructor
    · exact ⟨metaCICCandidateSetSNHandoffFieldFaithful⟩
    · constructor
      · exact ⟨metaCICCandidateSetSNHandoffNontrivial⟩
      · constructor
        · exact metaCICCandidateSetSNHandoffDecode_encode_bhist
        · constructor
          · exact metaCICCandidateSetSNHandoff_round_trip
          · rfl

end BEDC.Derived.MetaCICCandidateSetSNHandoffUp
