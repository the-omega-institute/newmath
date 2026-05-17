import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NameEligibilityProofUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NameEligibilityProofUp : Type where
  | mk :
      (target source classifier strength audit refusal transport replay provenance name : BHist) →
      NameEligibilityProofUp
  deriving DecidableEq

def nameEligibilityProofEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: nameEligibilityProofEncodeBHist h
  | BHist.e1 h => BMark.b1 :: nameEligibilityProofEncodeBHist h

def nameEligibilityProofDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (nameEligibilityProofDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (nameEligibilityProofDecodeBHist tail)

private theorem nameEligibilityProof_decode_encode_bhist :
    ∀ h : BHist, nameEligibilityProofDecodeBHist (nameEligibilityProofEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def nameEligibilityProofFields : NameEligibilityProofUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NameEligibilityProofUp.mk target source classifier strength audit refusal transport replay
      provenance name =>
      [target, source, classifier, strength, audit, refusal, transport, replay, provenance, name]

def nameEligibilityProofToEventFlow : NameEligibilityProofUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map nameEligibilityProofEncodeBHist (nameEligibilityProofFields x)

def nameEligibilityProofFromEventFlow : EventFlow → Option NameEligibilityProofUp
  -- BEDC touchpoint anchor: BHist BMark
  | [target, source, classifier, strength, audit, refusal, transport, replay, provenance, name] =>
      some
        (NameEligibilityProofUp.mk
          (nameEligibilityProofDecodeBHist target)
          (nameEligibilityProofDecodeBHist source)
          (nameEligibilityProofDecodeBHist classifier)
          (nameEligibilityProofDecodeBHist strength)
          (nameEligibilityProofDecodeBHist audit)
          (nameEligibilityProofDecodeBHist refusal)
          (nameEligibilityProofDecodeBHist transport)
          (nameEligibilityProofDecodeBHist replay)
          (nameEligibilityProofDecodeBHist provenance)
          (nameEligibilityProofDecodeBHist name))
  | _ => none

private theorem nameEligibilityProof_round_trip :
    ∀ x : NameEligibilityProofUp,
      nameEligibilityProofFromEventFlow (nameEligibilityProofToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk target source classifier strength audit refusal transport replay provenance name =>
      change
        some
          (NameEligibilityProofUp.mk
            (nameEligibilityProofDecodeBHist (nameEligibilityProofEncodeBHist target))
            (nameEligibilityProofDecodeBHist (nameEligibilityProofEncodeBHist source))
            (nameEligibilityProofDecodeBHist (nameEligibilityProofEncodeBHist classifier))
            (nameEligibilityProofDecodeBHist (nameEligibilityProofEncodeBHist strength))
            (nameEligibilityProofDecodeBHist (nameEligibilityProofEncodeBHist audit))
            (nameEligibilityProofDecodeBHist (nameEligibilityProofEncodeBHist refusal))
            (nameEligibilityProofDecodeBHist (nameEligibilityProofEncodeBHist transport))
            (nameEligibilityProofDecodeBHist (nameEligibilityProofEncodeBHist replay))
            (nameEligibilityProofDecodeBHist (nameEligibilityProofEncodeBHist provenance))
            (nameEligibilityProofDecodeBHist (nameEligibilityProofEncodeBHist name))) =
          some
            (NameEligibilityProofUp.mk target source classifier strength audit refusal transport
              replay provenance name)
      rw [nameEligibilityProof_decode_encode_bhist target,
        nameEligibilityProof_decode_encode_bhist source,
        nameEligibilityProof_decode_encode_bhist classifier,
        nameEligibilityProof_decode_encode_bhist strength,
        nameEligibilityProof_decode_encode_bhist audit,
        nameEligibilityProof_decode_encode_bhist refusal,
        nameEligibilityProof_decode_encode_bhist transport,
        nameEligibilityProof_decode_encode_bhist replay,
        nameEligibilityProof_decode_encode_bhist provenance,
        nameEligibilityProof_decode_encode_bhist name]

private theorem nameEligibilityProofToEventFlow_injective {x y : NameEligibilityProofUp} :
    nameEligibilityProofToEventFlow x = nameEligibilityProofToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      nameEligibilityProofFromEventFlow (nameEligibilityProofToEventFlow x) =
        nameEligibilityProofFromEventFlow (nameEligibilityProofToEventFlow y) :=
    congrArg nameEligibilityProofFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (nameEligibilityProof_round_trip x).symm
      (Eq.trans hread (nameEligibilityProof_round_trip y)))

private theorem nameEligibilityProof_field_faithful :
    ∀ x y : NameEligibilityProofUp,
      nameEligibilityProofFields x = nameEligibilityProofFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk target₁ source₁ classifier₁ strength₁ audit₁ refusal₁ transport₁ replay₁ provenance₁
      name₁ =>
      cases y with
      | mk target₂ source₂ classifier₂ strength₂ audit₂ refusal₂ transport₂ replay₂ provenance₂
          name₂ =>
          cases h
          rfl

instance nameEligibilityProofBHistCarrier : BHistCarrier NameEligibilityProofUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := nameEligibilityProofToEventFlow
  fromEventFlow := nameEligibilityProofFromEventFlow

instance nameEligibilityProofChapterTasteGate : ChapterTasteGate NameEligibilityProofUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change nameEligibilityProofFromEventFlow (nameEligibilityProofToEventFlow x) = some x
    exact nameEligibilityProof_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (nameEligibilityProofToEventFlow_injective heq)

instance nameEligibilityProofFieldFaithful : FieldFaithful NameEligibilityProofUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := nameEligibilityProofFields
  field_faithful := nameEligibilityProof_field_faithful

instance nameEligibilityProofNontrivial : Nontrivial NameEligibilityProofUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨NameEligibilityProofUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      NameEligibilityProofUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate NameEligibilityProofUp :=
  -- BEDC touchpoint anchor: BHist BMark
  nameEligibilityProofChapterTasteGate

end BEDC.Derived.NameEligibilityProofUp
