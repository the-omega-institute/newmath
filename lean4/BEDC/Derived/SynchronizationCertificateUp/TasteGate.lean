import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SynchronizationCertificateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SynchronizationCertificateUp : Type where
  | mk :
      (source target sourceStream targetStream correspondence locality refusal transport
        provenance name : BHist) →
      SynchronizationCertificateUp

def synchronizationCertificateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: synchronizationCertificateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: synchronizationCertificateEncodeBHist h

def synchronizationCertificateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (synchronizationCertificateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (synchronizationCertificateDecodeBHist tail)

theorem synchronizationCertificateDecode_encode_bhist :
    ∀ h : BHist,
      synchronizationCertificateDecodeBHist (synchronizationCertificateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def synchronizationCertificateToEventFlow :
    SynchronizationCertificateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SynchronizationCertificateUp.mk source target sourceStream targetStream correspondence
      locality refusal transport provenance name =>
      [[BMark.b0],
        synchronizationCertificateEncodeBHist source,
        [BMark.b1, BMark.b0],
        synchronizationCertificateEncodeBHist target,
        [BMark.b1, BMark.b1, BMark.b0],
        synchronizationCertificateEncodeBHist sourceStream,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        synchronizationCertificateEncodeBHist targetStream,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        synchronizationCertificateEncodeBHist correspondence,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        synchronizationCertificateEncodeBHist locality,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        synchronizationCertificateEncodeBHist refusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        synchronizationCertificateEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        synchronizationCertificateEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        synchronizationCertificateEncodeBHist name]

private def synchronizationCertificateFromEventFlow :
    EventFlow → Option SynchronizationCertificateUp
  -- BEDC touchpoint anchor: BHist BMark
  | [_tag0, source, _tag1, target, _tag2, sourceStream, _tag3, targetStream,
      _tag4, correspondence, _tag5, locality, _tag6, refusal, _tag7, transport,
      _tag8, provenance, _tag9, name] =>
      some
        (SynchronizationCertificateUp.mk
          (synchronizationCertificateDecodeBHist source)
          (synchronizationCertificateDecodeBHist target)
          (synchronizationCertificateDecodeBHist sourceStream)
          (synchronizationCertificateDecodeBHist targetStream)
          (synchronizationCertificateDecodeBHist correspondence)
          (synchronizationCertificateDecodeBHist locality)
          (synchronizationCertificateDecodeBHist refusal)
          (synchronizationCertificateDecodeBHist transport)
          (synchronizationCertificateDecodeBHist provenance)
          (synchronizationCertificateDecodeBHist name))
  | _ => none

private theorem synchronizationCertificate_round_trip :
    ∀ x : SynchronizationCertificateUp,
      synchronizationCertificateFromEventFlow (synchronizationCertificateToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source target sourceStream targetStream correspondence locality refusal transport
      provenance name =>
      change
        some
          (SynchronizationCertificateUp.mk
            (synchronizationCertificateDecodeBHist
              (synchronizationCertificateEncodeBHist source))
            (synchronizationCertificateDecodeBHist
              (synchronizationCertificateEncodeBHist target))
            (synchronizationCertificateDecodeBHist
              (synchronizationCertificateEncodeBHist sourceStream))
            (synchronizationCertificateDecodeBHist
              (synchronizationCertificateEncodeBHist targetStream))
            (synchronizationCertificateDecodeBHist
              (synchronizationCertificateEncodeBHist correspondence))
            (synchronizationCertificateDecodeBHist
              (synchronizationCertificateEncodeBHist locality))
            (synchronizationCertificateDecodeBHist
              (synchronizationCertificateEncodeBHist refusal))
            (synchronizationCertificateDecodeBHist
              (synchronizationCertificateEncodeBHist transport))
            (synchronizationCertificateDecodeBHist
              (synchronizationCertificateEncodeBHist provenance))
            (synchronizationCertificateDecodeBHist
              (synchronizationCertificateEncodeBHist name))) =
          some
            (SynchronizationCertificateUp.mk source target sourceStream targetStream
              correspondence locality refusal transport provenance name)
      rw [synchronizationCertificateDecode_encode_bhist source,
        synchronizationCertificateDecode_encode_bhist target,
        synchronizationCertificateDecode_encode_bhist sourceStream,
        synchronizationCertificateDecode_encode_bhist targetStream,
        synchronizationCertificateDecode_encode_bhist correspondence,
        synchronizationCertificateDecode_encode_bhist locality,
        synchronizationCertificateDecode_encode_bhist refusal,
        synchronizationCertificateDecode_encode_bhist transport,
        synchronizationCertificateDecode_encode_bhist provenance,
        synchronizationCertificateDecode_encode_bhist name]

private theorem synchronizationCertificateToEventFlow_injective
    {x y : SynchronizationCertificateUp} :
    synchronizationCertificateToEventFlow x = synchronizationCertificateToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      synchronizationCertificateFromEventFlow (synchronizationCertificateToEventFlow x) =
        synchronizationCertificateFromEventFlow (synchronizationCertificateToEventFlow y) :=
    congrArg synchronizationCertificateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (synchronizationCertificate_round_trip x).symm
      (Eq.trans hread (synchronizationCertificate_round_trip y)))

def synchronizationCertificateFields : SynchronizationCertificateUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SynchronizationCertificateUp.mk source target sourceStream targetStream correspondence
      locality refusal transport provenance name =>
      [source, target, sourceStream, targetStream, correspondence, locality, refusal,
        transport, provenance, name]

private theorem synchronizationCertificate_field_faithful :
    ∀ x y : SynchronizationCertificateUp,
      synchronizationCertificateFields x = synchronizationCertificateFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk source₁ target₁ sourceStream₁ targetStream₁ correspondence₁ locality₁ refusal₁
      transport₁ provenance₁ name₁ =>
      cases y with
      | mk source₂ target₂ sourceStream₂ targetStream₂ correspondence₂ locality₂ refusal₂
          transport₂ provenance₂ name₂ =>
          cases h
          rfl

instance synchronizationCertificateBHistCarrier :
    BHistCarrier SynchronizationCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := synchronizationCertificateToEventFlow
  fromEventFlow := synchronizationCertificateFromEventFlow

instance synchronizationCertificateChapterTasteGate :
    ChapterTasteGate SynchronizationCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      synchronizationCertificateFromEventFlow (synchronizationCertificateToEventFlow x) =
        some x
    exact synchronizationCertificate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (synchronizationCertificateToEventFlow_injective heq)

instance synchronizationCertificateFieldFaithful :
    FieldFaithful SynchronizationCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := synchronizationCertificateFields
  field_faithful := synchronizationCertificate_field_faithful

instance synchronizationCertificateNontrivial : Nontrivial SynchronizationCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SynchronizationCertificateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SynchronizationCertificateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SynchronizationCertificateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  synchronizationCertificateChapterTasteGate

theorem SynchronizationCertificateTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      synchronizationCertificateDecodeBHist (synchronizationCertificateEncodeBHist h) = h) ∧
      synchronizationCertificateEncodeBHist BHist.Empty = ([] : List BMark) ∧
        (∀ x y : SynchronizationCertificateUp,
          synchronizationCertificateFields x = synchronizationCertificateFields y → x = y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact synchronizationCertificateDecode_encode_bhist
  · constructor
    · rfl
    · exact synchronizationCertificate_field_faithful

end BEDC.Derived.SynchronizationCertificateUp
