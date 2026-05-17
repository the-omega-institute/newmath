import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ObservationLogicBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ObservationLogicBoundaryUp : Type where
  | mk
      (observation logic metaLoop phaseRefusal gapAudit residue transport replay provenance
        localCert : BHist) :
      ObservationLogicBoundaryUp

def observationLogicBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: observationLogicBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: observationLogicBoundaryEncodeBHist h

def observationLogicBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (observationLogicBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (observationLogicBoundaryDecodeBHist tail)

private theorem observationLogicBoundary_decode_encode_bhist :
    ∀ h : BHist,
      observationLogicBoundaryDecodeBHist (observationLogicBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def observationLogicBoundaryFields : ObservationLogicBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ObservationLogicBoundaryUp.mk observation logic metaLoop phaseRefusal gapAudit residue
      transport replay provenance localCert =>
      [observation, logic, metaLoop, phaseRefusal, gapAudit, residue, transport, replay,
        provenance, localCert]

def observationLogicBoundaryToEventFlow : ObservationLogicBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (observationLogicBoundaryFields x).map observationLogicBoundaryEncodeBHist

def observationLogicBoundaryFromEventFlow : EventFlow → Option ObservationLogicBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | observation :: logic :: metaLoop :: phaseRefusal :: gapAudit :: residue :: transport ::
      replay :: provenance :: localCert :: [] =>
      some
        (ObservationLogicBoundaryUp.mk
          (observationLogicBoundaryDecodeBHist observation)
          (observationLogicBoundaryDecodeBHist logic)
          (observationLogicBoundaryDecodeBHist metaLoop)
          (observationLogicBoundaryDecodeBHist phaseRefusal)
          (observationLogicBoundaryDecodeBHist gapAudit)
          (observationLogicBoundaryDecodeBHist residue)
          (observationLogicBoundaryDecodeBHist transport)
          (observationLogicBoundaryDecodeBHist replay)
          (observationLogicBoundaryDecodeBHist provenance)
          (observationLogicBoundaryDecodeBHist localCert))
  | _ => none

private theorem observationLogicBoundary_round_trip :
    ∀ x : ObservationLogicBoundaryUp,
      observationLogicBoundaryFromEventFlow
        (observationLogicBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk observation logic metaLoop phaseRefusal gapAudit residue transport replay provenance
      localCert =>
      change
        some
          (ObservationLogicBoundaryUp.mk
            (observationLogicBoundaryDecodeBHist
              (observationLogicBoundaryEncodeBHist observation))
            (observationLogicBoundaryDecodeBHist
              (observationLogicBoundaryEncodeBHist logic))
            (observationLogicBoundaryDecodeBHist
              (observationLogicBoundaryEncodeBHist metaLoop))
            (observationLogicBoundaryDecodeBHist
              (observationLogicBoundaryEncodeBHist phaseRefusal))
            (observationLogicBoundaryDecodeBHist
              (observationLogicBoundaryEncodeBHist gapAudit))
            (observationLogicBoundaryDecodeBHist
              (observationLogicBoundaryEncodeBHist residue))
            (observationLogicBoundaryDecodeBHist
              (observationLogicBoundaryEncodeBHist transport))
            (observationLogicBoundaryDecodeBHist
              (observationLogicBoundaryEncodeBHist replay))
            (observationLogicBoundaryDecodeBHist
              (observationLogicBoundaryEncodeBHist provenance))
            (observationLogicBoundaryDecodeBHist
              (observationLogicBoundaryEncodeBHist localCert))) =
          some
            (ObservationLogicBoundaryUp.mk observation logic metaLoop phaseRefusal gapAudit
              residue transport replay provenance localCert)
      rw [observationLogicBoundary_decode_encode_bhist observation,
        observationLogicBoundary_decode_encode_bhist logic,
        observationLogicBoundary_decode_encode_bhist metaLoop,
        observationLogicBoundary_decode_encode_bhist phaseRefusal,
        observationLogicBoundary_decode_encode_bhist gapAudit,
        observationLogicBoundary_decode_encode_bhist residue,
        observationLogicBoundary_decode_encode_bhist transport,
        observationLogicBoundary_decode_encode_bhist replay,
        observationLogicBoundary_decode_encode_bhist provenance,
        observationLogicBoundary_decode_encode_bhist localCert]

private theorem observationLogicBoundaryToEventFlow_injective
    {x y : ObservationLogicBoundaryUp} :
    observationLogicBoundaryToEventFlow x = observationLogicBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      observationLogicBoundaryFromEventFlow (observationLogicBoundaryToEventFlow x) =
        observationLogicBoundaryFromEventFlow (observationLogicBoundaryToEventFlow y) :=
    congrArg observationLogicBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (observationLogicBoundary_round_trip x).symm
      (Eq.trans hread (observationLogicBoundary_round_trip y)))

private theorem observationLogicBoundary_fields_faithful :
    ∀ x y : ObservationLogicBoundaryUp,
      observationLogicBoundaryFields x = observationLogicBoundaryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk observation₁ logic₁ metaLoop₁ phaseRefusal₁ gapAudit₁ residue₁ transport₁ replay₁
      provenance₁ localCert₁ =>
      cases y with
      | mk observation₂ logic₂ metaLoop₂ phaseRefusal₂ gapAudit₂ residue₂ transport₂ replay₂
          provenance₂ localCert₂ =>
          cases hfields
          rfl

instance observationLogicBoundaryBHistCarrier :
    BHistCarrier ObservationLogicBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := observationLogicBoundaryToEventFlow
  fromEventFlow := observationLogicBoundaryFromEventFlow

instance observationLogicBoundaryChapterTasteGate :
    ChapterTasteGate ObservationLogicBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      observationLogicBoundaryFromEventFlow
        (observationLogicBoundaryToEventFlow x) = some x
    exact observationLogicBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (observationLogicBoundaryToEventFlow_injective heq)

instance observationLogicBoundaryFieldFaithful :
    FieldFaithful ObservationLogicBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := observationLogicBoundaryFields
  field_faithful := observationLogicBoundary_fields_faithful

instance observationLogicBoundaryNontrivial :
    Nontrivial ObservationLogicBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ObservationLogicBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ObservationLogicBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ObservationLogicBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  observationLogicBoundaryChapterTasteGate

def taste_gate_witness : FieldFaithful ObservationLogicBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  observationLogicBoundaryFieldFaithful

end BEDC.Derived.ObservationLogicBoundaryUp
