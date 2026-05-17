import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.InscriptionNoveltySocketUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive InscriptionNoveltySocketUp : Type where
  | mk :
      (priorBoundary inscriptionEvent aspectSeparation auditGate transport replay provenance
        name : BHist) →
      InscriptionNoveltySocketUp
  deriving DecidableEq

def inscriptionNoveltySocketEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: inscriptionNoveltySocketEncodeBHist h
  | BHist.e1 h => BMark.b1 :: inscriptionNoveltySocketEncodeBHist h

def inscriptionNoveltySocketDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (inscriptionNoveltySocketDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (inscriptionNoveltySocketDecodeBHist tail)

private theorem inscriptionNoveltySocket_decode_encode_bhist :
    ∀ h : BHist,
      inscriptionNoveltySocketDecodeBHist (inscriptionNoveltySocketEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def inscriptionNoveltySocketFields : InscriptionNoveltySocketUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | InscriptionNoveltySocketUp.mk priorBoundary inscriptionEvent aspectSeparation auditGate
      transport replay provenance name =>
      [priorBoundary, inscriptionEvent, aspectSeparation, auditGate, transport, replay,
        provenance, name]

def inscriptionNoveltySocketToEventFlow : InscriptionNoveltySocketUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map inscriptionNoveltySocketEncodeBHist (inscriptionNoveltySocketFields x)

def inscriptionNoveltySocketFromEventFlow : EventFlow → Option InscriptionNoveltySocketUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | priorBoundary :: rest0 =>
      match rest0 with
      | [] => none
      | inscriptionEvent :: rest1 =>
          match rest1 with
          | [] => none
          | aspectSeparation :: rest2 =>
              match rest2 with
              | [] => none
              | auditGate :: rest3 =>
                  match rest3 with
                  | [] => none
                  | transport :: rest4 =>
                      match rest4 with
                      | [] => none
                      | replay :: rest5 =>
                          match rest5 with
                          | [] => none
                          | provenance :: rest6 =>
                              match rest6 with
                              | [] => none
                              | name :: rest7 =>
                                  match rest7 with
                                  | [] =>
                                      some
                                        (InscriptionNoveltySocketUp.mk
                                          (inscriptionNoveltySocketDecodeBHist priorBoundary)
                                          (inscriptionNoveltySocketDecodeBHist inscriptionEvent)
                                          (inscriptionNoveltySocketDecodeBHist aspectSeparation)
                                          (inscriptionNoveltySocketDecodeBHist auditGate)
                                          (inscriptionNoveltySocketDecodeBHist transport)
                                          (inscriptionNoveltySocketDecodeBHist replay)
                                          (inscriptionNoveltySocketDecodeBHist provenance)
                                          (inscriptionNoveltySocketDecodeBHist name))
                                  | _ :: _ => none

private theorem inscriptionNoveltySocket_round_trip :
    ∀ x : InscriptionNoveltySocketUp,
      inscriptionNoveltySocketFromEventFlow (inscriptionNoveltySocketToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk priorBoundary inscriptionEvent aspectSeparation auditGate transport replay provenance name =>
      change
        some
          (InscriptionNoveltySocketUp.mk
            (inscriptionNoveltySocketDecodeBHist
              (inscriptionNoveltySocketEncodeBHist priorBoundary))
            (inscriptionNoveltySocketDecodeBHist
              (inscriptionNoveltySocketEncodeBHist inscriptionEvent))
            (inscriptionNoveltySocketDecodeBHist
              (inscriptionNoveltySocketEncodeBHist aspectSeparation))
            (inscriptionNoveltySocketDecodeBHist
              (inscriptionNoveltySocketEncodeBHist auditGate))
            (inscriptionNoveltySocketDecodeBHist
              (inscriptionNoveltySocketEncodeBHist transport))
            (inscriptionNoveltySocketDecodeBHist
              (inscriptionNoveltySocketEncodeBHist replay))
            (inscriptionNoveltySocketDecodeBHist
              (inscriptionNoveltySocketEncodeBHist provenance))
            (inscriptionNoveltySocketDecodeBHist
              (inscriptionNoveltySocketEncodeBHist name))) =
          some
            (InscriptionNoveltySocketUp.mk priorBoundary inscriptionEvent aspectSeparation
              auditGate transport replay provenance name)
      rw [inscriptionNoveltySocket_decode_encode_bhist priorBoundary,
        inscriptionNoveltySocket_decode_encode_bhist inscriptionEvent,
        inscriptionNoveltySocket_decode_encode_bhist aspectSeparation,
        inscriptionNoveltySocket_decode_encode_bhist auditGate,
        inscriptionNoveltySocket_decode_encode_bhist transport,
        inscriptionNoveltySocket_decode_encode_bhist replay,
        inscriptionNoveltySocket_decode_encode_bhist provenance,
        inscriptionNoveltySocket_decode_encode_bhist name]

private theorem inscriptionNoveltySocketToEventFlow_injective {x y : InscriptionNoveltySocketUp} :
    inscriptionNoveltySocketToEventFlow x = inscriptionNoveltySocketToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      inscriptionNoveltySocketFromEventFlow (inscriptionNoveltySocketToEventFlow x) =
        inscriptionNoveltySocketFromEventFlow (inscriptionNoveltySocketToEventFlow y) :=
    congrArg inscriptionNoveltySocketFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (inscriptionNoveltySocket_round_trip x).symm
      (Eq.trans hread (inscriptionNoveltySocket_round_trip y)))

private theorem inscriptionNoveltySocket_field_faithful :
    ∀ x y : InscriptionNoveltySocketUp,
      inscriptionNoveltySocketFields x = inscriptionNoveltySocketFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk prior₁ event₁ aspect₁ gate₁ transport₁ replay₁ provenance₁ name₁ =>
      cases y with
      | mk prior₂ event₂ aspect₂ gate₂ transport₂ replay₂ provenance₂ name₂ =>
          cases h
          rfl

instance inscriptionNoveltySocketBHistCarrier : BHistCarrier InscriptionNoveltySocketUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := inscriptionNoveltySocketToEventFlow
  fromEventFlow := inscriptionNoveltySocketFromEventFlow

instance inscriptionNoveltySocketChapterTasteGate :
    ChapterTasteGate InscriptionNoveltySocketUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      inscriptionNoveltySocketFromEventFlow (inscriptionNoveltySocketToEventFlow x) =
        some x
    exact inscriptionNoveltySocket_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (inscriptionNoveltySocketToEventFlow_injective heq)

instance inscriptionNoveltySocketFieldFaithful :
    FieldFaithful InscriptionNoveltySocketUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := inscriptionNoveltySocketFields
  field_faithful := inscriptionNoveltySocket_field_faithful

instance inscriptionNoveltySocketNontrivial : Nontrivial InscriptionNoveltySocketUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨InscriptionNoveltySocketUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      InscriptionNoveltySocketUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate InscriptionNoveltySocketUp :=
  -- BEDC touchpoint anchor: BHist BMark
  inscriptionNoveltySocketChapterTasteGate

theorem InscriptionNoveltySocketTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      inscriptionNoveltySocketDecodeBHist (inscriptionNoveltySocketEncodeBHist h) = h) ∧
      (∀ x : InscriptionNoveltySocketUp,
        inscriptionNoveltySocketFromEventFlow (inscriptionNoveltySocketToEventFlow x) =
          some x) ∧
        (∀ x y : InscriptionNoveltySocketUp,
          inscriptionNoveltySocketFields x = inscriptionNoveltySocketFields y → x = y) ∧
          (∃ x y : InscriptionNoveltySocketUp, x ≠ y) ∧
            inscriptionNoveltySocketEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact inscriptionNoveltySocket_decode_encode_bhist
  · constructor
    · exact inscriptionNoveltySocket_round_trip
    · constructor
      · exact inscriptionNoveltySocket_field_faithful
      · constructor
        · exact ⟨Nontrivial.witness_pair.1, Nontrivial.witness_pair.2.1,
            Nontrivial.witness_pair.2.2⟩
        · rfl

end BEDC.Derived.InscriptionNoveltySocketUp
