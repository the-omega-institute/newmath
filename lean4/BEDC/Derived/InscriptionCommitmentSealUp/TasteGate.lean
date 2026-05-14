import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.InscriptionCommitmentSealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive InscriptionCommitmentSealUp : Type where
  | mk : (source commitment consumer gap transport route provenance name : BHist) →
      InscriptionCommitmentSealUp
  deriving DecidableEq

def inscriptionCommitmentSealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: inscriptionCommitmentSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: inscriptionCommitmentSealEncodeBHist h

def inscriptionCommitmentSealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (inscriptionCommitmentSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (inscriptionCommitmentSealDecodeBHist tail)

private theorem inscriptionCommitmentSealDecodeEncodeBHist :
    ∀ h : BHist,
      inscriptionCommitmentSealDecodeBHist
        (inscriptionCommitmentSealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def inscriptionCommitmentSealFields : InscriptionCommitmentSealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | InscriptionCommitmentSealUp.mk source commitment consumer gap transport route provenance name =>
      [source, commitment, consumer, gap, transport, route, provenance, name]

def inscriptionCommitmentSealToEventFlow :
    InscriptionCommitmentSealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (inscriptionCommitmentSealFields x).map inscriptionCommitmentSealEncodeBHist

def inscriptionCommitmentSealFromEventFlow :
    EventFlow → Option InscriptionCommitmentSealUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | source :: rest0 =>
      match rest0 with
      | [] => none
      | commitment :: rest1 =>
          match rest1 with
          | [] => none
          | consumer :: rest2 =>
              match rest2 with
              | [] => none
              | gap :: rest3 =>
                  match rest3 with
                  | [] => none
                  | transport :: rest4 =>
                      match rest4 with
                      | [] => none
                      | route :: rest5 =>
                          match rest5 with
                          | [] => none
                          | provenance :: rest6 =>
                              match rest6 with
                              | [] => none
                              | name :: rest7 =>
                                  match rest7 with
                                  | [] =>
                                      some
                                        (InscriptionCommitmentSealUp.mk
                                          (inscriptionCommitmentSealDecodeBHist source)
                                          (inscriptionCommitmentSealDecodeBHist commitment)
                                          (inscriptionCommitmentSealDecodeBHist consumer)
                                          (inscriptionCommitmentSealDecodeBHist gap)
                                          (inscriptionCommitmentSealDecodeBHist transport)
                                          (inscriptionCommitmentSealDecodeBHist route)
                                          (inscriptionCommitmentSealDecodeBHist provenance)
                                          (inscriptionCommitmentSealDecodeBHist name))
                                  | _ :: _ => none

private theorem inscriptionCommitmentSeal_round_trip :
    ∀ x : InscriptionCommitmentSealUp,
      inscriptionCommitmentSealFromEventFlow
        (inscriptionCommitmentSealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source commitment consumer gap transport route provenance name =>
      change
        some
          (InscriptionCommitmentSealUp.mk
            (inscriptionCommitmentSealDecodeBHist
              (inscriptionCommitmentSealEncodeBHist source))
            (inscriptionCommitmentSealDecodeBHist
              (inscriptionCommitmentSealEncodeBHist commitment))
            (inscriptionCommitmentSealDecodeBHist
              (inscriptionCommitmentSealEncodeBHist consumer))
            (inscriptionCommitmentSealDecodeBHist
              (inscriptionCommitmentSealEncodeBHist gap))
            (inscriptionCommitmentSealDecodeBHist
              (inscriptionCommitmentSealEncodeBHist transport))
            (inscriptionCommitmentSealDecodeBHist
              (inscriptionCommitmentSealEncodeBHist route))
            (inscriptionCommitmentSealDecodeBHist
              (inscriptionCommitmentSealEncodeBHist provenance))
            (inscriptionCommitmentSealDecodeBHist
              (inscriptionCommitmentSealEncodeBHist name))) =
          some
            (InscriptionCommitmentSealUp.mk source commitment consumer gap transport route
              provenance name)
      rw [inscriptionCommitmentSealDecodeEncodeBHist source,
        inscriptionCommitmentSealDecodeEncodeBHist commitment,
        inscriptionCommitmentSealDecodeEncodeBHist consumer,
        inscriptionCommitmentSealDecodeEncodeBHist gap,
        inscriptionCommitmentSealDecodeEncodeBHist transport,
        inscriptionCommitmentSealDecodeEncodeBHist route,
        inscriptionCommitmentSealDecodeEncodeBHist provenance,
        inscriptionCommitmentSealDecodeEncodeBHist name]

private theorem inscriptionCommitmentSealToEventFlow_injective
    {x y : InscriptionCommitmentSealUp} :
    inscriptionCommitmentSealToEventFlow x =
      inscriptionCommitmentSealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      inscriptionCommitmentSealFromEventFlow (inscriptionCommitmentSealToEventFlow x) =
        inscriptionCommitmentSealFromEventFlow (inscriptionCommitmentSealToEventFlow y) :=
    congrArg inscriptionCommitmentSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (inscriptionCommitmentSeal_round_trip x).symm
      (Eq.trans hread (inscriptionCommitmentSeal_round_trip y)))

private theorem inscriptionCommitmentSeal_fields_faithful :
    ∀ x y : InscriptionCommitmentSealUp,
      inscriptionCommitmentSealFields x = inscriptionCommitmentSealFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk source₁ commitment₁ consumer₁ gap₁ transport₁ route₁ provenance₁ name₁ =>
      cases y with
      | mk source₂ commitment₂ consumer₂ gap₂ transport₂ route₂ provenance₂ name₂ =>
          injection hfields with hsource tail0
          injection tail0 with hcommitment tail1
          injection tail1 with hconsumer tail2
          injection tail2 with hgap tail3
          injection tail3 with htransport tail4
          injection tail4 with hroute tail5
          injection tail5 with hprovenance tail6
          injection tail6 with hname _
          subst hsource
          subst hcommitment
          subst hconsumer
          subst hgap
          subst htransport
          subst hroute
          subst hprovenance
          subst hname
          rfl

instance inscriptionCommitmentSealBHistCarrier :
    BHistCarrier InscriptionCommitmentSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := inscriptionCommitmentSealToEventFlow
  fromEventFlow := inscriptionCommitmentSealFromEventFlow

instance inscriptionCommitmentSealChapterTasteGate :
    ChapterTasteGate InscriptionCommitmentSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      inscriptionCommitmentSealFromEventFlow
        (inscriptionCommitmentSealToEventFlow x) = some x
    exact inscriptionCommitmentSeal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (inscriptionCommitmentSealToEventFlow_injective heq)

instance inscriptionCommitmentSealFieldFaithful :
    FieldFaithful InscriptionCommitmentSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := inscriptionCommitmentSealFields
  field_faithful := inscriptionCommitmentSeal_fields_faithful

theorem InscriptionCommitmentSealTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      inscriptionCommitmentSealDecodeBHist
        (inscriptionCommitmentSealEncodeBHist h) = h) ∧
      (∀ x : InscriptionCommitmentSealUp,
        inscriptionCommitmentSealFromEventFlow
          (inscriptionCommitmentSealToEventFlow x) = some x) ∧
        (∀ x y : InscriptionCommitmentSealUp,
          inscriptionCommitmentSealToEventFlow x =
            inscriptionCommitmentSealToEventFlow y → x = y) ∧
          inscriptionCommitmentSealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact inscriptionCommitmentSealDecodeEncodeBHist
  · constructor
    · exact inscriptionCommitmentSeal_round_trip
    · constructor
      · intro x y heq
        exact inscriptionCommitmentSealToEventFlow_injective heq
      · rfl

end BEDC.Derived.InscriptionCommitmentSealUp
