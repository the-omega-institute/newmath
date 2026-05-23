import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniqueChoicePrincipleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniqueChoicePrincipleUp : Type where
  | mk :
      (source relation existence uniquenessLedger deterministicReadback transport replay
        provenance localNameCert : BHist) →
        UniqueChoicePrincipleUp
  deriving DecidableEq

def uniqueChoicePrincipleEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniqueChoicePrincipleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniqueChoicePrincipleEncodeBHist h

def uniqueChoicePrincipleDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniqueChoicePrincipleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniqueChoicePrincipleDecodeBHist tail)

private theorem UniqueChoicePrincipleTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, uniqueChoicePrincipleDecodeBHist (uniqueChoicePrincipleEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def uniqueChoicePrincipleFields : UniqueChoicePrincipleUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniqueChoicePrincipleUp.mk source relation existence uniquenessLedger deterministicReadback
      transport replay provenance localNameCert =>
      [source, relation, existence, uniquenessLedger, deterministicReadback, transport, replay,
        provenance, localNameCert]

def uniqueChoicePrincipleToEventFlow : UniqueChoicePrincipleUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (uniqueChoicePrincipleFields x).map uniqueChoicePrincipleEncodeBHist

def uniqueChoicePrincipleFromEventFlow : EventFlow → Option UniqueChoicePrincipleUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | source :: rest0 =>
      match rest0 with
      | [] => none
      | relation :: rest1 =>
          match rest1 with
          | [] => none
          | existence :: rest2 =>
              match rest2 with
              | [] => none
              | uniquenessLedger :: rest3 =>
                  match rest3 with
                  | [] => none
                  | deterministicReadback :: rest4 =>
                      match rest4 with
                      | [] => none
                      | transport :: rest5 =>
                          match rest5 with
                          | [] => none
                          | replay :: rest6 =>
                              match rest6 with
                              | [] => none
                              | provenance :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | localNameCert :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (UniqueChoicePrincipleUp.mk
                                              (uniqueChoicePrincipleDecodeBHist source)
                                              (uniqueChoicePrincipleDecodeBHist relation)
                                              (uniqueChoicePrincipleDecodeBHist existence)
                                              (uniqueChoicePrincipleDecodeBHist uniquenessLedger)
                                              (uniqueChoicePrincipleDecodeBHist
                                                deterministicReadback)
                                              (uniqueChoicePrincipleDecodeBHist transport)
                                              (uniqueChoicePrincipleDecodeBHist replay)
                                              (uniqueChoicePrincipleDecodeBHist provenance)
                                              (uniqueChoicePrincipleDecodeBHist localNameCert))
                                      | _ :: _ => none

private theorem UniqueChoicePrincipleTasteGate_single_carrier_alignment_round_trip :
    ∀ x : UniqueChoicePrincipleUp,
      uniqueChoicePrincipleFromEventFlow (uniqueChoicePrincipleToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source relation existence uniquenessLedger deterministicReadback transport replay
      provenance localNameCert =>
      change
        some
          (UniqueChoicePrincipleUp.mk
            (uniqueChoicePrincipleDecodeBHist (uniqueChoicePrincipleEncodeBHist source))
            (uniqueChoicePrincipleDecodeBHist (uniqueChoicePrincipleEncodeBHist relation))
            (uniqueChoicePrincipleDecodeBHist (uniqueChoicePrincipleEncodeBHist existence))
            (uniqueChoicePrincipleDecodeBHist
              (uniqueChoicePrincipleEncodeBHist uniquenessLedger))
            (uniqueChoicePrincipleDecodeBHist
              (uniqueChoicePrincipleEncodeBHist deterministicReadback))
            (uniqueChoicePrincipleDecodeBHist (uniqueChoicePrincipleEncodeBHist transport))
            (uniqueChoicePrincipleDecodeBHist (uniqueChoicePrincipleEncodeBHist replay))
            (uniqueChoicePrincipleDecodeBHist (uniqueChoicePrincipleEncodeBHist provenance))
            (uniqueChoicePrincipleDecodeBHist (uniqueChoicePrincipleEncodeBHist localNameCert))) =
          some
            (UniqueChoicePrincipleUp.mk source relation existence uniquenessLedger
              deterministicReadback transport replay provenance localNameCert)
      rw [UniqueChoicePrincipleTasteGate_single_carrier_alignment_decode_encode source,
        UniqueChoicePrincipleTasteGate_single_carrier_alignment_decode_encode relation,
        UniqueChoicePrincipleTasteGate_single_carrier_alignment_decode_encode existence,
        UniqueChoicePrincipleTasteGate_single_carrier_alignment_decode_encode uniquenessLedger,
        UniqueChoicePrincipleTasteGate_single_carrier_alignment_decode_encode deterministicReadback,
        UniqueChoicePrincipleTasteGate_single_carrier_alignment_decode_encode transport,
        UniqueChoicePrincipleTasteGate_single_carrier_alignment_decode_encode replay,
        UniqueChoicePrincipleTasteGate_single_carrier_alignment_decode_encode provenance,
        UniqueChoicePrincipleTasteGate_single_carrier_alignment_decode_encode localNameCert]

private theorem UniqueChoicePrincipleTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : UniqueChoicePrincipleUp} :
    uniqueChoicePrincipleToEventFlow x = uniqueChoicePrincipleToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniqueChoicePrincipleFromEventFlow (uniqueChoicePrincipleToEventFlow x) =
        uniqueChoicePrincipleFromEventFlow (uniqueChoicePrincipleToEventFlow y) :=
    congrArg uniqueChoicePrincipleFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (UniqueChoicePrincipleTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (UniqueChoicePrincipleTasteGate_single_carrier_alignment_round_trip y)))

private theorem UniqueChoicePrincipleTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : UniqueChoicePrincipleUp, uniqueChoicePrincipleFields x =
      uniqueChoicePrincipleFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk source₁ relation₁ existence₁ uniquenessLedger₁ deterministicReadback₁ transport₁ replay₁
      provenance₁ localNameCert₁ =>
      cases y with
      | mk source₂ relation₂ existence₂ uniquenessLedger₂ deterministicReadback₂ transport₂
          replay₂ provenance₂ localNameCert₂ =>
          injection hfields with hSource tail0
          injection tail0 with hRelation tail1
          injection tail1 with hExistence tail2
          injection tail2 with hUniquenessLedger tail3
          injection tail3 with hDeterministicReadback tail4
          injection tail4 with hTransport tail5
          injection tail5 with hReplay tail6
          injection tail6 with hProvenance tail7
          injection tail7 with hLocalNameCert _
          subst hSource
          subst hRelation
          subst hExistence
          subst hUniquenessLedger
          subst hDeterministicReadback
          subst hTransport
          subst hReplay
          subst hProvenance
          subst hLocalNameCert
          rfl

instance UniqueChoicePrincipleTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier UniqueChoicePrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniqueChoicePrincipleToEventFlow
  fromEventFlow := uniqueChoicePrincipleFromEventFlow

instance UniqueChoicePrincipleTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate UniqueChoicePrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change uniqueChoicePrincipleFromEventFlow (uniqueChoicePrincipleToEventFlow x) = some x
    exact UniqueChoicePrincipleTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (UniqueChoicePrincipleTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance UniqueChoicePrincipleTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful UniqueChoicePrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := uniqueChoicePrincipleFields
  field_faithful := UniqueChoicePrincipleTasteGate_single_carrier_alignment_fields_faithful

instance UniqueChoicePrincipleTasteGate_single_carrier_alignment_Nontrivial :
    Nontrivial UniqueChoicePrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UniqueChoicePrincipleUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      UniqueChoicePrincipleUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def UniqueChoicePrincipleTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate UniqueChoicePrincipleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  UniqueChoicePrincipleTasteGate_single_carrier_alignment_ChapterTasteGate

theorem UniqueChoicePrincipleTasteGate_single_carrier_alignment :
    (∀ h : BHist, uniqueChoicePrincipleDecodeBHist (uniqueChoicePrincipleEncodeBHist h) = h) ∧
      (∀ x : UniqueChoicePrincipleUp,
        uniqueChoicePrincipleFromEventFlow (uniqueChoicePrincipleToEventFlow x) = some x) ∧
        (∀ x y : UniqueChoicePrincipleUp,
          uniqueChoicePrincipleToEventFlow x = uniqueChoicePrincipleToEventFlow y → x = y) ∧
          uniqueChoicePrincipleEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact UniqueChoicePrincipleTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact UniqueChoicePrincipleTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact UniqueChoicePrincipleTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · rfl

end BEDC.Derived.UniqueChoicePrincipleUp
