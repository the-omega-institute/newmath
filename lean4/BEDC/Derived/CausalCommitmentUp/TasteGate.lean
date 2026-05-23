import BEDC.Derived.CausalCommitmentUp
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CausalCommitmentUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CausalCommitmentUp : Type where
  | mk :
      (observed regularity gap forward transport continuation provenance localName : BHist) →
        CausalCommitmentUp
  deriving DecidableEq

def causalCommitmentEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: causalCommitmentEncodeBHist h
  | BHist.e1 h => BMark.b1 :: causalCommitmentEncodeBHist h

def causalCommitmentDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (causalCommitmentDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (causalCommitmentDecodeBHist tail)

private theorem causalCommitmentDecodeEncodeBHist :
    ∀ h : BHist, causalCommitmentDecodeBHist (causalCommitmentEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def causalCommitmentFields : CausalCommitmentUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CausalCommitmentUp.mk observed regularity gap forward transport continuation provenance
      localName =>
      [observed, regularity, gap, forward, transport, continuation, provenance, localName]

def causalCommitmentToEventFlow : CausalCommitmentUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (causalCommitmentFields x).map causalCommitmentEncodeBHist

def causalCommitmentFromEventFlow : EventFlow → Option CausalCommitmentUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | observed :: rest0 =>
      match rest0 with
      | [] => none
      | regularity :: rest1 =>
          match rest1 with
          | [] => none
          | gap :: rest2 =>
              match rest2 with
              | [] => none
              | forward :: rest3 =>
                  match rest3 with
                  | [] => none
                  | transport :: rest4 =>
                      match rest4 with
                      | [] => none
                      | continuation :: rest5 =>
                          match rest5 with
                          | [] => none
                          | provenance :: rest6 =>
                              match rest6 with
                              | [] => none
                              | localName :: rest7 =>
                                  match rest7 with
                                  | [] =>
                                      some
                                        (CausalCommitmentUp.mk
                                          (causalCommitmentDecodeBHist observed)
                                          (causalCommitmentDecodeBHist regularity)
                                          (causalCommitmentDecodeBHist gap)
                                          (causalCommitmentDecodeBHist forward)
                                          (causalCommitmentDecodeBHist transport)
                                          (causalCommitmentDecodeBHist continuation)
                                          (causalCommitmentDecodeBHist provenance)
                                          (causalCommitmentDecodeBHist localName))
                                  | _ :: _ => none

private theorem causalCommitment_round_trip :
    ∀ x : CausalCommitmentUp,
      causalCommitmentFromEventFlow (causalCommitmentToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk observed regularity gap forward transport continuation provenance localName =>
      change
        some
          (CausalCommitmentUp.mk
            (causalCommitmentDecodeBHist (causalCommitmentEncodeBHist observed))
            (causalCommitmentDecodeBHist (causalCommitmentEncodeBHist regularity))
            (causalCommitmentDecodeBHist (causalCommitmentEncodeBHist gap))
            (causalCommitmentDecodeBHist (causalCommitmentEncodeBHist forward))
            (causalCommitmentDecodeBHist (causalCommitmentEncodeBHist transport))
            (causalCommitmentDecodeBHist (causalCommitmentEncodeBHist continuation))
            (causalCommitmentDecodeBHist (causalCommitmentEncodeBHist provenance))
            (causalCommitmentDecodeBHist (causalCommitmentEncodeBHist localName))) =
          some
            (CausalCommitmentUp.mk observed regularity gap forward transport continuation
              provenance localName)
      rw [causalCommitmentDecodeEncodeBHist observed,
        causalCommitmentDecodeEncodeBHist regularity,
        causalCommitmentDecodeEncodeBHist gap,
        causalCommitmentDecodeEncodeBHist forward,
        causalCommitmentDecodeEncodeBHist transport,
        causalCommitmentDecodeEncodeBHist continuation,
        causalCommitmentDecodeEncodeBHist provenance,
        causalCommitmentDecodeEncodeBHist localName]

private theorem causalCommitmentToEventFlow_injective {x y : CausalCommitmentUp} :
    causalCommitmentToEventFlow x = causalCommitmentToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      causalCommitmentFromEventFlow (causalCommitmentToEventFlow x) =
        causalCommitmentFromEventFlow (causalCommitmentToEventFlow y) :=
    congrArg causalCommitmentFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (causalCommitment_round_trip x).symm
      (Eq.trans hread (causalCommitment_round_trip y)))

private theorem causalCommitment_fields_faithful :
    ∀ x y : CausalCommitmentUp, causalCommitmentFields x = causalCommitmentFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk observed₁ regularity₁ gap₁ forward₁ transport₁ continuation₁ provenance₁ localName₁ =>
      cases y with
      | mk observed₂ regularity₂ gap₂ forward₂ transport₂ continuation₂ provenance₂ localName₂ =>
          injection hfields with hobserved tail0
          injection tail0 with hregularity tail1
          injection tail1 with hgap tail2
          injection tail2 with hforward tail3
          injection tail3 with htransport tail4
          injection tail4 with hcontinuation tail5
          injection tail5 with hprovenance tail6
          injection tail6 with hlocalName _
          subst hobserved
          subst hregularity
          subst hgap
          subst hforward
          subst htransport
          subst hcontinuation
          subst hprovenance
          subst hlocalName
          rfl

instance causalCommitmentBHistCarrier : BHistCarrier CausalCommitmentUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := causalCommitmentToEventFlow
  fromEventFlow := causalCommitmentFromEventFlow

instance causalCommitmentChapterTasteGate : ChapterTasteGate CausalCommitmentUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change causalCommitmentFromEventFlow (causalCommitmentToEventFlow x) = some x
    exact causalCommitment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (causalCommitmentToEventFlow_injective heq)

instance causalCommitmentFieldFaithful : FieldFaithful CausalCommitmentUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := causalCommitmentFields
  field_faithful := causalCommitment_fields_faithful

instance causalCommitmentNontrivial : Nontrivial CausalCommitmentUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CausalCommitmentUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      CausalCommitmentUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CausalCommitmentUp :=
  -- BEDC touchpoint anchor: BHist BMark
  causalCommitmentChapterTasteGate

theorem CausalCommitmentTasteGate_single_carrier_alignment :
    (∀ h : BHist, causalCommitmentDecodeBHist (causalCommitmentEncodeBHist h) = h) ∧
      (∀ x : CausalCommitmentUp,
        causalCommitmentFromEventFlow (causalCommitmentToEventFlow x) = some x) ∧
        (∀ x y : CausalCommitmentUp,
          causalCommitmentToEventFlow x = causalCommitmentToEventFlow y → x = y) ∧
          causalCommitmentEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : CausalCommitmentUp,
              causalCommitmentFields x = causalCommitmentFields y → x = y) ∧
              (∃ x y : CausalCommitmentUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact causalCommitmentDecodeEncodeBHist
  · constructor
    · exact causalCommitment_round_trip
    · constructor
      · intro x y heq
        exact causalCommitmentToEventFlow_injective heq
      · constructor
        · rfl
        · constructor
          · exact causalCommitment_fields_faithful
          · exact
              ⟨CausalCommitmentUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
                CausalCommitmentUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
                by
                  intro h
                  cases h⟩

end BEDC.Derived.CausalCommitmentUp
