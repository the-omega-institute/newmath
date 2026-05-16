import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ContextWindowCommitmentUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ContextWindowCommitmentUp : Type where
  | mk :
      (scope prompt boundary refusal consumer transport routes provenance nameCert : BHist) →
      ContextWindowCommitmentUp
  deriving DecidableEq

def contextWindowCommitmentEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: contextWindowCommitmentEncodeBHist h
  | BHist.e1 h => BMark.b1 :: contextWindowCommitmentEncodeBHist h

def contextWindowCommitmentDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (contextWindowCommitmentDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (contextWindowCommitmentDecodeBHist tail)

def contextWindowCommitmentTag : Nat → RawEvent → Bool
  | Nat.zero, [] => false
  | Nat.zero, BMark.b0 :: tail =>
      match tail with
      | [] => true
      | _ :: _ => false
  | Nat.zero, BMark.b1 :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ _, BMark.b0 :: _ => false
  | Nat.succ n, BMark.b1 :: tail => contextWindowCommitmentTag n tail

private theorem contextWindowCommitmentDecode_encode_bhist :
    ∀ h : BHist,
      contextWindowCommitmentDecodeBHist
        (contextWindowCommitmentEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def contextWindowCommitmentToEventFlow :
    ContextWindowCommitmentUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ContextWindowCommitmentUp.mk scope prompt boundary refusal consumer transport routes
      provenance nameCert =>
      [[BMark.b0],
        contextWindowCommitmentEncodeBHist scope,
        [BMark.b1, BMark.b0],
        contextWindowCommitmentEncodeBHist prompt,
        [BMark.b1, BMark.b1, BMark.b0],
        contextWindowCommitmentEncodeBHist boundary,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        contextWindowCommitmentEncodeBHist refusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        contextWindowCommitmentEncodeBHist consumer,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        contextWindowCommitmentEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        contextWindowCommitmentEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        contextWindowCommitmentEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        contextWindowCommitmentEncodeBHist nameCert]

def contextWindowCommitmentFromEventFlow :
    EventFlow → Option ContextWindowCommitmentUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | tag0 :: tail0 =>
      match tail0 with
      | [] => none
      | scope :: tail1 =>
          match tail1 with
          | [] => none
          | tag10 :: tail2 =>
              match tail2 with
              | [] => none
              | prompt :: tail3 =>
                  match tail3 with
                  | [] => none
                  | tag110 :: tail4 =>
                      match tail4 with
                      | [] => none
                      | boundary :: tail5 =>
                          match tail5 with
                          | [] => none
                          | tag1110 :: tail6 =>
                              match tail6 with
                              | [] => none
                              | refusal :: tail7 =>
                                  match tail7 with
                                  | [] => none
                                  | tag11110 :: tail8 =>
                                      match tail8 with
                                      | [] => none
                                      | consumer :: tail9 =>
                                          match tail9 with
                                          | [] => none
                                          | tag111110 :: tail10 =>
                                              match tail10 with
                                              | [] => none
                                              | transport :: tail11 =>
                                                  match tail11 with
                                                  | [] => none
                                                  | tag1111110 :: tail12 =>
                                                      match tail12 with
                                                      | [] => none
                                                      | routes :: tail13 =>
                                                          match tail13 with
                                                          | [] => none
                                                          | tag11111110 :: tail14 =>
                                                              match tail14 with
                                                              | [] => none
                                                              | provenance :: tail15 =>
                                                                  match tail15 with
                                                                  | [] => none
                                                                  | tag111111110 :: tail16 =>
                                                                      match tail16 with
                                                                      | [] => none
                                                                      | nameCert :: tail17 =>
                                                                          match tail17 with
                                                                          | _ :: _ => none
                                                                          | [] =>
                                                                              match
                                                                                  contextWindowCommitmentTag 0 tag0 with
                                                                              | false => none
                                                                              | true =>
                                                                                  match
                                                                                      contextWindowCommitmentTag 1 tag10 with
                                                                                  | false => none
                                                                                  | true =>
                                                                                      match
                                                                                          contextWindowCommitmentTag 2 tag110 with
                                                                                      | false => none
                                                                                      | true =>
                                                                                          match
                                                                                              contextWindowCommitmentTag 3 tag1110 with
                                                                                          | false => none
                                                                                          | true =>
                                                                                              match
                                                                                                  contextWindowCommitmentTag 4 tag11110 with
                                                                                              | false => none
                                                                                              | true =>
                                                                                                  match
                                                                                                      contextWindowCommitmentTag 5 tag111110 with
                                                                                                  | false => none
                                                                                                  | true =>
                                                                                                      match
                                                                                                          contextWindowCommitmentTag 6 tag1111110 with
                                                                                                      | false => none
                                                                                                      | true =>
                                                                                                          match
                                                                                                              contextWindowCommitmentTag 7 tag11111110 with
                                                                                                          | false => none
                                                                                                          | true =>
                                                                                                              match
                                                                                                                  contextWindowCommitmentTag 8 tag111111110 with
                                                                                                              | false => none
                                                                                                              | true =>
                                                                                                                  some
                                                                                                                    (ContextWindowCommitmentUp.mk
                                                                                                                      (contextWindowCommitmentDecodeBHist scope)
                                                                                                                      (contextWindowCommitmentDecodeBHist prompt)
                                                                                                                      (contextWindowCommitmentDecodeBHist boundary)
                                                                                                                      (contextWindowCommitmentDecodeBHist refusal)
                                                                                                                      (contextWindowCommitmentDecodeBHist consumer)
                                                                                                                      (contextWindowCommitmentDecodeBHist transport)
                                                                                                                      (contextWindowCommitmentDecodeBHist routes)
                                                                                                                      (contextWindowCommitmentDecodeBHist provenance)
                                                                                                                      (contextWindowCommitmentDecodeBHist nameCert))

private theorem contextWindowCommitment_round_trip :
    ∀ x : ContextWindowCommitmentUp,
      contextWindowCommitmentFromEventFlow
        (contextWindowCommitmentToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk scope prompt boundary refusal consumer transport routes provenance nameCert =>
      change
        some
            (ContextWindowCommitmentUp.mk
              (contextWindowCommitmentDecodeBHist
                (contextWindowCommitmentEncodeBHist scope))
              (contextWindowCommitmentDecodeBHist
                (contextWindowCommitmentEncodeBHist prompt))
              (contextWindowCommitmentDecodeBHist
                (contextWindowCommitmentEncodeBHist boundary))
              (contextWindowCommitmentDecodeBHist
                (contextWindowCommitmentEncodeBHist refusal))
              (contextWindowCommitmentDecodeBHist
                (contextWindowCommitmentEncodeBHist consumer))
              (contextWindowCommitmentDecodeBHist
                (contextWindowCommitmentEncodeBHist transport))
              (contextWindowCommitmentDecodeBHist
                (contextWindowCommitmentEncodeBHist routes))
              (contextWindowCommitmentDecodeBHist
                (contextWindowCommitmentEncodeBHist provenance))
              (contextWindowCommitmentDecodeBHist
                (contextWindowCommitmentEncodeBHist nameCert))) =
          some
            (ContextWindowCommitmentUp.mk scope prompt boundary refusal consumer transport
              routes provenance nameCert)
      rw [contextWindowCommitmentDecode_encode_bhist scope]
      rw [contextWindowCommitmentDecode_encode_bhist prompt]
      rw [contextWindowCommitmentDecode_encode_bhist boundary]
      rw [contextWindowCommitmentDecode_encode_bhist refusal]
      rw [contextWindowCommitmentDecode_encode_bhist consumer]
      rw [contextWindowCommitmentDecode_encode_bhist transport]
      rw [contextWindowCommitmentDecode_encode_bhist routes]
      rw [contextWindowCommitmentDecode_encode_bhist provenance]
      rw [contextWindowCommitmentDecode_encode_bhist nameCert]

private theorem contextWindowCommitmentToEventFlow_injective
    {x y : ContextWindowCommitmentUp} :
    contextWindowCommitmentToEventFlow x =
      contextWindowCommitmentToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      contextWindowCommitmentFromEventFlow
          (contextWindowCommitmentToEventFlow x) =
        contextWindowCommitmentFromEventFlow
          (contextWindowCommitmentToEventFlow y) :=
    congrArg contextWindowCommitmentFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (contextWindowCommitment_round_trip x).symm
      (Eq.trans hread (contextWindowCommitment_round_trip y)))

instance contextWindowCommitmentBHistCarrier :
    BHistCarrier ContextWindowCommitmentUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := contextWindowCommitmentToEventFlow
  fromEventFlow := contextWindowCommitmentFromEventFlow

instance contextWindowCommitmentChapterTasteGate :
    ChapterTasteGate ContextWindowCommitmentUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      contextWindowCommitmentFromEventFlow
          (contextWindowCommitmentToEventFlow x) =
        some x
    exact contextWindowCommitment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (contextWindowCommitmentToEventFlow_injective heq)

def taste_gate : ChapterTasteGate ContextWindowCommitmentUp :=
  -- BEDC touchpoint anchor: BHist BMark
  contextWindowCommitmentChapterTasteGate

instance contextWindowCommitmentNontrivial :
    Nontrivial ContextWindowCommitmentUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ContextWindowCommitmentUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ContextWindowCommitmentUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def contextWindowCommitmentFields : ContextWindowCommitmentUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ContextWindowCommitmentUp.mk scope prompt boundary refusal consumer transport routes
      provenance nameCert =>
      [scope, prompt, boundary, refusal, consumer, transport, routes, provenance, nameCert]

private theorem contextWindowCommitment_field_faithful :
    ∀ x y : ContextWindowCommitmentUp,
      contextWindowCommitmentFields x = contextWindowCommitmentFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk scope₁ prompt₁ boundary₁ refusal₁ consumer₁ transport₁ routes₁ provenance₁
      nameCert₁ =>
      cases y with
      | mk scope₂ prompt₂ boundary₂ refusal₂ consumer₂ transport₂ routes₂ provenance₂
          nameCert₂ =>
          cases h
          rfl

instance contextWindowCommitmentFieldFaithful :
    FieldFaithful ContextWindowCommitmentUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := contextWindowCommitmentFields
  field_faithful := contextWindowCommitment_field_faithful

theorem ContextWindowCommitmentTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      contextWindowCommitmentDecodeBHist
        (contextWindowCommitmentEncodeBHist h) = h) ∧
      (∀ x : ContextWindowCommitmentUp,
        contextWindowCommitmentFromEventFlow
          (contextWindowCommitmentToEventFlow x) = some x) ∧
        (∀ x y : ContextWindowCommitmentUp,
          contextWindowCommitmentToEventFlow x =
            contextWindowCommitmentToEventFlow y → x = y) ∧
          contextWindowCommitmentEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact contextWindowCommitmentDecode_encode_bhist
  · constructor
    · exact contextWindowCommitment_round_trip
    · constructor
      · intro x y heq
        exact contextWindowCommitmentToEventFlow_injective heq
      · rfl

end BEDC.Derived.ContextWindowCommitmentUp
