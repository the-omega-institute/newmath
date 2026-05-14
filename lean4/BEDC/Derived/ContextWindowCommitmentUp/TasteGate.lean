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
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: contextWindowCommitmentEncodeBHist h
  | BHist.e1 h => BMark.b1 :: contextWindowCommitmentEncodeBHist h

def contextWindowCommitmentDecodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (contextWindowCommitmentDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (contextWindowCommitmentDecodeBHist tail)

private theorem contextWindowCommitmentDecode_encode_bhist :
    ∀ h : BHist,
      contextWindowCommitmentDecodeBHist
        (contextWindowCommitmentEncodeBHist h) = h := by
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
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | scope :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | prompt :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | boundary :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | refusal :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | consumer :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transport :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | routes :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | nameCert ::
                                                                          rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (ContextWindowCommitmentUp.mk
                                                                                  (contextWindowCommitmentDecodeBHist
                                                                                    scope)
                                                                                  (contextWindowCommitmentDecodeBHist
                                                                                    prompt)
                                                                                  (contextWindowCommitmentDecodeBHist
                                                                                    boundary)
                                                                                  (contextWindowCommitmentDecodeBHist
                                                                                    refusal)
                                                                                  (contextWindowCommitmentDecodeBHist
                                                                                    consumer)
                                                                                  (contextWindowCommitmentDecodeBHist
                                                                                    transport)
                                                                                  (contextWindowCommitmentDecodeBHist
                                                                                    routes)
                                                                                  (contextWindowCommitmentDecodeBHist
                                                                                    provenance)
                                                                                  (contextWindowCommitmentDecodeBHist
                                                                                    nameCert))
                                                                          | _ :: _ => none

private theorem contextWindowCommitment_round_trip :
    ∀ x : ContextWindowCommitmentUp,
      contextWindowCommitmentFromEventFlow
        (contextWindowCommitmentToEventFlow x) = some x := by
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
      rw [contextWindowCommitmentDecode_encode_bhist scope,
        contextWindowCommitmentDecode_encode_bhist prompt,
        contextWindowCommitmentDecode_encode_bhist boundary,
        contextWindowCommitmentDecode_encode_bhist refusal,
        contextWindowCommitmentDecode_encode_bhist consumer,
        contextWindowCommitmentDecode_encode_bhist transport,
        contextWindowCommitmentDecode_encode_bhist routes,
        contextWindowCommitmentDecode_encode_bhist provenance,
        contextWindowCommitmentDecode_encode_bhist nameCert]

private theorem contextWindowCommitmentToEventFlow_injective
    {x y : ContextWindowCommitmentUp} :
    contextWindowCommitmentToEventFlow x =
      contextWindowCommitmentToEventFlow y → x = y := by
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
  toEventFlow := contextWindowCommitmentToEventFlow
  fromEventFlow := contextWindowCommitmentFromEventFlow

instance contextWindowCommitmentChapterTasteGate :
    ChapterTasteGate ContextWindowCommitmentUp where
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
  contextWindowCommitmentChapterTasteGate

instance contextWindowCommitmentNontrivial :
    Nontrivial ContextWindowCommitmentUp where
  witness_pair :=
    ⟨ContextWindowCommitmentUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ContextWindowCommitmentUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

instance contextWindowCommitmentFieldFaithful :
    FieldFaithful ContextWindowCommitmentUp where
  fields := fun x =>
    match x with
    | ContextWindowCommitmentUp.mk scope prompt boundary refusal consumer transport routes
        provenance nameCert =>
        [scope, prompt, boundary, refusal, consumer, transport, routes, provenance, nameCert]
  field_faithful := by
    intro x y h
    cases x with
    | mk scope₁ prompt₁ boundary₁ refusal₁ consumer₁ transport₁ routes₁ provenance₁
        nameCert₁ =>
        cases y with
        | mk scope₂ prompt₂ boundary₂ refusal₂ consumer₂ transport₂ routes₂ provenance₂
            nameCert₂ =>
            cases h
            rfl

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
  constructor
  · exact contextWindowCommitmentDecode_encode_bhist
  · constructor
    · exact contextWindowCommitment_round_trip
    · constructor
      · intro x y heq
        exact contextWindowCommitmentToEventFlow_injective heq
      · rfl

end BEDC.Derived.ContextWindowCommitmentUp
