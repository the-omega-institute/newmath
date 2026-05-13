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
  | [[BMark.b0], scope,
      [BMark.b1, BMark.b0], prompt,
      [BMark.b1, BMark.b1, BMark.b0], boundary,
      [BMark.b1, BMark.b1, BMark.b1, BMark.b0], refusal,
      [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0], consumer,
      [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0], transport,
      [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        routes,
      [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
        BMark.b0], provenance,
      [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
        BMark.b1, BMark.b0], nameCert] =>
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
  | _ => none

private theorem contextWindowCommitment_round_trip :
    ∀ x : ContextWindowCommitmentUp,
      contextWindowCommitmentFromEventFlow
        (contextWindowCommitmentToEventFlow x) = some x := by
  intro x
  cases x with
  | mk scope prompt boundary refusal consumer transport routes provenance nameCert =>
      simp [contextWindowCommitmentToEventFlow, contextWindowCommitmentFromEventFlow,
        contextWindowCommitmentDecode_encode_bhist]

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
