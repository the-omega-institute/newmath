import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PromptResponseTraceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PromptResponseTraceUp : Type where
  | mk
      (model sourceChannel prompt output auditRefusal observerInterface obstructionBoundary
        transport route provenance name : BHist) :
      PromptResponseTraceUp
  deriving DecidableEq

def promptResponseTraceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: promptResponseTraceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: promptResponseTraceEncodeBHist h

def promptResponseTraceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (promptResponseTraceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (promptResponseTraceDecodeBHist tail)

private theorem promptResponseTraceDecode_encode_bhist :
    ∀ h : BHist,
      promptResponseTraceDecodeBHist (promptResponseTraceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem promptResponseTrace_mk_congr
    {model model' sourceChannel sourceChannel' prompt prompt' output output'
      auditRefusal auditRefusal' observerInterface observerInterface' obstructionBoundary
      obstructionBoundary' transport transport' route route' provenance provenance' name name' :
      BHist}
    (hModel : model' = model)
    (hSourceChannel : sourceChannel' = sourceChannel)
    (hPrompt : prompt' = prompt)
    (hOutput : output' = output)
    (hAuditRefusal : auditRefusal' = auditRefusal)
    (hObserverInterface : observerInterface' = observerInterface)
    (hObstructionBoundary : obstructionBoundary' = obstructionBoundary)
    (hTransport : transport' = transport)
    (hRoute : route' = route)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    PromptResponseTraceUp.mk model' sourceChannel' prompt' output' auditRefusal'
        observerInterface' obstructionBoundary' transport' route' provenance' name' =
      PromptResponseTraceUp.mk model sourceChannel prompt output auditRefusal observerInterface
        obstructionBoundary transport route provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hModel
  cases hSourceChannel
  cases hPrompt
  cases hOutput
  cases hAuditRefusal
  cases hObserverInterface
  cases hObstructionBoundary
  cases hTransport
  cases hRoute
  cases hProvenance
  cases hName
  rfl

def promptResponseTraceToEventFlow : PromptResponseTraceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | PromptResponseTraceUp.mk model sourceChannel prompt output auditRefusal observerInterface
      obstructionBoundary transport route provenance name =>
      [[BMark.b0],
        promptResponseTraceEncodeBHist model,
        [BMark.b1, BMark.b0],
        promptResponseTraceEncodeBHist sourceChannel,
        [BMark.b1, BMark.b1, BMark.b0],
        promptResponseTraceEncodeBHist prompt,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        promptResponseTraceEncodeBHist output,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        promptResponseTraceEncodeBHist auditRefusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        promptResponseTraceEncodeBHist observerInterface,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        promptResponseTraceEncodeBHist obstructionBoundary,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        promptResponseTraceEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        promptResponseTraceEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        promptResponseTraceEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        promptResponseTraceEncodeBHist name]

private def promptResponseTraceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => promptResponseTraceEventAtDefault index rest

def promptResponseTraceFromEventFlow (ef : EventFlow) : Option PromptResponseTraceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PromptResponseTraceUp.mk
      (promptResponseTraceDecodeBHist (promptResponseTraceEventAtDefault 1 ef))
      (promptResponseTraceDecodeBHist (promptResponseTraceEventAtDefault 3 ef))
      (promptResponseTraceDecodeBHist (promptResponseTraceEventAtDefault 5 ef))
      (promptResponseTraceDecodeBHist (promptResponseTraceEventAtDefault 7 ef))
      (promptResponseTraceDecodeBHist (promptResponseTraceEventAtDefault 9 ef))
      (promptResponseTraceDecodeBHist (promptResponseTraceEventAtDefault 11 ef))
      (promptResponseTraceDecodeBHist (promptResponseTraceEventAtDefault 13 ef))
      (promptResponseTraceDecodeBHist (promptResponseTraceEventAtDefault 15 ef))
      (promptResponseTraceDecodeBHist (promptResponseTraceEventAtDefault 17 ef))
      (promptResponseTraceDecodeBHist (promptResponseTraceEventAtDefault 19 ef))
      (promptResponseTraceDecodeBHist (promptResponseTraceEventAtDefault 21 ef)))

private theorem promptResponseTrace_round_trip :
    ∀ x : PromptResponseTraceUp,
      promptResponseTraceFromEventFlow (promptResponseTraceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk model sourceChannel prompt output auditRefusal observerInterface obstructionBoundary
      transport route provenance name =>
      change
        some
          (PromptResponseTraceUp.mk
            (promptResponseTraceDecodeBHist (promptResponseTraceEncodeBHist model))
            (promptResponseTraceDecodeBHist (promptResponseTraceEncodeBHist sourceChannel))
            (promptResponseTraceDecodeBHist (promptResponseTraceEncodeBHist prompt))
            (promptResponseTraceDecodeBHist (promptResponseTraceEncodeBHist output))
            (promptResponseTraceDecodeBHist (promptResponseTraceEncodeBHist auditRefusal))
            (promptResponseTraceDecodeBHist
              (promptResponseTraceEncodeBHist observerInterface))
            (promptResponseTraceDecodeBHist
              (promptResponseTraceEncodeBHist obstructionBoundary))
            (promptResponseTraceDecodeBHist (promptResponseTraceEncodeBHist transport))
            (promptResponseTraceDecodeBHist (promptResponseTraceEncodeBHist route))
            (promptResponseTraceDecodeBHist (promptResponseTraceEncodeBHist provenance))
            (promptResponseTraceDecodeBHist (promptResponseTraceEncodeBHist name))) =
          some
            (PromptResponseTraceUp.mk model sourceChannel prompt output auditRefusal
              observerInterface obstructionBoundary transport route provenance name)
      exact
        congrArg some
          (promptResponseTrace_mk_congr
            (promptResponseTraceDecode_encode_bhist model)
            (promptResponseTraceDecode_encode_bhist sourceChannel)
            (promptResponseTraceDecode_encode_bhist prompt)
            (promptResponseTraceDecode_encode_bhist output)
            (promptResponseTraceDecode_encode_bhist auditRefusal)
            (promptResponseTraceDecode_encode_bhist observerInterface)
            (promptResponseTraceDecode_encode_bhist obstructionBoundary)
            (promptResponseTraceDecode_encode_bhist transport)
            (promptResponseTraceDecode_encode_bhist route)
            (promptResponseTraceDecode_encode_bhist provenance)
            (promptResponseTraceDecode_encode_bhist name))

private theorem promptResponseTraceToEventFlow_injective {x y : PromptResponseTraceUp} :
    promptResponseTraceToEventFlow x = promptResponseTraceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      promptResponseTraceFromEventFlow (promptResponseTraceToEventFlow x) =
        promptResponseTraceFromEventFlow (promptResponseTraceToEventFlow y) :=
    congrArg promptResponseTraceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (promptResponseTrace_round_trip x).symm
      (Eq.trans hread (promptResponseTrace_round_trip y)))

instance promptResponseTraceBHistCarrier : BHistCarrier PromptResponseTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := promptResponseTraceToEventFlow
  fromEventFlow := promptResponseTraceFromEventFlow

instance promptResponseTraceChapterTasteGate : ChapterTasteGate PromptResponseTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change promptResponseTraceFromEventFlow (promptResponseTraceToEventFlow x) = some x
    exact promptResponseTrace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (promptResponseTraceToEventFlow_injective heq)

instance promptResponseTraceFieldFaithful : FieldFaithful PromptResponseTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | PromptResponseTraceUp.mk model sourceChannel prompt output auditRefusal
        observerInterface obstructionBoundary transport route provenance name =>
        [model, sourceChannel, prompt, output, auditRefusal, observerInterface,
          obstructionBoundary, transport, route, provenance, name]
  field_faithful := by
    intro x y h
    cases x with
    | mk model₁ sourceChannel₁ prompt₁ output₁ auditRefusal₁ observerInterface₁
        obstructionBoundary₁ transport₁ route₁ provenance₁ name₁ =>
        cases y with
        | mk model₂ sourceChannel₂ prompt₂ output₂ auditRefusal₂ observerInterface₂
            obstructionBoundary₂ transport₂ route₂ provenance₂ name₂ =>
            injection h with hModel hRest₁
            injection hRest₁ with hSourceChannel hRest₂
            injection hRest₂ with hPrompt hRest₃
            injection hRest₃ with hOutput hRest₄
            injection hRest₄ with hAuditRefusal hRest₅
            injection hRest₅ with hObserverInterface hRest₆
            injection hRest₆ with hObstructionBoundary hRest₇
            injection hRest₇ with hTransport hRest₈
            injection hRest₈ with hRoute hRest₉
            injection hRest₉ with hProvenance hRest₁₀
            injection hRest₁₀ with hName _
            cases hModel
            cases hSourceChannel
            cases hPrompt
            cases hOutput
            cases hAuditRefusal
            cases hObserverInterface
            cases hObstructionBoundary
            cases hTransport
            cases hRoute
            cases hProvenance
            cases hName
            rfl

instance promptResponseTraceNontrivial : Nontrivial PromptResponseTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PromptResponseTraceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PromptResponseTraceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem PromptResponseTraceTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier PromptResponseTraceUp) ∧
      Nonempty (ChapterTasteGate PromptResponseTraceUp) ∧
        Nonempty (FieldFaithful PromptResponseTraceUp) ∧
          Nonempty (Nontrivial PromptResponseTraceUp) ∧
            promptResponseTraceEncodeBHist BHist.Empty = ([] : RawEvent) ∧
              promptResponseTraceEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨promptResponseTraceBHistCarrier⟩
  · constructor
    · exact ⟨promptResponseTraceChapterTasteGate⟩
    · constructor
      · exact ⟨promptResponseTraceFieldFaithful⟩
      · constructor
        · exact ⟨promptResponseTraceNontrivial⟩
        · constructor
          · rfl
          · rfl

end BEDC.Derived.PromptResponseTraceUp
