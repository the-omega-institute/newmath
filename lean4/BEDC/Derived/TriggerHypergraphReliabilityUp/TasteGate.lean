import BEDC.Derived.TriggerHypergraphReliabilityUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TriggerHypergraphReliabilityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def triggerHypergraphReliabilityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: triggerHypergraphReliabilityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: triggerHypergraphReliabilityEncodeBHist h

def triggerHypergraphReliabilityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (triggerHypergraphReliabilityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (triggerHypergraphReliabilityDecodeBHist tail)

private theorem triggerHypergraphReliabilityDecodeEncode :
    ∀ h : BHist,
      triggerHypergraphReliabilityDecodeBHist
          (triggerHypergraphReliabilityEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def triggerHypergraphReliabilityFields :
    TriggerHypergraphReliabilityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TriggerHypergraphReliabilityUp.mk B E R L W D A H C P N =>
      [B, E, R, L, W, D, A, H, C, P, N]

def triggerHypergraphReliabilityToEventFlow :
    TriggerHypergraphReliabilityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => triggerHypergraphReliabilityFields x |>.map triggerHypergraphReliabilityEncodeBHist

def triggerHypergraphReliabilityFromEventFlow :
    EventFlow → Option TriggerHypergraphReliabilityUp
  -- BEDC touchpoint anchor: BHist BMark
  | [B, E, R, L, W, D, A, H, C, P, N] =>
      some
        (TriggerHypergraphReliabilityUp.mk
          (triggerHypergraphReliabilityDecodeBHist B)
          (triggerHypergraphReliabilityDecodeBHist E)
          (triggerHypergraphReliabilityDecodeBHist R)
          (triggerHypergraphReliabilityDecodeBHist L)
          (triggerHypergraphReliabilityDecodeBHist W)
          (triggerHypergraphReliabilityDecodeBHist D)
          (triggerHypergraphReliabilityDecodeBHist A)
          (triggerHypergraphReliabilityDecodeBHist H)
          (triggerHypergraphReliabilityDecodeBHist C)
          (triggerHypergraphReliabilityDecodeBHist P)
          (triggerHypergraphReliabilityDecodeBHist N))
  | _ => none

private theorem triggerHypergraphReliabilityRoundTrip
    (x : TriggerHypergraphReliabilityUp) :
    triggerHypergraphReliabilityFromEventFlow
        (triggerHypergraphReliabilityToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk B E R L W D A H C P N =>
      change
        some
          (TriggerHypergraphReliabilityUp.mk
            (triggerHypergraphReliabilityDecodeBHist
              (triggerHypergraphReliabilityEncodeBHist B))
            (triggerHypergraphReliabilityDecodeBHist
              (triggerHypergraphReliabilityEncodeBHist E))
            (triggerHypergraphReliabilityDecodeBHist
              (triggerHypergraphReliabilityEncodeBHist R))
            (triggerHypergraphReliabilityDecodeBHist
              (triggerHypergraphReliabilityEncodeBHist L))
            (triggerHypergraphReliabilityDecodeBHist
              (triggerHypergraphReliabilityEncodeBHist W))
            (triggerHypergraphReliabilityDecodeBHist
              (triggerHypergraphReliabilityEncodeBHist D))
            (triggerHypergraphReliabilityDecodeBHist
              (triggerHypergraphReliabilityEncodeBHist A))
            (triggerHypergraphReliabilityDecodeBHist
              (triggerHypergraphReliabilityEncodeBHist H))
            (triggerHypergraphReliabilityDecodeBHist
              (triggerHypergraphReliabilityEncodeBHist C))
            (triggerHypergraphReliabilityDecodeBHist
              (triggerHypergraphReliabilityEncodeBHist P))
            (triggerHypergraphReliabilityDecodeBHist
              (triggerHypergraphReliabilityEncodeBHist N))) =
          some (TriggerHypergraphReliabilityUp.mk B E R L W D A H C P N)
      rw [
        triggerHypergraphReliabilityDecodeEncode B,
        triggerHypergraphReliabilityDecodeEncode E,
        triggerHypergraphReliabilityDecodeEncode R,
        triggerHypergraphReliabilityDecodeEncode L,
        triggerHypergraphReliabilityDecodeEncode W,
        triggerHypergraphReliabilityDecodeEncode D,
        triggerHypergraphReliabilityDecodeEncode A,
        triggerHypergraphReliabilityDecodeEncode H,
        triggerHypergraphReliabilityDecodeEncode C,
        triggerHypergraphReliabilityDecodeEncode P,
        triggerHypergraphReliabilityDecodeEncode N]

private theorem triggerHypergraphReliabilityToEventFlowInjective
    {x y : TriggerHypergraphReliabilityUp} :
    triggerHypergraphReliabilityToEventFlow x =
      triggerHypergraphReliabilityToEventFlow y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      triggerHypergraphReliabilityFromEventFlow
          (triggerHypergraphReliabilityToEventFlow x) =
        triggerHypergraphReliabilityFromEventFlow
          (triggerHypergraphReliabilityToEventFlow y) :=
    congrArg triggerHypergraphReliabilityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (triggerHypergraphReliabilityRoundTrip x).symm
      (Eq.trans hread (triggerHypergraphReliabilityRoundTrip y)))

private theorem triggerHypergraphReliabilityFieldsFaithful :
    ∀ x y : TriggerHypergraphReliabilityUp,
      triggerHypergraphReliabilityFields x = triggerHypergraphReliabilityFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B₁ E₁ R₁ L₁ W₁ D₁ A₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk B₂ E₂ R₂ L₂ W₂ D₂ A₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance triggerHypergraphReliabilityBHistCarrier :
    BHistCarrier TriggerHypergraphReliabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := triggerHypergraphReliabilityToEventFlow
  fromEventFlow := triggerHypergraphReliabilityFromEventFlow

instance triggerHypergraphReliabilityChapterTasteGate :
    ChapterTasteGate TriggerHypergraphReliabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      triggerHypergraphReliabilityFromEventFlow
          (triggerHypergraphReliabilityToEventFlow x) =
        some x
    exact triggerHypergraphReliabilityRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (triggerHypergraphReliabilityToEventFlowInjective heq)

instance triggerHypergraphReliabilityFieldFaithful :
    FieldFaithful TriggerHypergraphReliabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := triggerHypergraphReliabilityFields
  field_faithful := triggerHypergraphReliabilityFieldsFaithful

instance triggerHypergraphReliabilityNontrivial :
    Nontrivial TriggerHypergraphReliabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨TriggerHypergraphReliabilityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      TriggerHypergraphReliabilityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def triggerHypergraphReliabilityTasteGate :
    ChapterTasteGate TriggerHypergraphReliabilityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  triggerHypergraphReliabilityChapterTasteGate

end BEDC.Derived.TriggerHypergraphReliabilityUp
