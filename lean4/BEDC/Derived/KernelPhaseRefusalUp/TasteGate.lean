import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KernelPhaseRefusalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KernelPhaseRefusalUp : Type where
  | mk :
      (phase target blocker refusal admissibility transport continuation provenance
        localName : BHist) →
        KernelPhaseRefusalUp
  deriving DecidableEq

def kernelPhaseRefusalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kernelPhaseRefusalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kernelPhaseRefusalEncodeBHist h

def kernelPhaseRefusalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kernelPhaseRefusalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kernelPhaseRefusalDecodeBHist tail)

private theorem KernelPhaseRefusalTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, kernelPhaseRefusalDecodeBHist (kernelPhaseRefusalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def kernelPhaseRefusalFields : KernelPhaseRefusalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | KernelPhaseRefusalUp.mk phase target blocker refusal admissibility transport continuation
      provenance localName =>
      [phase, target, blocker, refusal, admissibility, transport, continuation, provenance,
        localName]

def kernelPhaseRefusalToEventFlow : KernelPhaseRefusalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (kernelPhaseRefusalFields x).map kernelPhaseRefusalEncodeBHist

def kernelPhaseRefusalFromEventFlow : EventFlow → Option KernelPhaseRefusalUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | phase :: rest0 =>
      match rest0 with
      | [] => none
      | target :: rest1 =>
          match rest1 with
          | [] => none
          | blocker :: rest2 =>
              match rest2 with
              | [] => none
              | refusal :: rest3 =>
                  match rest3 with
                  | [] => none
                  | admissibility :: rest4 =>
                      match rest4 with
                      | [] => none
                      | transport :: rest5 =>
                          match rest5 with
                          | [] => none
                          | continuation :: rest6 =>
                              match rest6 with
                              | [] => none
                              | provenance :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | localName :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (KernelPhaseRefusalUp.mk
                                              (kernelPhaseRefusalDecodeBHist phase)
                                              (kernelPhaseRefusalDecodeBHist target)
                                              (kernelPhaseRefusalDecodeBHist blocker)
                                              (kernelPhaseRefusalDecodeBHist refusal)
                                              (kernelPhaseRefusalDecodeBHist admissibility)
                                              (kernelPhaseRefusalDecodeBHist transport)
                                              (kernelPhaseRefusalDecodeBHist continuation)
                                              (kernelPhaseRefusalDecodeBHist provenance)
                                              (kernelPhaseRefusalDecodeBHist localName))
                                      | _ :: _ => none

private theorem KernelPhaseRefusalTasteGate_single_carrier_alignment_round_trip :
    ∀ x : KernelPhaseRefusalUp,
      kernelPhaseRefusalFromEventFlow (kernelPhaseRefusalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk phase target blocker refusal admissibility transport continuation provenance localName =>
      change
        some
          (KernelPhaseRefusalUp.mk
            (kernelPhaseRefusalDecodeBHist (kernelPhaseRefusalEncodeBHist phase))
            (kernelPhaseRefusalDecodeBHist (kernelPhaseRefusalEncodeBHist target))
            (kernelPhaseRefusalDecodeBHist (kernelPhaseRefusalEncodeBHist blocker))
            (kernelPhaseRefusalDecodeBHist (kernelPhaseRefusalEncodeBHist refusal))
            (kernelPhaseRefusalDecodeBHist (kernelPhaseRefusalEncodeBHist admissibility))
            (kernelPhaseRefusalDecodeBHist (kernelPhaseRefusalEncodeBHist transport))
            (kernelPhaseRefusalDecodeBHist (kernelPhaseRefusalEncodeBHist continuation))
            (kernelPhaseRefusalDecodeBHist (kernelPhaseRefusalEncodeBHist provenance))
            (kernelPhaseRefusalDecodeBHist (kernelPhaseRefusalEncodeBHist localName))) =
          some
            (KernelPhaseRefusalUp.mk phase target blocker refusal admissibility transport
              continuation provenance localName)
      rw [KernelPhaseRefusalTasteGate_single_carrier_alignment_decode_encode phase,
        KernelPhaseRefusalTasteGate_single_carrier_alignment_decode_encode target,
        KernelPhaseRefusalTasteGate_single_carrier_alignment_decode_encode blocker,
        KernelPhaseRefusalTasteGate_single_carrier_alignment_decode_encode refusal,
        KernelPhaseRefusalTasteGate_single_carrier_alignment_decode_encode admissibility,
        KernelPhaseRefusalTasteGate_single_carrier_alignment_decode_encode transport,
        KernelPhaseRefusalTasteGate_single_carrier_alignment_decode_encode continuation,
        KernelPhaseRefusalTasteGate_single_carrier_alignment_decode_encode provenance,
        KernelPhaseRefusalTasteGate_single_carrier_alignment_decode_encode localName]

private theorem KernelPhaseRefusalTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : KernelPhaseRefusalUp} :
    kernelPhaseRefusalToEventFlow x = kernelPhaseRefusalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      kernelPhaseRefusalFromEventFlow (kernelPhaseRefusalToEventFlow x) =
        kernelPhaseRefusalFromEventFlow (kernelPhaseRefusalToEventFlow y) :=
    congrArg kernelPhaseRefusalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (KernelPhaseRefusalTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (KernelPhaseRefusalTasteGate_single_carrier_alignment_round_trip y)))

private theorem KernelPhaseRefusalTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : KernelPhaseRefusalUp,
      kernelPhaseRefusalFields x = kernelPhaseRefusalFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk phase₁ target₁ blocker₁ refusal₁ admissibility₁ transport₁ continuation₁ provenance₁
      localName₁ =>
      cases y with
      | mk phase₂ target₂ blocker₂ refusal₂ admissibility₂ transport₂ continuation₂ provenance₂
          localName₂ =>
          injection hfields with hPhase tail0
          injection tail0 with hTarget tail1
          injection tail1 with hBlocker tail2
          injection tail2 with hRefusal tail3
          injection tail3 with hAdmissibility tail4
          injection tail4 with hTransport tail5
          injection tail5 with hContinuation tail6
          injection tail6 with hProvenance tail7
          injection tail7 with hLocalName _
          subst hPhase
          subst hTarget
          subst hBlocker
          subst hRefusal
          subst hAdmissibility
          subst hTransport
          subst hContinuation
          subst hProvenance
          subst hLocalName
          rfl

instance kernelPhaseRefusalBHistCarrier : BHistCarrier KernelPhaseRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kernelPhaseRefusalToEventFlow
  fromEventFlow := kernelPhaseRefusalFromEventFlow

instance kernelPhaseRefusalChapterTasteGate : ChapterTasteGate KernelPhaseRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change kernelPhaseRefusalFromEventFlow (kernelPhaseRefusalToEventFlow x) = some x
    exact KernelPhaseRefusalTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (KernelPhaseRefusalTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance kernelPhaseRefusalFieldFaithful : FieldFaithful KernelPhaseRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := kernelPhaseRefusalFields
  field_faithful := KernelPhaseRefusalTasteGate_single_carrier_alignment_fields_faithful

instance kernelPhaseRefusalNontrivial : Nontrivial KernelPhaseRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨KernelPhaseRefusalUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      KernelPhaseRefusalUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate KernelPhaseRefusalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  kernelPhaseRefusalChapterTasteGate

theorem KernelPhaseRefusalTasteGate_single_carrier_alignment :
    (∀ h : BHist, kernelPhaseRefusalDecodeBHist (kernelPhaseRefusalEncodeBHist h) = h) ∧
      (∀ x : KernelPhaseRefusalUp,
        kernelPhaseRefusalFromEventFlow (kernelPhaseRefusalToEventFlow x) = some x) ∧
        (∀ x y : KernelPhaseRefusalUp,
          kernelPhaseRefusalToEventFlow x = kernelPhaseRefusalToEventFlow y → x = y) ∧
          kernelPhaseRefusalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨KernelPhaseRefusalTasteGate_single_carrier_alignment_decode_encode,
      KernelPhaseRefusalTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        KernelPhaseRefusalTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.KernelPhaseRefusalUp
