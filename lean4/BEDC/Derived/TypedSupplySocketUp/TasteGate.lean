import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TypedSupplySocketUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TypedSupplySocketUp : Type where
  | mk :
      (kind requestedSupply consumptionSite auditGate refusal transport continuation provenance
        localName : BHist) →
        TypedSupplySocketUp
  deriving DecidableEq

def typedSupplySocketEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: typedSupplySocketEncodeBHist h
  | BHist.e1 h => BMark.b1 :: typedSupplySocketEncodeBHist h

def typedSupplySocketDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (typedSupplySocketDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (typedSupplySocketDecodeBHist tail)

private theorem TypedSupplySocketTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, typedSupplySocketDecodeBHist (typedSupplySocketEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def typedSupplySocketFields : TypedSupplySocketUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TypedSupplySocketUp.mk kind requestedSupply consumptionSite auditGate refusal transport
      continuation provenance localName =>
      [kind, requestedSupply, consumptionSite, auditGate, refusal, transport, continuation,
        provenance, localName]

def typedSupplySocketToEventFlow : TypedSupplySocketUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (typedSupplySocketFields x).map typedSupplySocketEncodeBHist

def typedSupplySocketFromEventFlow : EventFlow → Option TypedSupplySocketUp
  -- BEDC touchpoint anchor: BHist BMark
  | kind :: requestedSupply :: consumptionSite :: auditGate :: refusal :: transport ::
      continuation :: provenance :: localName :: [] =>
      some
        (TypedSupplySocketUp.mk
          (typedSupplySocketDecodeBHist kind)
          (typedSupplySocketDecodeBHist requestedSupply)
          (typedSupplySocketDecodeBHist consumptionSite)
          (typedSupplySocketDecodeBHist auditGate)
          (typedSupplySocketDecodeBHist refusal)
          (typedSupplySocketDecodeBHist transport)
          (typedSupplySocketDecodeBHist continuation)
          (typedSupplySocketDecodeBHist provenance)
          (typedSupplySocketDecodeBHist localName))
  | _ => none

private theorem TypedSupplySocketTasteGate_single_carrier_alignment_round_trip :
    ∀ x : TypedSupplySocketUp,
      typedSupplySocketFromEventFlow (typedSupplySocketToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk kind requestedSupply consumptionSite auditGate refusal transport continuation provenance
      localName =>
      change
        some
          (TypedSupplySocketUp.mk
            (typedSupplySocketDecodeBHist (typedSupplySocketEncodeBHist kind))
            (typedSupplySocketDecodeBHist (typedSupplySocketEncodeBHist requestedSupply))
            (typedSupplySocketDecodeBHist (typedSupplySocketEncodeBHist consumptionSite))
            (typedSupplySocketDecodeBHist (typedSupplySocketEncodeBHist auditGate))
            (typedSupplySocketDecodeBHist (typedSupplySocketEncodeBHist refusal))
            (typedSupplySocketDecodeBHist (typedSupplySocketEncodeBHist transport))
            (typedSupplySocketDecodeBHist (typedSupplySocketEncodeBHist continuation))
            (typedSupplySocketDecodeBHist (typedSupplySocketEncodeBHist provenance))
            (typedSupplySocketDecodeBHist (typedSupplySocketEncodeBHist localName))) =
          some
            (TypedSupplySocketUp.mk kind requestedSupply consumptionSite auditGate refusal transport
              continuation provenance localName)
      rw [TypedSupplySocketTasteGate_single_carrier_alignment_decode_encode kind,
        TypedSupplySocketTasteGate_single_carrier_alignment_decode_encode requestedSupply,
        TypedSupplySocketTasteGate_single_carrier_alignment_decode_encode consumptionSite,
        TypedSupplySocketTasteGate_single_carrier_alignment_decode_encode auditGate,
        TypedSupplySocketTasteGate_single_carrier_alignment_decode_encode refusal,
        TypedSupplySocketTasteGate_single_carrier_alignment_decode_encode transport,
        TypedSupplySocketTasteGate_single_carrier_alignment_decode_encode continuation,
        TypedSupplySocketTasteGate_single_carrier_alignment_decode_encode provenance,
        TypedSupplySocketTasteGate_single_carrier_alignment_decode_encode localName]

private theorem TypedSupplySocketTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : TypedSupplySocketUp} :
    typedSupplySocketToEventFlow x = typedSupplySocketToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      typedSupplySocketFromEventFlow (typedSupplySocketToEventFlow x) =
        typedSupplySocketFromEventFlow (typedSupplySocketToEventFlow y) :=
    congrArg typedSupplySocketFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (TypedSupplySocketTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (TypedSupplySocketTasteGate_single_carrier_alignment_round_trip y)))

private theorem TypedSupplySocketTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : TypedSupplySocketUp,
      typedSupplySocketFields x = typedSupplySocketFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk kind₁ requestedSupply₁ consumptionSite₁ auditGate₁ refusal₁ transport₁ continuation₁
      provenance₁ localName₁ =>
      cases y with
      | mk kind₂ requestedSupply₂ consumptionSite₂ auditGate₂ refusal₂ transport₂ continuation₂
          provenance₂ localName₂ =>
          injection hfields with hKind tail0
          injection tail0 with hRequestedSupply tail1
          injection tail1 with hConsumptionSite tail2
          injection tail2 with hAuditGate tail3
          injection tail3 with hRefusal tail4
          injection tail4 with hTransport tail5
          injection tail5 with hContinuation tail6
          injection tail6 with hProvenance tail7
          injection tail7 with hLocalName _
          subst hKind
          subst hRequestedSupply
          subst hConsumptionSite
          subst hAuditGate
          subst hRefusal
          subst hTransport
          subst hContinuation
          subst hProvenance
          subst hLocalName
          rfl

instance typedSupplySocketBHistCarrier : BHistCarrier TypedSupplySocketUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := typedSupplySocketToEventFlow
  fromEventFlow := typedSupplySocketFromEventFlow

instance typedSupplySocketChapterTasteGate : ChapterTasteGate TypedSupplySocketUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change typedSupplySocketFromEventFlow (typedSupplySocketToEventFlow x) = some x
    exact TypedSupplySocketTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (TypedSupplySocketTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance typedSupplySocketFieldFaithful : FieldFaithful TypedSupplySocketUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := typedSupplySocketFields
  field_faithful := TypedSupplySocketTasteGate_single_carrier_alignment_fields_faithful

instance typedSupplySocketNontrivial : Nontrivial TypedSupplySocketUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨TypedSupplySocketUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      TypedSupplySocketUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate TypedSupplySocketUp :=
  -- BEDC touchpoint anchor: BHist BMark
  typedSupplySocketChapterTasteGate

theorem TypedSupplySocketTasteGate_single_carrier_alignment :
    (∀ h : BHist, typedSupplySocketDecodeBHist (typedSupplySocketEncodeBHist h) = h) ∧
      typedSupplySocketEncodeBHist BHist.Empty = ([] : List BMark) ∧
      (∀ x y : TypedSupplySocketUp,
        typedSupplySocketFields x = typedSupplySocketFields y → x = y) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨TypedSupplySocketTasteGate_single_carrier_alignment_decode_encode, rfl,
      TypedSupplySocketTasteGate_single_carrier_alignment_fields_faithful⟩

end BEDC.Derived.TypedSupplySocketUp
