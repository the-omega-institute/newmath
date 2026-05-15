import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RelationalFrameAuditUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RelationalFrameAuditUp : Type where
  | mk :
      (multiHist observerA observerB request symmetry causal rate refusal transport
        continuation provenance name : BHist) →
      RelationalFrameAuditUp
  deriving DecidableEq

def relationalFrameAuditEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: relationalFrameAuditEncodeBHist h
  | BHist.e1 h => BMark.b1 :: relationalFrameAuditEncodeBHist h

def relationalFrameAuditDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (relationalFrameAuditDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (relationalFrameAuditDecodeBHist tail)

private theorem relationalFrameAuditDecode_encode_bhist :
    ∀ h : BHist,
      relationalFrameAuditDecodeBHist (relationalFrameAuditEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def relationalFrameAuditFields : RelationalFrameAuditUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RelationalFrameAuditUp.mk multiHist observerA observerB request symmetry causal rate
      refusal transport continuation provenance name =>
      [multiHist, observerA, observerB, request, symmetry, causal, rate, refusal, transport,
        continuation, provenance, name]

def relationalFrameAuditToEventFlow : RelationalFrameAuditUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RelationalFrameAuditUp.mk multiHist observerA observerB request symmetry causal rate
      refusal transport continuation provenance name =>
      [[BMark.b0],
        relationalFrameAuditEncodeBHist multiHist,
        [BMark.b1, BMark.b0],
        relationalFrameAuditEncodeBHist observerA,
        [BMark.b1, BMark.b1, BMark.b0],
        relationalFrameAuditEncodeBHist observerB,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        relationalFrameAuditEncodeBHist request,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        relationalFrameAuditEncodeBHist symmetry,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        relationalFrameAuditEncodeBHist causal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        relationalFrameAuditEncodeBHist rate,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        relationalFrameAuditEncodeBHist refusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        relationalFrameAuditEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        relationalFrameAuditEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        relationalFrameAuditEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        relationalFrameAuditEncodeBHist name]

private def relationalFrameAuditEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => relationalFrameAuditEventAtDefault index rest

def relationalFrameAuditFromEventFlow :
    EventFlow → Option RelationalFrameAuditUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (RelationalFrameAuditUp.mk
        (relationalFrameAuditDecodeBHist (relationalFrameAuditEventAtDefault 1 ef))
        (relationalFrameAuditDecodeBHist (relationalFrameAuditEventAtDefault 3 ef))
        (relationalFrameAuditDecodeBHist (relationalFrameAuditEventAtDefault 5 ef))
        (relationalFrameAuditDecodeBHist (relationalFrameAuditEventAtDefault 7 ef))
        (relationalFrameAuditDecodeBHist (relationalFrameAuditEventAtDefault 9 ef))
        (relationalFrameAuditDecodeBHist (relationalFrameAuditEventAtDefault 11 ef))
        (relationalFrameAuditDecodeBHist (relationalFrameAuditEventAtDefault 13 ef))
        (relationalFrameAuditDecodeBHist (relationalFrameAuditEventAtDefault 15 ef))
        (relationalFrameAuditDecodeBHist (relationalFrameAuditEventAtDefault 17 ef))
        (relationalFrameAuditDecodeBHist (relationalFrameAuditEventAtDefault 19 ef))
        (relationalFrameAuditDecodeBHist (relationalFrameAuditEventAtDefault 21 ef))
        (relationalFrameAuditDecodeBHist (relationalFrameAuditEventAtDefault 23 ef)))

private theorem relationalFrameAudit_round_trip :
    ∀ x : RelationalFrameAuditUp,
      relationalFrameAuditFromEventFlow (relationalFrameAuditToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk multiHist observerA observerB request symmetry causal rate refusal transport
      continuation provenance name =>
      change
        some
            (RelationalFrameAuditUp.mk
              (relationalFrameAuditDecodeBHist
                (relationalFrameAuditEncodeBHist multiHist))
              (relationalFrameAuditDecodeBHist
                (relationalFrameAuditEncodeBHist observerA))
              (relationalFrameAuditDecodeBHist
                (relationalFrameAuditEncodeBHist observerB))
              (relationalFrameAuditDecodeBHist
                (relationalFrameAuditEncodeBHist request))
              (relationalFrameAuditDecodeBHist
                (relationalFrameAuditEncodeBHist symmetry))
              (relationalFrameAuditDecodeBHist
                (relationalFrameAuditEncodeBHist causal))
              (relationalFrameAuditDecodeBHist
                (relationalFrameAuditEncodeBHist rate))
              (relationalFrameAuditDecodeBHist
                (relationalFrameAuditEncodeBHist refusal))
              (relationalFrameAuditDecodeBHist
                (relationalFrameAuditEncodeBHist transport))
              (relationalFrameAuditDecodeBHist
                (relationalFrameAuditEncodeBHist continuation))
              (relationalFrameAuditDecodeBHist
                (relationalFrameAuditEncodeBHist provenance))
              (relationalFrameAuditDecodeBHist
                (relationalFrameAuditEncodeBHist name))) =
          some
            (RelationalFrameAuditUp.mk multiHist observerA observerB request symmetry causal
              rate refusal transport continuation provenance name)
      rw [relationalFrameAuditDecode_encode_bhist multiHist,
        relationalFrameAuditDecode_encode_bhist observerA,
        relationalFrameAuditDecode_encode_bhist observerB,
        relationalFrameAuditDecode_encode_bhist request,
        relationalFrameAuditDecode_encode_bhist symmetry,
        relationalFrameAuditDecode_encode_bhist causal,
        relationalFrameAuditDecode_encode_bhist rate,
        relationalFrameAuditDecode_encode_bhist refusal,
        relationalFrameAuditDecode_encode_bhist transport,
        relationalFrameAuditDecode_encode_bhist continuation,
        relationalFrameAuditDecode_encode_bhist provenance,
        relationalFrameAuditDecode_encode_bhist name]

private theorem relationalFrameAuditToEventFlow_injective
    {x y : RelationalFrameAuditUp} :
    relationalFrameAuditToEventFlow x = relationalFrameAuditToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      relationalFrameAuditFromEventFlow (relationalFrameAuditToEventFlow x) =
        relationalFrameAuditFromEventFlow (relationalFrameAuditToEventFlow y) :=
    congrArg relationalFrameAuditFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (relationalFrameAudit_round_trip x).symm
      (Eq.trans hread (relationalFrameAudit_round_trip y)))

private theorem relationalFrameAudit_field_faithful :
    ∀ x y : RelationalFrameAuditUp,
      relationalFrameAuditFields x = relationalFrameAuditFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk multiHist₁ observerA₁ observerB₁ request₁ symmetry₁ causal₁ rate₁ refusal₁
      transport₁ continuation₁ provenance₁ name₁ =>
      cases y with
      | mk multiHist₂ observerA₂ observerB₂ request₂ symmetry₂ causal₂ rate₂ refusal₂
          transport₂ continuation₂ provenance₂ name₂ =>
          cases h
          rfl

instance relationalFrameAuditBHistCarrier :
    BHistCarrier RelationalFrameAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := relationalFrameAuditToEventFlow
  fromEventFlow := relationalFrameAuditFromEventFlow

instance relationalFrameAuditChapterTasteGate :
    ChapterTasteGate RelationalFrameAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change relationalFrameAuditFromEventFlow
        (relationalFrameAuditToEventFlow x) = some x
    exact relationalFrameAudit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (relationalFrameAuditToEventFlow_injective heq)

instance relationalFrameAuditFieldFaithful :
    FieldFaithful RelationalFrameAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := relationalFrameAuditFields
  field_faithful := relationalFrameAudit_field_faithful

instance relationalFrameAuditNontrivial :
    Nontrivial RelationalFrameAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RelationalFrameAuditUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      RelationalFrameAuditUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RelationalFrameAuditUp :=
  -- BEDC touchpoint anchor: BHist BMark
  relationalFrameAuditChapterTasteGate

theorem RelationalFrameAuditTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier RelationalFrameAuditUp) ∧
      Nonempty (ChapterTasteGate RelationalFrameAuditUp) ∧
      Nonempty (FieldFaithful RelationalFrameAuditUp) ∧
      Nonempty (Nontrivial RelationalFrameAuditUp) ∧
      relationalFrameAuditEncodeBHist BHist.Empty = ([] : RawEvent) ∧
      relationalFrameAuditEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨⟨relationalFrameAuditBHistCarrier⟩,
      ⟨relationalFrameAuditChapterTasteGate⟩,
      ⟨relationalFrameAuditFieldFaithful⟩,
      ⟨relationalFrameAuditNontrivial⟩,
      rfl,
      rfl⟩

end BEDC.Derived.RelationalFrameAuditUp
