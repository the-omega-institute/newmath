import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CannotClaimExportGateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CannotClaimExportGateUp : Type where
  | mk (registry refusal exportDecision exportGrade target audit transport continuation
      provenance name : BHist) : CannotClaimExportGateUp
  deriving DecidableEq

def cannotClaimExportGateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cannotClaimExportGateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cannotClaimExportGateEncodeBHist h

def cannotClaimExportGateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cannotClaimExportGateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cannotClaimExportGateDecodeBHist tail)

private theorem cannotClaimExportGate_decode_encode_bhist :
    ∀ h : BHist,
      cannotClaimExportGateDecodeBHist (cannotClaimExportGateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem cannotClaimExportGate_mk_congr
    {registry registry' refusal refusal' exportDecision exportDecision'
      exportGrade exportGrade' target target' audit audit' transport transport'
      continuation continuation' provenance provenance' name name' : BHist}
    (hRegistry : registry' = registry)
    (hRefusal : refusal' = refusal)
    (hExportDecision : exportDecision' = exportDecision)
    (hExportGrade : exportGrade' = exportGrade)
    (hTarget : target' = target)
    (hAudit : audit' = audit)
    (hTransport : transport' = transport)
    (hContinuation : continuation' = continuation)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    CannotClaimExportGateUp.mk registry' refusal' exportDecision' exportGrade' target'
        audit' transport' continuation' provenance' name' =
      CannotClaimExportGateUp.mk registry refusal exportDecision exportGrade target audit
        transport continuation provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hRegistry
  cases hRefusal
  cases hExportDecision
  cases hExportGrade
  cases hTarget
  cases hAudit
  cases hTransport
  cases hContinuation
  cases hProvenance
  cases hName
  rfl

def cannotClaimExportGateToEventFlow : CannotClaimExportGateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CannotClaimExportGateUp.mk registry refusal exportDecision exportGrade target audit
      transport continuation provenance name =>
      [[BMark.b0],
        cannotClaimExportGateEncodeBHist registry,
        [BMark.b1, BMark.b0],
        cannotClaimExportGateEncodeBHist refusal,
        [BMark.b1, BMark.b1, BMark.b0],
        cannotClaimExportGateEncodeBHist exportDecision,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cannotClaimExportGateEncodeBHist exportGrade,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cannotClaimExportGateEncodeBHist target,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cannotClaimExportGateEncodeBHist audit,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cannotClaimExportGateEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        cannotClaimExportGateEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        cannotClaimExportGateEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        cannotClaimExportGateEncodeBHist name]

private def cannotClaimExportGateRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => cannotClaimExportGateRawAt n rest

private def cannotClaimExportGateLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => cannotClaimExportGateLengthEq n rest

def cannotClaimExportGateFromEventFlow : EventFlow → Option CannotClaimExportGateUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match cannotClaimExportGateLengthEq 20 flow with
      | true =>
          some
            (CannotClaimExportGateUp.mk
              (cannotClaimExportGateDecodeBHist (cannotClaimExportGateRawAt 1 flow))
              (cannotClaimExportGateDecodeBHist (cannotClaimExportGateRawAt 3 flow))
              (cannotClaimExportGateDecodeBHist (cannotClaimExportGateRawAt 5 flow))
              (cannotClaimExportGateDecodeBHist (cannotClaimExportGateRawAt 7 flow))
              (cannotClaimExportGateDecodeBHist (cannotClaimExportGateRawAt 9 flow))
              (cannotClaimExportGateDecodeBHist (cannotClaimExportGateRawAt 11 flow))
              (cannotClaimExportGateDecodeBHist (cannotClaimExportGateRawAt 13 flow))
              (cannotClaimExportGateDecodeBHist (cannotClaimExportGateRawAt 15 flow))
              (cannotClaimExportGateDecodeBHist (cannotClaimExportGateRawAt 17 flow))
              (cannotClaimExportGateDecodeBHist (cannotClaimExportGateRawAt 19 flow)))
      | false => none

private theorem cannotClaimExportGate_round_trip :
    ∀ x : CannotClaimExportGateUp,
      cannotClaimExportGateFromEventFlow (cannotClaimExportGateToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk registry refusal exportDecision exportGrade target audit transport continuation
      provenance name =>
      change
        some
          (CannotClaimExportGateUp.mk
            (cannotClaimExportGateDecodeBHist (cannotClaimExportGateEncodeBHist registry))
            (cannotClaimExportGateDecodeBHist (cannotClaimExportGateEncodeBHist refusal))
            (cannotClaimExportGateDecodeBHist
              (cannotClaimExportGateEncodeBHist exportDecision))
            (cannotClaimExportGateDecodeBHist
              (cannotClaimExportGateEncodeBHist exportGrade))
            (cannotClaimExportGateDecodeBHist (cannotClaimExportGateEncodeBHist target))
            (cannotClaimExportGateDecodeBHist (cannotClaimExportGateEncodeBHist audit))
            (cannotClaimExportGateDecodeBHist
              (cannotClaimExportGateEncodeBHist transport))
            (cannotClaimExportGateDecodeBHist
              (cannotClaimExportGateEncodeBHist continuation))
            (cannotClaimExportGateDecodeBHist
              (cannotClaimExportGateEncodeBHist provenance))
            (cannotClaimExportGateDecodeBHist (cannotClaimExportGateEncodeBHist name))) =
          some
            (CannotClaimExportGateUp.mk registry refusal exportDecision exportGrade target
              audit transport continuation provenance name)
      exact
        congrArg some
          (cannotClaimExportGate_mk_congr
            (cannotClaimExportGate_decode_encode_bhist registry)
            (cannotClaimExportGate_decode_encode_bhist refusal)
            (cannotClaimExportGate_decode_encode_bhist exportDecision)
            (cannotClaimExportGate_decode_encode_bhist exportGrade)
            (cannotClaimExportGate_decode_encode_bhist target)
            (cannotClaimExportGate_decode_encode_bhist audit)
            (cannotClaimExportGate_decode_encode_bhist transport)
            (cannotClaimExportGate_decode_encode_bhist continuation)
            (cannotClaimExportGate_decode_encode_bhist provenance)
            (cannotClaimExportGate_decode_encode_bhist name))

private theorem cannotClaimExportGateToEventFlow_injective
    {x y : CannotClaimExportGateUp} :
    cannotClaimExportGateToEventFlow x = cannotClaimExportGateToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cannotClaimExportGateFromEventFlow (cannotClaimExportGateToEventFlow x) =
        cannotClaimExportGateFromEventFlow (cannotClaimExportGateToEventFlow y) :=
    congrArg cannotClaimExportGateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cannotClaimExportGate_round_trip x).symm
      (Eq.trans hread (cannotClaimExportGate_round_trip y)))

private def cannotClaimExportGateFields : CannotClaimExportGateUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CannotClaimExportGateUp.mk registry refusal exportDecision exportGrade target audit
      transport continuation provenance name =>
      [registry, refusal, exportDecision, exportGrade, target, audit, transport,
        continuation, provenance, name]

private theorem cannotClaimExportGate_field_faithful :
    ∀ x y : CannotClaimExportGateUp,
      cannotClaimExportGateFields x = cannotClaimExportGateFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk registry₁ refusal₁ exportDecision₁ exportGrade₁ target₁ audit₁ transport₁
      continuation₁ provenance₁ name₁ =>
      cases y with
      | mk registry₂ refusal₂ exportDecision₂ exportGrade₂ target₂ audit₂ transport₂
          continuation₂ provenance₂ name₂ =>
          cases h
          rfl

instance cannotClaimExportGateBHistCarrier :
    BHistCarrier CannotClaimExportGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cannotClaimExportGateToEventFlow
  fromEventFlow := cannotClaimExportGateFromEventFlow

instance cannotClaimExportGateChapterTasteGate :
    ChapterTasteGate CannotClaimExportGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cannotClaimExportGateFromEventFlow (cannotClaimExportGateToEventFlow x) =
        some x
    exact cannotClaimExportGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cannotClaimExportGateToEventFlow_injective heq)

instance cannotClaimExportGateFieldFaithful :
    FieldFaithful CannotClaimExportGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cannotClaimExportGateFields
  field_faithful := cannotClaimExportGate_field_faithful

instance cannotClaimExportGateNontrivial :
    Nontrivial CannotClaimExportGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CannotClaimExportGateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CannotClaimExportGateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CannotClaimExportGateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cannotClaimExportGateChapterTasteGate

theorem CannotClaimExportGateTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cannotClaimExportGateDecodeBHist (cannotClaimExportGateEncodeBHist h) = h) ∧
      (∀ x : CannotClaimExportGateUp,
        cannotClaimExportGateFromEventFlow (cannotClaimExportGateToEventFlow x) =
          some x) ∧
        (∀ x y : CannotClaimExportGateUp,
          cannotClaimExportGateToEventFlow x =
            cannotClaimExportGateToEventFlow y → x = y) ∧
          Nonempty (FieldFaithful CannotClaimExportGateUp) ∧
            Nonempty (ChapterTasteGate CannotClaimExportGateUp) ∧
              cannotClaimExportGateEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact cannotClaimExportGate_decode_encode_bhist
  · constructor
    · exact cannotClaimExportGate_round_trip
    · constructor
      · intro x y heq
        exact cannotClaimExportGateToEventFlow_injective heq
      · constructor
        · exact Nonempty.intro cannotClaimExportGateFieldFaithful
        · constructor
          · exact Nonempty.intro cannotClaimExportGateChapterTasteGate
          · rfl

end BEDC.Derived.CannotClaimExportGateUp
