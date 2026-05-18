import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FormalTargetDependencyAuditUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FormalTargetDependencyAuditUp : Type where
  | mk
      (target dependency noSmuggling axiomAudit unresolvedSupply auditDecision exportGate
        transport replay provenance localName : BHist) :
      FormalTargetDependencyAuditUp
  deriving DecidableEq

private def formalTargetDependencyAuditEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: formalTargetDependencyAuditEncodeBHist h
  | BHist.e1 h => BMark.b1 :: formalTargetDependencyAuditEncodeBHist h

private def formalTargetDependencyAuditDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (formalTargetDependencyAuditDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (formalTargetDependencyAuditDecodeBHist tail)

private theorem formalTargetDependencyAudit_decode_encode_bhist :
    ∀ h : BHist,
      formalTargetDependencyAuditDecodeBHist
        (formalTargetDependencyAuditEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def formalTargetDependencyAuditToEventFlow :
    FormalTargetDependencyAuditUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FormalTargetDependencyAuditUp.mk target dependency noSmuggling axiomAudit
      unresolvedSupply auditDecision exportGate transport replay provenance localName =>
      [[BMark.b0],
        formalTargetDependencyAuditEncodeBHist target,
        [BMark.b1, BMark.b0],
        formalTargetDependencyAuditEncodeBHist dependency,
        [BMark.b1, BMark.b1, BMark.b0],
        formalTargetDependencyAuditEncodeBHist noSmuggling,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        formalTargetDependencyAuditEncodeBHist axiomAudit,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        formalTargetDependencyAuditEncodeBHist unresolvedSupply,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        formalTargetDependencyAuditEncodeBHist auditDecision,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        formalTargetDependencyAuditEncodeBHist exportGate,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        formalTargetDependencyAuditEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        formalTargetDependencyAuditEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        formalTargetDependencyAuditEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        formalTargetDependencyAuditEncodeBHist localName]

private def formalTargetDependencyAuditFromEventFlow :
    EventFlow → Option FormalTargetDependencyAuditUp
  -- BEDC touchpoint anchor: BHist BMark
  | [_tag0, target, _tag1, dependency, _tag2, noSmuggling, _tag3, axiomAudit, _tag4,
      unresolvedSupply, _tag5, auditDecision, _tag6, exportGate, _tag7, transport, _tag8,
      replay, _tag9, provenance, _tag10, localName] =>
      some
        (FormalTargetDependencyAuditUp.mk
          (formalTargetDependencyAuditDecodeBHist target)
          (formalTargetDependencyAuditDecodeBHist dependency)
          (formalTargetDependencyAuditDecodeBHist noSmuggling)
          (formalTargetDependencyAuditDecodeBHist axiomAudit)
          (formalTargetDependencyAuditDecodeBHist unresolvedSupply)
          (formalTargetDependencyAuditDecodeBHist auditDecision)
          (formalTargetDependencyAuditDecodeBHist exportGate)
          (formalTargetDependencyAuditDecodeBHist transport)
          (formalTargetDependencyAuditDecodeBHist replay)
          (formalTargetDependencyAuditDecodeBHist provenance)
          (formalTargetDependencyAuditDecodeBHist localName))
  | _ => none

private theorem formalTargetDependencyAudit_round_trip :
    ∀ x : FormalTargetDependencyAuditUp,
      formalTargetDependencyAuditFromEventFlow
        (formalTargetDependencyAuditToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk target dependency noSmuggling axiomAudit unresolvedSupply auditDecision exportGate
      transport replay provenance localName =>
      change
        some
          (FormalTargetDependencyAuditUp.mk
            (formalTargetDependencyAuditDecodeBHist
              (formalTargetDependencyAuditEncodeBHist target))
            (formalTargetDependencyAuditDecodeBHist
              (formalTargetDependencyAuditEncodeBHist dependency))
            (formalTargetDependencyAuditDecodeBHist
              (formalTargetDependencyAuditEncodeBHist noSmuggling))
            (formalTargetDependencyAuditDecodeBHist
              (formalTargetDependencyAuditEncodeBHist axiomAudit))
            (formalTargetDependencyAuditDecodeBHist
              (formalTargetDependencyAuditEncodeBHist unresolvedSupply))
            (formalTargetDependencyAuditDecodeBHist
              (formalTargetDependencyAuditEncodeBHist auditDecision))
            (formalTargetDependencyAuditDecodeBHist
              (formalTargetDependencyAuditEncodeBHist exportGate))
            (formalTargetDependencyAuditDecodeBHist
              (formalTargetDependencyAuditEncodeBHist transport))
            (formalTargetDependencyAuditDecodeBHist
              (formalTargetDependencyAuditEncodeBHist replay))
            (formalTargetDependencyAuditDecodeBHist
              (formalTargetDependencyAuditEncodeBHist provenance))
            (formalTargetDependencyAuditDecodeBHist
              (formalTargetDependencyAuditEncodeBHist localName))) =
          some
            (FormalTargetDependencyAuditUp.mk target dependency noSmuggling axiomAudit
              unresolvedSupply auditDecision exportGate transport replay provenance
              localName)
      rw [formalTargetDependencyAudit_decode_encode_bhist target,
        formalTargetDependencyAudit_decode_encode_bhist dependency,
        formalTargetDependencyAudit_decode_encode_bhist noSmuggling,
        formalTargetDependencyAudit_decode_encode_bhist axiomAudit,
        formalTargetDependencyAudit_decode_encode_bhist unresolvedSupply,
        formalTargetDependencyAudit_decode_encode_bhist auditDecision,
        formalTargetDependencyAudit_decode_encode_bhist exportGate,
        formalTargetDependencyAudit_decode_encode_bhist transport,
        formalTargetDependencyAudit_decode_encode_bhist replay,
        formalTargetDependencyAudit_decode_encode_bhist provenance,
        formalTargetDependencyAudit_decode_encode_bhist localName]

private theorem formalTargetDependencyAuditToEventFlow_injective
    {x y : FormalTargetDependencyAuditUp} :
    formalTargetDependencyAuditToEventFlow x =
      formalTargetDependencyAuditToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      formalTargetDependencyAuditFromEventFlow
          (formalTargetDependencyAuditToEventFlow x) =
        formalTargetDependencyAuditFromEventFlow
          (formalTargetDependencyAuditToEventFlow y) :=
    congrArg formalTargetDependencyAuditFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (formalTargetDependencyAudit_round_trip x).symm
      (Eq.trans hread (formalTargetDependencyAudit_round_trip y)))

instance formalTargetDependencyAuditBHistCarrier :
    BHistCarrier FormalTargetDependencyAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := formalTargetDependencyAuditToEventFlow
  fromEventFlow := formalTargetDependencyAuditFromEventFlow

instance formalTargetDependencyAuditChapterTasteGate :
    ChapterTasteGate FormalTargetDependencyAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      formalTargetDependencyAuditFromEventFlow
        (formalTargetDependencyAuditToEventFlow x) = some x
    exact formalTargetDependencyAudit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (formalTargetDependencyAuditToEventFlow_injective heq)

instance formalTargetDependencyAuditFieldFaithful :
    FieldFaithful FormalTargetDependencyAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | FormalTargetDependencyAuditUp.mk target dependency noSmuggling axiomAudit
        unresolvedSupply auditDecision exportGate transport replay provenance localName =>
        [target, dependency, noSmuggling, axiomAudit, unresolvedSupply, auditDecision,
          exportGate, transport, replay, provenance, localName]
  field_faithful := by
    intro x y h
    cases x with
    | mk target₁ dependency₁ noSmuggling₁ axiomAudit₁ unresolvedSupply₁ auditDecision₁
        exportGate₁ transport₁ replay₁ provenance₁ localName₁ =>
        cases y with
        | mk target₂ dependency₂ noSmuggling₂ axiomAudit₂ unresolvedSupply₂ auditDecision₂
            exportGate₂ transport₂ replay₂ provenance₂ localName₂ =>
            injection h with hTarget t1
            injection t1 with hDependency t2
            injection t2 with hNoSmuggling t3
            injection t3 with hAxiomAudit t4
            injection t4 with hUnresolvedSupply t5
            injection t5 with hAuditDecision t6
            injection t6 with hExportGate t7
            injection t7 with hTransport t8
            injection t8 with hReplay t9
            injection t9 with hProvenance t10
            injection t10 with hLocalName _
            cases hTarget
            cases hDependency
            cases hNoSmuggling
            cases hAxiomAudit
            cases hUnresolvedSupply
            cases hAuditDecision
            cases hExportGate
            cases hTransport
            cases hReplay
            cases hProvenance
            cases hLocalName
            rfl

instance formalTargetDependencyAuditNontrivial :
    Nontrivial FormalTargetDependencyAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FormalTargetDependencyAuditUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FormalTargetDependencyAuditUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FormalTargetDependencyAuditUp :=
  -- BEDC touchpoint anchor: BHist BMark
  formalTargetDependencyAuditChapterTasteGate

end BEDC.Derived.FormalTargetDependencyAuditUp
