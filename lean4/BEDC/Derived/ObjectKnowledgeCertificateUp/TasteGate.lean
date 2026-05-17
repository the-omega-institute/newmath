import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ObjectKnowledgeCertificateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ObjectKnowledgeCertificateUp : Type where
  | mk :
      (objectName witness source pattern classifier stability ledger auditRoute
        componentTransport localNameCert : BHist) →
      ObjectKnowledgeCertificateUp
  deriving DecidableEq

def objectKnowledgeCertificateFields : ObjectKnowledgeCertificateUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ObjectKnowledgeCertificateUp.mk objectName witness source pattern classifier stability
      ledger auditRoute componentTransport localNameCert =>
      [objectName, witness, source, pattern, classifier, stability, ledger, auditRoute,
        componentTransport, localNameCert]

def objectKnowledgeCertificateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: objectKnowledgeCertificateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: objectKnowledgeCertificateEncodeBHist h

def objectKnowledgeCertificateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (objectKnowledgeCertificateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (objectKnowledgeCertificateDecodeBHist tail)

private theorem objectKnowledgeCertificateDecodeEncodeBHist :
    ∀ h : BHist,
      objectKnowledgeCertificateDecodeBHist
        (objectKnowledgeCertificateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem objectKnowledgeCertificate_mk_congr
    {objectName objectName' witness witness' source source' pattern pattern'
      classifier classifier' stability stability' ledger ledger' auditRoute auditRoute'
      componentTransport componentTransport' localNameCert localNameCert' : BHist}
    (hObjectName : objectName' = objectName)
    (hWitness : witness' = witness)
    (hSource : source' = source)
    (hPattern : pattern' = pattern)
    (hClassifier : classifier' = classifier)
    (hStability : stability' = stability)
    (hLedger : ledger' = ledger)
    (hAuditRoute : auditRoute' = auditRoute)
    (hComponentTransport : componentTransport' = componentTransport)
    (hLocalNameCert : localNameCert' = localNameCert) :
    ObjectKnowledgeCertificateUp.mk objectName' witness' source' pattern' classifier'
        stability' ledger' auditRoute' componentTransport' localNameCert' =
      ObjectKnowledgeCertificateUp.mk objectName witness source pattern classifier stability
        ledger auditRoute componentTransport localNameCert := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hObjectName
  cases hWitness
  cases hSource
  cases hPattern
  cases hClassifier
  cases hStability
  cases hLedger
  cases hAuditRoute
  cases hComponentTransport
  cases hLocalNameCert
  rfl

def objectKnowledgeCertificateToEventFlow :
    ObjectKnowledgeCertificateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (objectKnowledgeCertificateFields x).map
        objectKnowledgeCertificateEncodeBHist

def objectKnowledgeCertificateFromEventFlow :
    EventFlow → Option ObjectKnowledgeCertificateUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | objectName :: rest0 =>
      match rest0 with
      | [] => none
      | witness :: rest1 =>
          match rest1 with
          | [] => none
          | source :: rest2 =>
              match rest2 with
              | [] => none
              | pattern :: rest3 =>
                  match rest3 with
                  | [] => none
                  | classifier :: rest4 =>
                      match rest4 with
                      | [] => none
                      | stability :: rest5 =>
                          match rest5 with
                          | [] => none
                          | ledger :: rest6 =>
                              match rest6 with
                              | [] => none
                              | auditRoute :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | componentTransport :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | localNameCert :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (ObjectKnowledgeCertificateUp.mk
                                                  (objectKnowledgeCertificateDecodeBHist
                                                    objectName)
                                                  (objectKnowledgeCertificateDecodeBHist
                                                    witness)
                                                  (objectKnowledgeCertificateDecodeBHist
                                                    source)
                                                  (objectKnowledgeCertificateDecodeBHist
                                                    pattern)
                                                  (objectKnowledgeCertificateDecodeBHist
                                                    classifier)
                                                  (objectKnowledgeCertificateDecodeBHist
                                                    stability)
                                                  (objectKnowledgeCertificateDecodeBHist
                                                    ledger)
                                                  (objectKnowledgeCertificateDecodeBHist
                                                    auditRoute)
                                                  (objectKnowledgeCertificateDecodeBHist
                                                    componentTransport)
                                                  (objectKnowledgeCertificateDecodeBHist
                                                    localNameCert))
                                          | _ :: _ => none

private theorem objectKnowledgeCertificate_round_trip :
    ∀ x : ObjectKnowledgeCertificateUp,
      objectKnowledgeCertificateFromEventFlow
        (objectKnowledgeCertificateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk objectName witness source pattern classifier stability ledger auditRoute
      componentTransport localNameCert =>
      exact
        congrArg some
          (objectKnowledgeCertificate_mk_congr
            (objectKnowledgeCertificateDecodeEncodeBHist objectName)
            (objectKnowledgeCertificateDecodeEncodeBHist witness)
            (objectKnowledgeCertificateDecodeEncodeBHist source)
            (objectKnowledgeCertificateDecodeEncodeBHist pattern)
            (objectKnowledgeCertificateDecodeEncodeBHist classifier)
            (objectKnowledgeCertificateDecodeEncodeBHist stability)
            (objectKnowledgeCertificateDecodeEncodeBHist ledger)
            (objectKnowledgeCertificateDecodeEncodeBHist auditRoute)
            (objectKnowledgeCertificateDecodeEncodeBHist componentTransport)
            (objectKnowledgeCertificateDecodeEncodeBHist localNameCert))

private theorem objectKnowledgeCertificateToEventFlow_injective
    {x y : ObjectKnowledgeCertificateUp} :
    objectKnowledgeCertificateToEventFlow x =
      objectKnowledgeCertificateToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      objectKnowledgeCertificateFromEventFlow
          (objectKnowledgeCertificateToEventFlow x) =
        objectKnowledgeCertificateFromEventFlow
          (objectKnowledgeCertificateToEventFlow y) :=
    congrArg objectKnowledgeCertificateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (objectKnowledgeCertificate_round_trip x).symm
      (Eq.trans hread (objectKnowledgeCertificate_round_trip y)))

private theorem objectKnowledgeCertificate_field_faithful :
    ∀ x y : ObjectKnowledgeCertificateUp,
      objectKnowledgeCertificateFields x =
        objectKnowledgeCertificateFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk objectName witness source pattern classifier stability ledger auditRoute
      componentTransport localNameCert =>
      cases y with
      | mk objectName' witness' source' pattern' classifier' stability' ledger' auditRoute'
          componentTransport' localNameCert' =>
          cases hfields
          rfl

instance objectKnowledgeCertificateBHistCarrier :
    BHistCarrier ObjectKnowledgeCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := objectKnowledgeCertificateToEventFlow
  fromEventFlow := objectKnowledgeCertificateFromEventFlow

instance objectKnowledgeCertificateChapterTasteGate :
    ChapterTasteGate ObjectKnowledgeCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      objectKnowledgeCertificateFromEventFlow
        (objectKnowledgeCertificateToEventFlow x) = some x
    exact objectKnowledgeCertificate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (objectKnowledgeCertificateToEventFlow_injective heq)

instance objectKnowledgeCertificateFieldFaithful :
    FieldFaithful ObjectKnowledgeCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := objectKnowledgeCertificateFields
  field_faithful := objectKnowledgeCertificate_field_faithful

instance objectKnowledgeCertificateNontrivial :
    Nontrivial ObjectKnowledgeCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ObjectKnowledgeCertificateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ObjectKnowledgeCertificateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ObjectKnowledgeCertificateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  objectKnowledgeCertificateChapterTasteGate

theorem ObjectKnowledgeCertificateTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      objectKnowledgeCertificateDecodeBHist
        (objectKnowledgeCertificateEncodeBHist h) = h) ∧
      objectKnowledgeCertificateEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] ∧
        (∀ x : ObjectKnowledgeCertificateUp,
          objectKnowledgeCertificateFromEventFlow
            (objectKnowledgeCertificateToEventFlow x) = some x) ∧
          (∀ x y : ObjectKnowledgeCertificateUp,
            objectKnowledgeCertificateToEventFlow x =
              objectKnowledgeCertificateToEventFlow y → x = y) ∧
            (∀ x y : ObjectKnowledgeCertificateUp,
              objectKnowledgeCertificateFields x =
                objectKnowledgeCertificateFields y → x = y) ∧
              (∃ x y : ObjectKnowledgeCertificateUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨objectKnowledgeCertificateDecodeEncodeBHist, rfl,
      objectKnowledgeCertificate_round_trip,
      (fun _ _ heq => objectKnowledgeCertificateToEventFlow_injective heq),
      objectKnowledgeCertificate_field_faithful,
      ⟨ObjectKnowledgeCertificateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        ObjectKnowledgeCertificateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty,
        by
          intro h
          cases h⟩⟩

theorem ObjectKnowledgeCertificate_witness_audit_rows_reflect_display
    {N W S P K T L A C Q N' W' S' P' K' T' L' A' C' Q' : BHist}
    (hdisplay :
      objectKnowledgeCertificateToEventFlow
          (ObjectKnowledgeCertificateUp.mk N W S P K T L A C Q) =
        objectKnowledgeCertificateToEventFlow
          (ObjectKnowledgeCertificateUp.mk N' W' S' P' K' T' L' A' C' Q')) :
    W = W' ∧ A = A' ∧
      objectKnowledgeCertificateEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark
  have hpacket :
      ObjectKnowledgeCertificateUp.mk N W S P K T L A C Q =
        ObjectKnowledgeCertificateUp.mk N' W' S' P' K' T' L' A' C' Q' :=
    objectKnowledgeCertificateToEventFlow_injective hdisplay
  cases hpacket
  exact ⟨rfl, rfl, rfl⟩

end BEDC.Derived.ObjectKnowledgeCertificateUp
