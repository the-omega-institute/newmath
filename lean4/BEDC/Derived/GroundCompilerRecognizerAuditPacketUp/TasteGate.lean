import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GroundCompilerRecognizerAuditPacketUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive GroundCompilerRecognizerAuditPacketUp : Type where
  | mk :
      (recognizer address evidence nonEvidence bridgeRequest transports continuations
        provenance name : BHist) →
      GroundCompilerRecognizerAuditPacketUp
  deriving DecidableEq

def groundCompilerRecognizerAuditPacketEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: groundCompilerRecognizerAuditPacketEncodeBHist h
  | BHist.e1 h => BMark.b1 :: groundCompilerRecognizerAuditPacketEncodeBHist h

def groundCompilerRecognizerAuditPacketDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (groundCompilerRecognizerAuditPacketDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (groundCompilerRecognizerAuditPacketDecodeBHist tail)

private theorem groundCompilerRecognizerAuditPacketDecodeEncodeBHist :
    ∀ h : BHist,
      groundCompilerRecognizerAuditPacketDecodeBHist
        (groundCompilerRecognizerAuditPacketEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def groundCompilerRecognizerAuditPacketFields :
    GroundCompilerRecognizerAuditPacketUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | GroundCompilerRecognizerAuditPacketUp.mk recognizer address evidence nonEvidence
      bridgeRequest transports continuations provenance name =>
      [recognizer, address, evidence, nonEvidence, bridgeRequest, transports,
        continuations, provenance, name]

def groundCompilerRecognizerAuditPacketToEventFlow :
    GroundCompilerRecognizerAuditPacketUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (groundCompilerRecognizerAuditPacketFields x).map
        groundCompilerRecognizerAuditPacketEncodeBHist

def groundCompilerRecognizerAuditPacketFromEventFlow :
    EventFlow → Option GroundCompilerRecognizerAuditPacketUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | recognizer :: rest0 =>
      match rest0 with
      | [] => none
      | address :: rest1 =>
          match rest1 with
          | [] => none
          | evidence :: rest2 =>
              match rest2 with
              | [] => none
              | nonEvidence :: rest3 =>
                  match rest3 with
                  | [] => none
                  | bridgeRequest :: rest4 =>
                      match rest4 with
                      | [] => none
                      | transports :: rest5 =>
                          match rest5 with
                          | [] => none
                          | continuations :: rest6 =>
                              match rest6 with
                              | [] => none
                              | provenance :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | name :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (GroundCompilerRecognizerAuditPacketUp.mk
                                              (groundCompilerRecognizerAuditPacketDecodeBHist
                                                recognizer)
                                              (groundCompilerRecognizerAuditPacketDecodeBHist
                                                address)
                                              (groundCompilerRecognizerAuditPacketDecodeBHist
                                                evidence)
                                              (groundCompilerRecognizerAuditPacketDecodeBHist
                                                nonEvidence)
                                              (groundCompilerRecognizerAuditPacketDecodeBHist
                                                bridgeRequest)
                                              (groundCompilerRecognizerAuditPacketDecodeBHist
                                                transports)
                                              (groundCompilerRecognizerAuditPacketDecodeBHist
                                                continuations)
                                              (groundCompilerRecognizerAuditPacketDecodeBHist
                                                provenance)
                                              (groundCompilerRecognizerAuditPacketDecodeBHist
                                                name))
                                      | _ :: _ => none

private theorem groundCompilerRecognizerAuditPacket_round_trip :
    ∀ x : GroundCompilerRecognizerAuditPacketUp,
      groundCompilerRecognizerAuditPacketFromEventFlow
        (groundCompilerRecognizerAuditPacketToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk recognizer address evidence nonEvidence bridgeRequest transports continuations
      provenance name =>
      change
        some
          (GroundCompilerRecognizerAuditPacketUp.mk
            (groundCompilerRecognizerAuditPacketDecodeBHist
              (groundCompilerRecognizerAuditPacketEncodeBHist recognizer))
            (groundCompilerRecognizerAuditPacketDecodeBHist
              (groundCompilerRecognizerAuditPacketEncodeBHist address))
            (groundCompilerRecognizerAuditPacketDecodeBHist
              (groundCompilerRecognizerAuditPacketEncodeBHist evidence))
            (groundCompilerRecognizerAuditPacketDecodeBHist
              (groundCompilerRecognizerAuditPacketEncodeBHist nonEvidence))
            (groundCompilerRecognizerAuditPacketDecodeBHist
              (groundCompilerRecognizerAuditPacketEncodeBHist bridgeRequest))
            (groundCompilerRecognizerAuditPacketDecodeBHist
              (groundCompilerRecognizerAuditPacketEncodeBHist transports))
            (groundCompilerRecognizerAuditPacketDecodeBHist
              (groundCompilerRecognizerAuditPacketEncodeBHist continuations))
            (groundCompilerRecognizerAuditPacketDecodeBHist
              (groundCompilerRecognizerAuditPacketEncodeBHist provenance))
            (groundCompilerRecognizerAuditPacketDecodeBHist
              (groundCompilerRecognizerAuditPacketEncodeBHist name))) =
          some
            (GroundCompilerRecognizerAuditPacketUp.mk recognizer address evidence
              nonEvidence bridgeRequest transports continuations provenance name)
      rw [groundCompilerRecognizerAuditPacketDecodeEncodeBHist recognizer,
        groundCompilerRecognizerAuditPacketDecodeEncodeBHist address,
        groundCompilerRecognizerAuditPacketDecodeEncodeBHist evidence,
        groundCompilerRecognizerAuditPacketDecodeEncodeBHist nonEvidence,
        groundCompilerRecognizerAuditPacketDecodeEncodeBHist bridgeRequest,
        groundCompilerRecognizerAuditPacketDecodeEncodeBHist transports,
        groundCompilerRecognizerAuditPacketDecodeEncodeBHist continuations,
        groundCompilerRecognizerAuditPacketDecodeEncodeBHist provenance,
        groundCompilerRecognizerAuditPacketDecodeEncodeBHist name]

private theorem groundCompilerRecognizerAuditPacketToEventFlow_injective
    {x y : GroundCompilerRecognizerAuditPacketUp} :
    groundCompilerRecognizerAuditPacketToEventFlow x =
      groundCompilerRecognizerAuditPacketToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      groundCompilerRecognizerAuditPacketFromEventFlow
          (groundCompilerRecognizerAuditPacketToEventFlow x) =
        groundCompilerRecognizerAuditPacketFromEventFlow
          (groundCompilerRecognizerAuditPacketToEventFlow y) :=
    congrArg groundCompilerRecognizerAuditPacketFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (groundCompilerRecognizerAuditPacket_round_trip x).symm
      (Eq.trans hread (groundCompilerRecognizerAuditPacket_round_trip y)))

private theorem groundCompilerRecognizerAuditPacket_field_faithful :
    ∀ x y : GroundCompilerRecognizerAuditPacketUp,
      groundCompilerRecognizerAuditPacketFields x =
        groundCompilerRecognizerAuditPacketFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk recognizer address evidence nonEvidence bridgeRequest transports continuations
      provenance name =>
      cases y with
      | mk recognizer' address' evidence' nonEvidence' bridgeRequest' transports'
          continuations' provenance' name' =>
          cases hfields
          rfl

instance groundCompilerRecognizerAuditPacketBHistCarrier :
    BHistCarrier GroundCompilerRecognizerAuditPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := groundCompilerRecognizerAuditPacketToEventFlow
  fromEventFlow := groundCompilerRecognizerAuditPacketFromEventFlow

instance groundCompilerRecognizerAuditPacketChapterTasteGate :
    ChapterTasteGate GroundCompilerRecognizerAuditPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      groundCompilerRecognizerAuditPacketFromEventFlow
          (groundCompilerRecognizerAuditPacketToEventFlow x) =
        some x
    exact groundCompilerRecognizerAuditPacket_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (groundCompilerRecognizerAuditPacketToEventFlow_injective heq)

instance groundCompilerRecognizerAuditPacketFieldFaithful :
    FieldFaithful GroundCompilerRecognizerAuditPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := groundCompilerRecognizerAuditPacketFields
  field_faithful := groundCompilerRecognizerAuditPacket_field_faithful

instance groundCompilerRecognizerAuditPacketNontrivial :
    Nontrivial GroundCompilerRecognizerAuditPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨GroundCompilerRecognizerAuditPacketUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      GroundCompilerRecognizerAuditPacketUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate GroundCompilerRecognizerAuditPacketUp :=
  -- BEDC touchpoint anchor: BHist BMark
  groundCompilerRecognizerAuditPacketChapterTasteGate

theorem GroundCompilerRecognizerAuditPacketTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      groundCompilerRecognizerAuditPacketDecodeBHist
        (groundCompilerRecognizerAuditPacketEncodeBHist h) = h) ∧
      (∀ x : GroundCompilerRecognizerAuditPacketUp,
        groundCompilerRecognizerAuditPacketFromEventFlow
          (groundCompilerRecognizerAuditPacketToEventFlow x) = some x) ∧
        (∀ x y : GroundCompilerRecognizerAuditPacketUp,
          groundCompilerRecognizerAuditPacketToEventFlow x =
            groundCompilerRecognizerAuditPacketToEventFlow y → x = y) ∧
          groundCompilerRecognizerAuditPacketEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact groundCompilerRecognizerAuditPacketDecodeEncodeBHist
  · constructor
    · exact groundCompilerRecognizerAuditPacket_round_trip
    · constructor
      · intro x y heq
        exact groundCompilerRecognizerAuditPacketToEventFlow_injective heq
      · rfl

end BEDC.Derived.GroundCompilerRecognizerAuditPacketUp
