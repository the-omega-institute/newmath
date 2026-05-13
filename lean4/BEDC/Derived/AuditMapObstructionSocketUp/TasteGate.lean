import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AuditMapObstructionSocketUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AuditMapObstructionSocketUp : Type where
  | mk :
      (auditTag positive conditional obstruction frontier transport continuations provenance
        nameCert : BHist) →
      AuditMapObstructionSocketUp
  deriving DecidableEq

def auditMapObstructionSocketEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: auditMapObstructionSocketEncodeBHist h
  | BHist.e1 h => BMark.b1 :: auditMapObstructionSocketEncodeBHist h

def auditMapObstructionSocketDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (auditMapObstructionSocketDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (auditMapObstructionSocketDecodeBHist tail)

private theorem auditMapObstructionSocket_decode_encode_bhist :
    ∀ h : BHist,
      auditMapObstructionSocketDecodeBHist (auditMapObstructionSocketEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def auditMapObstructionSocketToEventFlow : AuditMapObstructionSocketUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AuditMapObstructionSocketUp.mk auditTag positive conditional obstruction frontier transport
      continuations provenance nameCert =>
      [[BMark.b0],
        auditMapObstructionSocketEncodeBHist auditTag,
        [BMark.b1, BMark.b0],
        auditMapObstructionSocketEncodeBHist positive,
        [BMark.b1, BMark.b1, BMark.b0],
        auditMapObstructionSocketEncodeBHist conditional,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapObstructionSocketEncodeBHist obstruction,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapObstructionSocketEncodeBHist frontier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapObstructionSocketEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapObstructionSocketEncodeBHist continuations,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        auditMapObstructionSocketEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        auditMapObstructionSocketEncodeBHist nameCert]

def auditMapObstructionSocketFromEventFlow : EventFlow → Option AuditMapObstructionSocketUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | auditTag :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | positive :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | conditional :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | obstruction :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | frontier :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transport :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | continuations :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | nameCert :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (AuditMapObstructionSocketUp.mk
                                                                                  (auditMapObstructionSocketDecodeBHist
                                                                                    auditTag)
                                                                                  (auditMapObstructionSocketDecodeBHist
                                                                                    positive)
                                                                                  (auditMapObstructionSocketDecodeBHist
                                                                                    conditional)
                                                                                  (auditMapObstructionSocketDecodeBHist
                                                                                    obstruction)
                                                                                  (auditMapObstructionSocketDecodeBHist
                                                                                    frontier)
                                                                                  (auditMapObstructionSocketDecodeBHist
                                                                                    transport)
                                                                                  (auditMapObstructionSocketDecodeBHist
                                                                                    continuations)
                                                                                  (auditMapObstructionSocketDecodeBHist
                                                                                    provenance)
                                                                                  (auditMapObstructionSocketDecodeBHist
                                                                                    nameCert))
                                                                          | _ :: _ => none

private theorem auditMapObstructionSocket_mk_congr
    {auditTag auditTag' positive positive' conditional conditional' obstruction obstruction'
      frontier frontier' transport transport' continuations continuations' provenance provenance'
      nameCert nameCert' : BHist}
    (hAuditTag : auditTag' = auditTag)
    (hPositive : positive' = positive)
    (hConditional : conditional' = conditional)
    (hObstruction : obstruction' = obstruction)
    (hFrontier : frontier' = frontier)
    (hTransport : transport' = transport)
    (hContinuations : continuations' = continuations)
    (hProvenance : provenance' = provenance)
    (hNameCert : nameCert' = nameCert) :
    AuditMapObstructionSocketUp.mk auditTag' positive' conditional' obstruction' frontier'
        transport' continuations' provenance' nameCert' =
      AuditMapObstructionSocketUp.mk auditTag positive conditional obstruction frontier transport
        continuations provenance nameCert := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hAuditTag
  cases hPositive
  cases hConditional
  cases hObstruction
  cases hFrontier
  cases hTransport
  cases hContinuations
  cases hProvenance
  cases hNameCert
  rfl

private theorem auditMapObstructionSocket_round_trip :
    ∀ x : AuditMapObstructionSocketUp,
      auditMapObstructionSocketFromEventFlow (auditMapObstructionSocketToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk auditTag positive conditional obstruction frontier transport continuations provenance
      nameCert =>
      change
        some
          (AuditMapObstructionSocketUp.mk
            (auditMapObstructionSocketDecodeBHist (auditMapObstructionSocketEncodeBHist auditTag))
            (auditMapObstructionSocketDecodeBHist (auditMapObstructionSocketEncodeBHist positive))
            (auditMapObstructionSocketDecodeBHist
              (auditMapObstructionSocketEncodeBHist conditional))
            (auditMapObstructionSocketDecodeBHist
              (auditMapObstructionSocketEncodeBHist obstruction))
            (auditMapObstructionSocketDecodeBHist (auditMapObstructionSocketEncodeBHist frontier))
            (auditMapObstructionSocketDecodeBHist
              (auditMapObstructionSocketEncodeBHist transport))
            (auditMapObstructionSocketDecodeBHist
              (auditMapObstructionSocketEncodeBHist continuations))
            (auditMapObstructionSocketDecodeBHist
              (auditMapObstructionSocketEncodeBHist provenance))
            (auditMapObstructionSocketDecodeBHist (auditMapObstructionSocketEncodeBHist nameCert))) =
          some
            (AuditMapObstructionSocketUp.mk auditTag positive conditional obstruction frontier
              transport continuations provenance nameCert)
      exact
        congrArg some
          (auditMapObstructionSocket_mk_congr
            (auditMapObstructionSocket_decode_encode_bhist auditTag)
            (auditMapObstructionSocket_decode_encode_bhist positive)
            (auditMapObstructionSocket_decode_encode_bhist conditional)
            (auditMapObstructionSocket_decode_encode_bhist obstruction)
            (auditMapObstructionSocket_decode_encode_bhist frontier)
            (auditMapObstructionSocket_decode_encode_bhist transport)
            (auditMapObstructionSocket_decode_encode_bhist continuations)
            (auditMapObstructionSocket_decode_encode_bhist provenance)
            (auditMapObstructionSocket_decode_encode_bhist nameCert))

private theorem auditMapObstructionSocketToEventFlow_injective {x y : AuditMapObstructionSocketUp} :
    auditMapObstructionSocketToEventFlow x = auditMapObstructionSocketToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      auditMapObstructionSocketFromEventFlow (auditMapObstructionSocketToEventFlow x) =
        auditMapObstructionSocketFromEventFlow (auditMapObstructionSocketToEventFlow y) :=
    congrArg auditMapObstructionSocketFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (auditMapObstructionSocket_round_trip x).symm
      (Eq.trans hread (auditMapObstructionSocket_round_trip y)))

instance auditMapObstructionSocketBHistCarrier : BHistCarrier AuditMapObstructionSocketUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := auditMapObstructionSocketToEventFlow
  fromEventFlow := auditMapObstructionSocketFromEventFlow

instance auditMapObstructionSocketChapterTasteGate :
    ChapterTasteGate AuditMapObstructionSocketUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      auditMapObstructionSocketFromEventFlow (auditMapObstructionSocketToEventFlow x) = some x
    exact auditMapObstructionSocket_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (auditMapObstructionSocketToEventFlow_injective heq)

instance auditMapObstructionSocketFieldFaithful : FieldFaithful AuditMapObstructionSocketUp where
  fields
    | AuditMapObstructionSocketUp.mk auditTag positive conditional obstruction frontier
        transport continuations provenance nameCert =>
        [auditTag, positive, conditional, obstruction, frontier, transport, continuations,
          provenance, nameCert]
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y hfields
    cases x with
    | mk auditTag positive conditional obstruction frontier transport continuations provenance
        nameCert =>
        cases y with
        | mk auditTag' positive' conditional' obstruction' frontier' transport' continuations'
            provenance' nameCert' =>
            cases hfields
            rfl

theorem AuditMapObstructionSocketTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      auditMapObstructionSocketDecodeBHist (auditMapObstructionSocketEncodeBHist h) = h) ∧
      (∀ x : AuditMapObstructionSocketUp,
        auditMapObstructionSocketFromEventFlow (auditMapObstructionSocketToEventFlow x) = some x) ∧
        (∀ x y : AuditMapObstructionSocketUp,
          auditMapObstructionSocketToEventFlow x = auditMapObstructionSocketToEventFlow y →
            x = y) ∧
          auditMapObstructionSocketEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact auditMapObstructionSocket_decode_encode_bhist
  · constructor
    · exact auditMapObstructionSocket_round_trip
    · constructor
      · intro x y heq
        exact auditMapObstructionSocketToEventFlow_injective heq
      · rfl

end BEDC.Derived.AuditMapObstructionSocketUp
