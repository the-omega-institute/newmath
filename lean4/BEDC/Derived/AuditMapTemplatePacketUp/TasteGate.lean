import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AuditMapTemplatePacketUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AuditMapTemplatePacketUp : Type where
  | mk (template obligation route obstruction frontier transport provenance nameCert : BHist) :
      AuditMapTemplatePacketUp
  deriving DecidableEq

private def auditMapTemplatePacketEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: auditMapTemplatePacketEncodeBHist h
  | BHist.e1 h => BMark.b1 :: auditMapTemplatePacketEncodeBHist h

private def auditMapTemplatePacketDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (auditMapTemplatePacketDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (auditMapTemplatePacketDecodeBHist tail)

private theorem auditMapTemplatePacketDecode_encode_bhist :
    ∀ h : BHist,
      auditMapTemplatePacketDecodeBHist (auditMapTemplatePacketEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def auditMapTemplatePacketToEventFlow : AuditMapTemplatePacketUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AuditMapTemplatePacketUp.mk template obligation route obstruction frontier transport
      provenance nameCert =>
      [[BMark.b0],
        auditMapTemplatePacketEncodeBHist template,
        [BMark.b1, BMark.b0],
        auditMapTemplatePacketEncodeBHist obligation,
        [BMark.b1, BMark.b1, BMark.b0],
        auditMapTemplatePacketEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapTemplatePacketEncodeBHist obstruction,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapTemplatePacketEncodeBHist frontier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapTemplatePacketEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapTemplatePacketEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        auditMapTemplatePacketEncodeBHist nameCert]

private def auditMapTemplatePacketFromEventFlow : EventFlow → Option AuditMapTemplatePacketUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | template :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | obligation :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | route :: rest5 =>
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
                                                      | provenance :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | nameCert :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (AuditMapTemplatePacketUp.mk
                                                                          (auditMapTemplatePacketDecodeBHist
                                                                            template)
                                                                          (auditMapTemplatePacketDecodeBHist
                                                                            obligation)
                                                                          (auditMapTemplatePacketDecodeBHist
                                                                            route)
                                                                          (auditMapTemplatePacketDecodeBHist
                                                                            obstruction)
                                                                          (auditMapTemplatePacketDecodeBHist
                                                                            frontier)
                                                                          (auditMapTemplatePacketDecodeBHist
                                                                            transport)
                                                                          (auditMapTemplatePacketDecodeBHist
                                                                            provenance)
                                                                          (auditMapTemplatePacketDecodeBHist
                                                                            nameCert))
                                                                  | _ :: _ => none

private theorem auditMapTemplatePacket_round_trip :
    ∀ x : AuditMapTemplatePacketUp,
      auditMapTemplatePacketFromEventFlow (auditMapTemplatePacketToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk template obligation route obstruction frontier transport provenance nameCert =>
      change
        some
          (AuditMapTemplatePacketUp.mk
            (auditMapTemplatePacketDecodeBHist
              (auditMapTemplatePacketEncodeBHist template))
            (auditMapTemplatePacketDecodeBHist
              (auditMapTemplatePacketEncodeBHist obligation))
            (auditMapTemplatePacketDecodeBHist (auditMapTemplatePacketEncodeBHist route))
            (auditMapTemplatePacketDecodeBHist
              (auditMapTemplatePacketEncodeBHist obstruction))
            (auditMapTemplatePacketDecodeBHist
              (auditMapTemplatePacketEncodeBHist frontier))
            (auditMapTemplatePacketDecodeBHist
              (auditMapTemplatePacketEncodeBHist transport))
            (auditMapTemplatePacketDecodeBHist
              (auditMapTemplatePacketEncodeBHist provenance))
            (auditMapTemplatePacketDecodeBHist
              (auditMapTemplatePacketEncodeBHist nameCert))) =
          some
            (AuditMapTemplatePacketUp.mk template obligation route obstruction frontier
              transport provenance nameCert)
      rw [auditMapTemplatePacketDecode_encode_bhist template,
        auditMapTemplatePacketDecode_encode_bhist obligation,
        auditMapTemplatePacketDecode_encode_bhist route,
        auditMapTemplatePacketDecode_encode_bhist obstruction,
        auditMapTemplatePacketDecode_encode_bhist frontier,
        auditMapTemplatePacketDecode_encode_bhist transport,
        auditMapTemplatePacketDecode_encode_bhist provenance,
        auditMapTemplatePacketDecode_encode_bhist nameCert]

private theorem auditMapTemplatePacketToEventFlow_injective
    {x y : AuditMapTemplatePacketUp} :
    auditMapTemplatePacketToEventFlow x = auditMapTemplatePacketToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      auditMapTemplatePacketFromEventFlow (auditMapTemplatePacketToEventFlow x) =
        auditMapTemplatePacketFromEventFlow (auditMapTemplatePacketToEventFlow y) :=
    congrArg auditMapTemplatePacketFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (auditMapTemplatePacket_round_trip x).symm
      (Eq.trans hread (auditMapTemplatePacket_round_trip y)))

instance auditMapTemplatePacketBHistCarrier : BHistCarrier AuditMapTemplatePacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := auditMapTemplatePacketToEventFlow
  fromEventFlow := auditMapTemplatePacketFromEventFlow

instance auditMapTemplatePacketChapterTasteGate :
    ChapterTasteGate AuditMapTemplatePacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change auditMapTemplatePacketFromEventFlow (auditMapTemplatePacketToEventFlow x) = some x
    exact auditMapTemplatePacket_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (auditMapTemplatePacketToEventFlow_injective heq)

instance auditMapTemplatePacketFieldFaithful : FieldFaithful AuditMapTemplatePacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | AuditMapTemplatePacketUp.mk template obligation route obstruction frontier transport
        provenance nameCert =>
        [template, obligation, route, obstruction, frontier, transport, provenance, nameCert]
  field_faithful := by
    intro x y h
    cases x with
    | mk template₁ obligation₁ route₁ obstruction₁ frontier₁ transport₁ provenance₁
        nameCert₁ =>
        cases y with
        | mk template₂ obligation₂ route₂ obstruction₂ frontier₂ transport₂ provenance₂
            nameCert₂ =>
            injection h with htemplate t1
            injection t1 with hobligation t2
            injection t2 with hroute t3
            injection t3 with hobstruction t4
            injection t4 with hfrontier t5
            injection t5 with htransport t6
            injection t6 with hprovenance t7
            injection t7 with hnameCert _
            cases htemplate
            cases hobligation
            cases hroute
            cases hobstruction
            cases hfrontier
            cases htransport
            cases hprovenance
            cases hnameCert
            rfl

instance auditMapTemplatePacketNontrivial : Nontrivial AuditMapTemplatePacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AuditMapTemplatePacketUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      AuditMapTemplatePacketUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate AuditMapTemplatePacketUp :=
  -- BEDC touchpoint anchor: BHist BMark
  auditMapTemplatePacketChapterTasteGate

theorem AuditMapTemplatePacketTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      auditMapTemplatePacketDecodeBHist (auditMapTemplatePacketEncodeBHist h) = h) ∧
      (∀ x : AuditMapTemplatePacketUp,
        auditMapTemplatePacketFromEventFlow (auditMapTemplatePacketToEventFlow x) = some x) ∧
        (∀ x y : AuditMapTemplatePacketUp,
          auditMapTemplatePacketToEventFlow x =
            auditMapTemplatePacketToEventFlow y → x = y) ∧
          auditMapTemplatePacketEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact auditMapTemplatePacketDecode_encode_bhist
  · constructor
    · exact auditMapTemplatePacket_round_trip
    · constructor
      · intro x y heq
        exact auditMapTemplatePacketToEventFlow_injective heq
      · rfl

end BEDC.Derived.AuditMapTemplatePacketUp
