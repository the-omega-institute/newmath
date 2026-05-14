import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetacicDecidableAuditPacketUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetacicDecidableAuditPacketUp : Type where
  | mk :
      (checker sameTerm typing gallery boundedNormal boundary obstruction transport replay
        provenance localName : BHist) →
      MetacicDecidableAuditPacketUp
  deriving DecidableEq

def metacicDecidableAuditPacketEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metacicDecidableAuditPacketEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metacicDecidableAuditPacketEncodeBHist h

def metacicDecidableAuditPacketDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metacicDecidableAuditPacketDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metacicDecidableAuditPacketDecodeBHist tail)

private theorem metacicDecidableAuditPacket_decode_encode_bhist :
    ∀ h : BHist,
      metacicDecidableAuditPacketDecodeBHist
        (metacicDecidableAuditPacketEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def metacicDecidableAuditPacketToEventFlow :
    MetacicDecidableAuditPacketUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetacicDecidableAuditPacketUp.mk checker sameTerm typing gallery boundedNormal boundary
      obstruction transport replay provenance localName =>
      [[BMark.b0],
        metacicDecidableAuditPacketEncodeBHist checker,
        [BMark.b1, BMark.b0],
        metacicDecidableAuditPacketEncodeBHist sameTerm,
        [BMark.b1, BMark.b1, BMark.b0],
        metacicDecidableAuditPacketEncodeBHist typing,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metacicDecidableAuditPacketEncodeBHist gallery,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metacicDecidableAuditPacketEncodeBHist boundedNormal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metacicDecidableAuditPacketEncodeBHist boundary,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metacicDecidableAuditPacketEncodeBHist obstruction,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        metacicDecidableAuditPacketEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        metacicDecidableAuditPacketEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        metacicDecidableAuditPacketEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metacicDecidableAuditPacketEncodeBHist localName]

def metacicDecidableAuditPacketFromEventFlow :
    EventFlow → Option MetacicDecidableAuditPacketUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | checker :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | sameTerm :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | typing :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | gallery :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | boundedNormal :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | boundary :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | obstruction :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | transport ::
                                                                  rest15 =>
                                                                  match rest15
                                                                    with
                                                                  | [] => none
                                                                  | _tag8 ::
                                                                      rest16 =>
                                                                      match rest16
                                                                        with
                                                                      | [] =>
                                                                          none
                                                                      | replay ::
                                                                          rest17 =>
                                                                          match rest17
                                                                            with
                                                                          | [] =>
                                                                              none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match rest18
                                                                                with
                                                                              | [] =>
                                                                                  none
                                                                              | provenance ::
                                                                                  rest19 =>
                                                                                  match rest19
                                                                                    with
                                                                                  | [] =>
                                                                                      none
                                                                                  | _tag10 ::
                                                                                      rest20 =>
                                                                                      match rest20
                                                                                        with
                                                                                      | [] =>
                                                                                          none
                                                                                      | localName ::
                                                                                          rest21 =>
                                                                                          match rest21
                                                                                            with
                                                                                          | [] =>
                                                                                              some
                                                                                                (MetacicDecidableAuditPacketUp.mk
                                                                                                  (metacicDecidableAuditPacketDecodeBHist
                                                                                                    checker)
                                                                                                  (metacicDecidableAuditPacketDecodeBHist
                                                                                                    sameTerm)
                                                                                                  (metacicDecidableAuditPacketDecodeBHist
                                                                                                    typing)
                                                                                                  (metacicDecidableAuditPacketDecodeBHist
                                                                                                    gallery)
                                                                                                  (metacicDecidableAuditPacketDecodeBHist
                                                                                                    boundedNormal)
                                                                                                  (metacicDecidableAuditPacketDecodeBHist
                                                                                                    boundary)
                                                                                                  (metacicDecidableAuditPacketDecodeBHist
                                                                                                    obstruction)
                                                                                                  (metacicDecidableAuditPacketDecodeBHist
                                                                                                    transport)
                                                                                                  (metacicDecidableAuditPacketDecodeBHist
                                                                                                    replay)
                                                                                                  (metacicDecidableAuditPacketDecodeBHist
                                                                                                    provenance)
                                                                                                  (metacicDecidableAuditPacketDecodeBHist
                                                                                                    localName))
                                                                                          | _ :: _ =>
                                                                                              none

private theorem metacicDecidableAuditPacket_round_trip :
    ∀ x : MetacicDecidableAuditPacketUp,
      metacicDecidableAuditPacketFromEventFlow
        (metacicDecidableAuditPacketToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk checker sameTerm typing gallery boundedNormal boundary obstruction transport replay
      provenance localName =>
      change
        some
          (MetacicDecidableAuditPacketUp.mk
            (metacicDecidableAuditPacketDecodeBHist
              (metacicDecidableAuditPacketEncodeBHist checker))
            (metacicDecidableAuditPacketDecodeBHist
              (metacicDecidableAuditPacketEncodeBHist sameTerm))
            (metacicDecidableAuditPacketDecodeBHist
              (metacicDecidableAuditPacketEncodeBHist typing))
            (metacicDecidableAuditPacketDecodeBHist
              (metacicDecidableAuditPacketEncodeBHist gallery))
            (metacicDecidableAuditPacketDecodeBHist
              (metacicDecidableAuditPacketEncodeBHist boundedNormal))
            (metacicDecidableAuditPacketDecodeBHist
              (metacicDecidableAuditPacketEncodeBHist boundary))
            (metacicDecidableAuditPacketDecodeBHist
              (metacicDecidableAuditPacketEncodeBHist obstruction))
            (metacicDecidableAuditPacketDecodeBHist
              (metacicDecidableAuditPacketEncodeBHist transport))
            (metacicDecidableAuditPacketDecodeBHist
              (metacicDecidableAuditPacketEncodeBHist replay))
            (metacicDecidableAuditPacketDecodeBHist
              (metacicDecidableAuditPacketEncodeBHist provenance))
            (metacicDecidableAuditPacketDecodeBHist
              (metacicDecidableAuditPacketEncodeBHist localName))) =
          some
            (MetacicDecidableAuditPacketUp.mk checker sameTerm typing gallery boundedNormal
              boundary obstruction transport replay provenance localName)
      rw [metacicDecidableAuditPacket_decode_encode_bhist checker,
        metacicDecidableAuditPacket_decode_encode_bhist sameTerm,
        metacicDecidableAuditPacket_decode_encode_bhist typing,
        metacicDecidableAuditPacket_decode_encode_bhist gallery,
        metacicDecidableAuditPacket_decode_encode_bhist boundedNormal,
        metacicDecidableAuditPacket_decode_encode_bhist boundary,
        metacicDecidableAuditPacket_decode_encode_bhist obstruction,
        metacicDecidableAuditPacket_decode_encode_bhist transport,
        metacicDecidableAuditPacket_decode_encode_bhist replay,
        metacicDecidableAuditPacket_decode_encode_bhist provenance,
        metacicDecidableAuditPacket_decode_encode_bhist localName]

private theorem metacicDecidableAuditPacketToEventFlow_injective
    {x y : MetacicDecidableAuditPacketUp} :
    metacicDecidableAuditPacketToEventFlow x =
      metacicDecidableAuditPacketToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metacicDecidableAuditPacketFromEventFlow
          (metacicDecidableAuditPacketToEventFlow x) =
        metacicDecidableAuditPacketFromEventFlow
          (metacicDecidableAuditPacketToEventFlow y) :=
    congrArg metacicDecidableAuditPacketFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metacicDecidableAuditPacket_round_trip x).symm
      (Eq.trans hread (metacicDecidableAuditPacket_round_trip y)))

instance metacicDecidableAuditPacketBHistCarrier :
    BHistCarrier MetacicDecidableAuditPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metacicDecidableAuditPacketToEventFlow
  fromEventFlow := metacicDecidableAuditPacketFromEventFlow

instance metacicDecidableAuditPacketChapterTasteGate :
    ChapterTasteGate MetacicDecidableAuditPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metacicDecidableAuditPacketFromEventFlow
        (metacicDecidableAuditPacketToEventFlow x) = some x
    exact metacicDecidableAuditPacket_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metacicDecidableAuditPacketToEventFlow_injective heq)

instance metacicDecidableAuditPacketFieldFaithful :
    FieldFaithful MetacicDecidableAuditPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields
    | MetacicDecidableAuditPacketUp.mk checker sameTerm typing gallery boundedNormal boundary
        obstruction transport replay provenance localName =>
        [checker, sameTerm, typing, gallery, boundedNormal, boundary, obstruction, transport,
          replay, provenance, localName]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk checker sameTerm typing gallery boundedNormal boundary obstruction transport replay
        provenance localName =>
        cases y with
        | mk checker' sameTerm' typing' gallery' boundedNormal' boundary' obstruction'
            transport' replay' provenance' localName' =>
            injection hfields with hChecker hTail0
            injection hTail0 with hSameTerm hTail1
            injection hTail1 with hTyping hTail2
            injection hTail2 with hGallery hTail3
            injection hTail3 with hBoundedNormal hTail4
            injection hTail4 with hBoundary hTail5
            injection hTail5 with hObstruction hTail6
            injection hTail6 with hTransport hTail7
            injection hTail7 with hReplay hTail8
            injection hTail8 with hProvenance hTail9
            injection hTail9 with hLocalName _hNil
            cases hChecker
            cases hSameTerm
            cases hTyping
            cases hGallery
            cases hBoundedNormal
            cases hBoundary
            cases hObstruction
            cases hTransport
            cases hReplay
            cases hProvenance
            cases hLocalName
            rfl

theorem MetacicDecidableAuditPacketTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      metacicDecidableAuditPacketDecodeBHist
        (metacicDecidableAuditPacketEncodeBHist h) = h) ∧
      (∀ x : MetacicDecidableAuditPacketUp,
        metacicDecidableAuditPacketFromEventFlow
          (metacicDecidableAuditPacketToEventFlow x) = some x) ∧
        (∀ x y : MetacicDecidableAuditPacketUp,
          metacicDecidableAuditPacketToEventFlow x =
            metacicDecidableAuditPacketToEventFlow y → x = y) ∧
          metacicDecidableAuditPacketEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact metacicDecidableAuditPacket_decode_encode_bhist
  · constructor
    · exact metacicDecidableAuditPacket_round_trip
    · constructor
      · intro x y heq
        exact metacicDecidableAuditPacketToEventFlow_injective heq
      · rfl

end BEDC.Derived.MetacicDecidableAuditPacketUp
