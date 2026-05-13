import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICConfluenceAuditPacketUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICConfluenceAuditPacketUp : Type where
  | mk :
      (diamond closedStar normal atomFragments substitutionBoundary subjectReduction
        transports routes provenance localName : BHist) →
      MetaCICConfluenceAuditPacketUp
  deriving DecidableEq

private def metaCICConfluenceAuditPacketEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaCICConfluenceAuditPacketEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaCICConfluenceAuditPacketEncodeBHist h

private def metaCICConfluenceAuditPacketDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaCICConfluenceAuditPacketDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaCICConfluenceAuditPacketDecodeBHist tail)

private theorem metaCICConfluenceAuditPacket_decode_encode_bhist :
    ∀ h : BHist,
      metaCICConfluenceAuditPacketDecodeBHist
        (metaCICConfluenceAuditPacketEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def metaCICConfluenceAuditPacketToEventFlow :
    MetaCICConfluenceAuditPacketUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICConfluenceAuditPacketUp.mk diamond closedStar normal atomFragments
      substitutionBoundary subjectReduction transports routes provenance localName =>
      [[BMark.b0],
        metaCICConfluenceAuditPacketEncodeBHist diamond,
        [BMark.b1, BMark.b0],
        metaCICConfluenceAuditPacketEncodeBHist closedStar,
        [BMark.b1, BMark.b1, BMark.b0],
        metaCICConfluenceAuditPacketEncodeBHist normal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICConfluenceAuditPacketEncodeBHist atomFragments,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICConfluenceAuditPacketEncodeBHist substitutionBoundary,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICConfluenceAuditPacketEncodeBHist subjectReduction,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICConfluenceAuditPacketEncodeBHist transports,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        metaCICConfluenceAuditPacketEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        metaCICConfluenceAuditPacketEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        metaCICConfluenceAuditPacketEncodeBHist localName]

private def metaCICConfluenceAuditPacketDecodeRows :
    RawEvent → RawEvent → RawEvent → RawEvent → RawEvent → RawEvent → RawEvent →
      RawEvent → RawEvent → RawEvent → MetaCICConfluenceAuditPacketUp
  -- BEDC touchpoint anchor: BHist BMark
  | diamond, closedStar, normal, atomFragments, substitutionBoundary, subjectReduction,
      transports, routes, provenance, localName =>
      MetaCICConfluenceAuditPacketUp.mk
        (metaCICConfluenceAuditPacketDecodeBHist diamond)
        (metaCICConfluenceAuditPacketDecodeBHist closedStar)
        (metaCICConfluenceAuditPacketDecodeBHist normal)
        (metaCICConfluenceAuditPacketDecodeBHist atomFragments)
        (metaCICConfluenceAuditPacketDecodeBHist substitutionBoundary)
        (metaCICConfluenceAuditPacketDecodeBHist subjectReduction)
        (metaCICConfluenceAuditPacketDecodeBHist transports)
        (metaCICConfluenceAuditPacketDecodeBHist routes)
        (metaCICConfluenceAuditPacketDecodeBHist provenance)
        (metaCICConfluenceAuditPacketDecodeBHist localName)

private theorem metaCICConfluenceAuditPacket_mk_congr
    {diamond diamond' closedStar closedStar' normal normal' atomFragments atomFragments'
      substitutionBoundary substitutionBoundary' subjectReduction subjectReduction'
      transports transports' routes routes' provenance provenance' localName localName' : BHist}
    (hDiamond : diamond' = diamond)
    (hClosedStar : closedStar' = closedStar)
    (hNormal : normal' = normal)
    (hAtomFragments : atomFragments' = atomFragments)
    (hSubstitutionBoundary : substitutionBoundary' = substitutionBoundary)
    (hSubjectReduction : subjectReduction' = subjectReduction)
    (hTransports : transports' = transports)
    (hRoutes : routes' = routes)
    (hProvenance : provenance' = provenance)
    (hLocalName : localName' = localName) :
    MetaCICConfluenceAuditPacketUp.mk diamond' closedStar' normal' atomFragments'
        substitutionBoundary' subjectReduction' transports' routes' provenance' localName' =
      MetaCICConfluenceAuditPacketUp.mk diamond closedStar normal atomFragments
        substitutionBoundary subjectReduction transports routes provenance localName := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hDiamond
  cases hClosedStar
  cases hNormal
  cases hAtomFragments
  cases hSubstitutionBoundary
  cases hSubjectReduction
  cases hTransports
  cases hRoutes
  cases hProvenance
  cases hLocalName
  rfl

private def metaCICConfluenceAuditPacketFromEventFlow :
    EventFlow → Option MetaCICConfluenceAuditPacketUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | diamond :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | closedStar :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | normal :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | atomFragments :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | substitutionBoundary :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | subjectReduction :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | transports :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | routes :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | provenance :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | localName :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (metaCICConfluenceAuditPacketDecodeRows
                                                                                          diamond
                                                                                          closedStar
                                                                                          normal
                                                                                          atomFragments
                                                                                          substitutionBoundary
                                                                                          subjectReduction
                                                                                          transports
                                                                                          routes
                                                                                          provenance
                                                                                          localName)
                                                                                  | _ :: _ => none

private theorem metaCICConfluenceAuditPacket_round_trip :
    ∀ x : MetaCICConfluenceAuditPacketUp,
      metaCICConfluenceAuditPacketFromEventFlow
        (metaCICConfluenceAuditPacketToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk diamond closedStar normal atomFragments substitutionBoundary subjectReduction
      transports routes provenance localName =>
      change
        some
          (MetaCICConfluenceAuditPacketUp.mk
            (metaCICConfluenceAuditPacketDecodeBHist
              (metaCICConfluenceAuditPacketEncodeBHist diamond))
            (metaCICConfluenceAuditPacketDecodeBHist
              (metaCICConfluenceAuditPacketEncodeBHist closedStar))
            (metaCICConfluenceAuditPacketDecodeBHist
              (metaCICConfluenceAuditPacketEncodeBHist normal))
            (metaCICConfluenceAuditPacketDecodeBHist
              (metaCICConfluenceAuditPacketEncodeBHist atomFragments))
            (metaCICConfluenceAuditPacketDecodeBHist
              (metaCICConfluenceAuditPacketEncodeBHist substitutionBoundary))
            (metaCICConfluenceAuditPacketDecodeBHist
              (metaCICConfluenceAuditPacketEncodeBHist subjectReduction))
            (metaCICConfluenceAuditPacketDecodeBHist
              (metaCICConfluenceAuditPacketEncodeBHist transports))
            (metaCICConfluenceAuditPacketDecodeBHist
              (metaCICConfluenceAuditPacketEncodeBHist routes))
            (metaCICConfluenceAuditPacketDecodeBHist
              (metaCICConfluenceAuditPacketEncodeBHist provenance))
            (metaCICConfluenceAuditPacketDecodeBHist
              (metaCICConfluenceAuditPacketEncodeBHist localName))) =
          some
            (MetaCICConfluenceAuditPacketUp.mk diamond closedStar normal atomFragments
              substitutionBoundary subjectReduction transports routes provenance localName)
      exact
        congrArg some
          (metaCICConfluenceAuditPacket_mk_congr
            (metaCICConfluenceAuditPacket_decode_encode_bhist diamond)
            (metaCICConfluenceAuditPacket_decode_encode_bhist closedStar)
            (metaCICConfluenceAuditPacket_decode_encode_bhist normal)
            (metaCICConfluenceAuditPacket_decode_encode_bhist atomFragments)
            (metaCICConfluenceAuditPacket_decode_encode_bhist substitutionBoundary)
            (metaCICConfluenceAuditPacket_decode_encode_bhist subjectReduction)
            (metaCICConfluenceAuditPacket_decode_encode_bhist transports)
            (metaCICConfluenceAuditPacket_decode_encode_bhist routes)
            (metaCICConfluenceAuditPacket_decode_encode_bhist provenance)
            (metaCICConfluenceAuditPacket_decode_encode_bhist localName))

private theorem metaCICConfluenceAuditPacketToEventFlow_injective
    {x y : MetaCICConfluenceAuditPacketUp} :
    metaCICConfluenceAuditPacketToEventFlow x =
      metaCICConfluenceAuditPacketToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaCICConfluenceAuditPacketFromEventFlow
          (metaCICConfluenceAuditPacketToEventFlow x) =
        metaCICConfluenceAuditPacketFromEventFlow
          (metaCICConfluenceAuditPacketToEventFlow y) :=
    congrArg metaCICConfluenceAuditPacketFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metaCICConfluenceAuditPacket_round_trip x).symm
      (Eq.trans hread (metaCICConfluenceAuditPacket_round_trip y)))

instance metaCICConfluenceAuditPacketBHistCarrier :
    BHistCarrier MetaCICConfluenceAuditPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaCICConfluenceAuditPacketToEventFlow
  fromEventFlow := metaCICConfluenceAuditPacketFromEventFlow

instance metaCICConfluenceAuditPacketChapterTasteGate :
    ChapterTasteGate MetaCICConfluenceAuditPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metaCICConfluenceAuditPacketFromEventFlow
        (metaCICConfluenceAuditPacketToEventFlow x) = some x
    exact metaCICConfluenceAuditPacket_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metaCICConfluenceAuditPacketToEventFlow_injective heq)

instance metaCICConfluenceAuditPacketFieldFaithful :
    FieldFaithful MetaCICConfluenceAuditPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields
    | MetaCICConfluenceAuditPacketUp.mk diamond closedStar normal atomFragments
        substitutionBoundary subjectReduction transports routes provenance localName =>
        [diamond, closedStar, normal, atomFragments, substitutionBoundary, subjectReduction,
          transports, routes, provenance, localName]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk diamond closedStar normal atomFragments substitutionBoundary subjectReduction
        transports routes provenance localName =>
        cases y with
        | mk diamond' closedStar' normal' atomFragments' substitutionBoundary'
            subjectReduction' transports' routes' provenance' localName' =>
            cases hfields
            rfl

theorem MetaCICConfluenceAuditPacketTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      metaCICConfluenceAuditPacketDecodeBHist
        (metaCICConfluenceAuditPacketEncodeBHist h) = h) ∧
      (∀ x : MetaCICConfluenceAuditPacketUp,
        metaCICConfluenceAuditPacketFromEventFlow
          (metaCICConfluenceAuditPacketToEventFlow x) = some x) ∧
        (∀ x y : MetaCICConfluenceAuditPacketUp,
          metaCICConfluenceAuditPacketToEventFlow x =
            metaCICConfluenceAuditPacketToEventFlow y → x = y) ∧
          metaCICConfluenceAuditPacketEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact metaCICConfluenceAuditPacket_decode_encode_bhist
  · constructor
    · exact metaCICConfluenceAuditPacket_round_trip
    · constructor
      · intro x y heq
        exact metaCICConfluenceAuditPacketToEventFlow_injective heq
      · rfl

end BEDC.Derived.MetaCICConfluenceAuditPacketUp
