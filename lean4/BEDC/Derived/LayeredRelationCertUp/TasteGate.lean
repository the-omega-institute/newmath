import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LayeredRelationCertUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LayeredRelationCertUp : Type where
  | mk
      (chainA chainB layerMap classifier preserved refused exactness failureBoundary
        strength transport route provenance nameRow : BHist) :
      LayeredRelationCertUp
  deriving DecidableEq

private def layeredRelationCertEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: layeredRelationCertEncodeBHist h
  | BHist.e1 h => BMark.b1 :: layeredRelationCertEncodeBHist h

private def layeredRelationCertDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (layeredRelationCertDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (layeredRelationCertDecodeBHist tail)

private theorem layeredRelationCertDecode_encode_bhist :
    ∀ h : BHist, layeredRelationCertDecodeBHist (layeredRelationCertEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def layeredRelationCertToEventFlow : LayeredRelationCertUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LayeredRelationCertUp.mk chainA chainB layerMap classifier preserved refused exactness
      failureBoundary strength transport route provenance nameRow =>
      [[BMark.b0],
        layeredRelationCertEncodeBHist chainA,
        [BMark.b1, BMark.b0],
        layeredRelationCertEncodeBHist chainB,
        [BMark.b1, BMark.b1, BMark.b0],
        layeredRelationCertEncodeBHist layerMap,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        layeredRelationCertEncodeBHist classifier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        layeredRelationCertEncodeBHist preserved,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        layeredRelationCertEncodeBHist refused,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        layeredRelationCertEncodeBHist exactness,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        layeredRelationCertEncodeBHist failureBoundary,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        layeredRelationCertEncodeBHist strength,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        layeredRelationCertEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        layeredRelationCertEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        layeredRelationCertEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        layeredRelationCertEncodeBHist nameRow]

private def layeredRelationCertFromEventFlow : EventFlow → Option LayeredRelationCertUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | chainA :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | chainB :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | layerMap :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | classifier :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | preserved :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | refused :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | exactness :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | failureBoundary ::
                                                                  rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | strength ::
                                                                          rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match
                                                                                rest18
                                                                              with
                                                                              | [] =>
                                                                                  none
                                                                              | transport ::
                                                                                  rest19 =>
                                                                                  match
                                                                                    rest19
                                                                                  with
                                                                                  | [] =>
                                                                                      none
                                                                                  | _tag10 ::
                                                                                      rest20 =>
                                                                                      match
                                                                                        rest20
                                                                                      with
                                                                                      | [] =>
                                                                                          none
                                                                                      | route ::
                                                                                          rest21 =>
                                                                                          match
                                                                                            rest21
                                                                                          with
                                                                                          | [] =>
                                                                                              none
                                                                                          | _tag11 ::
                                                                                              rest22 =>
                                                                                              match
                                                                                                rest22
                                                                                              with
                                                                                              | [] =>
                                                                                                  none
                                                                                              | provenance ::
                                                                                                  rest23 =>
                                                                                                  match
                                                                                                    rest23
                                                                                                  with
                                                                                                  | [] =>
                                                                                                      none
                                                                                                  | _tag12 ::
                                                                                                      rest24 =>
                                                                                                      match
                                                                                                        rest24
                                                                                                      with
                                                                                                      | [] =>
                                                                                                          none
                                                                                                      | nameRow ::
                                                                                                          rest25 =>
                                                                                                          match
                                                                                                            rest25
                                                                                                          with
                                                                                                          | [] =>
                                                                                                              some
                                                                                                                (LayeredRelationCertUp.mk
                                                                                                                  (layeredRelationCertDecodeBHist
                                                                                                                    chainA)
                                                                                                                  (layeredRelationCertDecodeBHist
                                                                                                                    chainB)
                                                                                                                  (layeredRelationCertDecodeBHist
                                                                                                                    layerMap)
                                                                                                                  (layeredRelationCertDecodeBHist
                                                                                                                    classifier)
                                                                                                                  (layeredRelationCertDecodeBHist
                                                                                                                    preserved)
                                                                                                                  (layeredRelationCertDecodeBHist
                                                                                                                    refused)
                                                                                                                  (layeredRelationCertDecodeBHist
                                                                                                                    exactness)
                                                                                                                  (layeredRelationCertDecodeBHist
                                                                                                                    failureBoundary)
                                                                                                                  (layeredRelationCertDecodeBHist
                                                                                                                    strength)
                                                                                                                  (layeredRelationCertDecodeBHist
                                                                                                                    transport)
                                                                                                                  (layeredRelationCertDecodeBHist
                                                                                                                    route)
                                                                                                                  (layeredRelationCertDecodeBHist
                                                                                                                    provenance)
                                                                                                                  (layeredRelationCertDecodeBHist
                                                                                                                    nameRow))
                                                                                                          | _ ::
                                                                                                              _ =>
                                                                                                              none

private theorem layeredRelationCert_round_trip :
    ∀ x : LayeredRelationCertUp,
      layeredRelationCertFromEventFlow (layeredRelationCertToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk chainA chainB layerMap classifier preserved refused exactness failureBoundary
      strength transport route provenance nameRow =>
      change
        some
          (LayeredRelationCertUp.mk
            (layeredRelationCertDecodeBHist (layeredRelationCertEncodeBHist chainA))
            (layeredRelationCertDecodeBHist (layeredRelationCertEncodeBHist chainB))
            (layeredRelationCertDecodeBHist (layeredRelationCertEncodeBHist layerMap))
            (layeredRelationCertDecodeBHist (layeredRelationCertEncodeBHist classifier))
            (layeredRelationCertDecodeBHist (layeredRelationCertEncodeBHist preserved))
            (layeredRelationCertDecodeBHist (layeredRelationCertEncodeBHist refused))
            (layeredRelationCertDecodeBHist (layeredRelationCertEncodeBHist exactness))
            (layeredRelationCertDecodeBHist
              (layeredRelationCertEncodeBHist failureBoundary))
            (layeredRelationCertDecodeBHist (layeredRelationCertEncodeBHist strength))
            (layeredRelationCertDecodeBHist (layeredRelationCertEncodeBHist transport))
            (layeredRelationCertDecodeBHist (layeredRelationCertEncodeBHist route))
            (layeredRelationCertDecodeBHist (layeredRelationCertEncodeBHist provenance))
            (layeredRelationCertDecodeBHist (layeredRelationCertEncodeBHist nameRow))) =
          some
            (LayeredRelationCertUp.mk chainA chainB layerMap classifier preserved refused
              exactness failureBoundary strength transport route provenance nameRow)
      rw [layeredRelationCertDecode_encode_bhist chainA,
        layeredRelationCertDecode_encode_bhist chainB,
        layeredRelationCertDecode_encode_bhist layerMap,
        layeredRelationCertDecode_encode_bhist classifier,
        layeredRelationCertDecode_encode_bhist preserved,
        layeredRelationCertDecode_encode_bhist refused,
        layeredRelationCertDecode_encode_bhist exactness,
        layeredRelationCertDecode_encode_bhist failureBoundary,
        layeredRelationCertDecode_encode_bhist strength,
        layeredRelationCertDecode_encode_bhist transport,
        layeredRelationCertDecode_encode_bhist route,
        layeredRelationCertDecode_encode_bhist provenance,
        layeredRelationCertDecode_encode_bhist nameRow]

private theorem layeredRelationCertToEventFlow_injective {x y : LayeredRelationCertUp} :
    layeredRelationCertToEventFlow x = layeredRelationCertToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      layeredRelationCertFromEventFlow (layeredRelationCertToEventFlow x) =
        layeredRelationCertFromEventFlow (layeredRelationCertToEventFlow y) :=
    congrArg layeredRelationCertFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (layeredRelationCert_round_trip x).symm
      (Eq.trans hread (layeredRelationCert_round_trip y)))

private def layeredRelationCertFields : LayeredRelationCertUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LayeredRelationCertUp.mk chainA chainB layerMap classifier preserved refused exactness
      failureBoundary strength transport route provenance nameRow =>
      [chainA, chainB, layerMap, classifier, preserved, refused, exactness,
        failureBoundary, strength, transport, route, provenance, nameRow]

private theorem layeredRelationCert_field_faithful :
    ∀ x y : LayeredRelationCertUp, layeredRelationCertFields x = layeredRelationCertFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk chainA1 chainB1 layerMap1 classifier1 preserved1 refused1 exactness1
      failureBoundary1 strength1 transport1 route1 provenance1 nameRow1 =>
      cases y with
      | mk chainA2 chainB2 layerMap2 classifier2 preserved2 refused2 exactness2
          failureBoundary2 strength2 transport2 route2 provenance2 nameRow2 =>
          cases h
          rfl

instance layeredRelationCertBHistCarrier : BHistCarrier LayeredRelationCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := layeredRelationCertToEventFlow
  fromEventFlow := layeredRelationCertFromEventFlow

instance layeredRelationCertChapterTasteGate : ChapterTasteGate LayeredRelationCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change layeredRelationCertFromEventFlow (layeredRelationCertToEventFlow x) = some x
    exact layeredRelationCert_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (layeredRelationCertToEventFlow_injective heq)

instance layeredRelationCertFieldFaithful : FieldFaithful LayeredRelationCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := layeredRelationCertFields
  field_faithful := layeredRelationCert_field_faithful

instance layeredRelationCertNontrivial : Nontrivial LayeredRelationCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LayeredRelationCertUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      LayeredRelationCertUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LayeredRelationCertUp :=
  -- BEDC touchpoint anchor: BHist BMark
  layeredRelationCertChapterTasteGate

theorem LayeredRelationCert_refused_row_concrete_boundary
    {chainA chainB layerMap classifier preserved exactness failureBoundary strength transport
      route provenance nameRow : BHist} :
    LayeredRelationCertUp.mk chainA chainB layerMap classifier preserved BHist.Empty exactness
        failureBoundary strength transport route provenance nameRow ≠
      LayeredRelationCertUp.mk chainA chainB layerMap classifier preserved
        (BHist.e0 BHist.Empty) exactness failureBoundary strength transport route provenance
        nameRow := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  cases h

theorem LayeredRelationCertTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate LayeredRelationCertUp) ∧
      Nonempty (FieldFaithful LayeredRelationCertUp) ∧
        Nonempty (Nontrivial LayeredRelationCertUp) ∧
          (∀ h : BHist, layeredRelationCertDecodeBHist (layeredRelationCertEncodeBHist h) = h) ∧
            (∀ x : LayeredRelationCertUp,
              layeredRelationCertFromEventFlow (layeredRelationCertToEventFlow x) = some x) ∧
              (∀ x y : LayeredRelationCertUp,
                layeredRelationCertToEventFlow x = layeredRelationCertToEventFlow y → x = y) ∧
                LayeredRelationCertUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                    BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                    BHist.Empty BHist.Empty BHist.Empty ≠
                  LayeredRelationCertUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                    BHist.Empty (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
                    BHist.Empty BHist.Empty BHist.Empty BHist.Empty := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨layeredRelationCertChapterTasteGate⟩
  · constructor
    · exact ⟨layeredRelationCertFieldFaithful⟩
    · constructor
      · exact ⟨layeredRelationCertNontrivial⟩
      · constructor
        · exact layeredRelationCertDecode_encode_bhist
        · constructor
          · exact layeredRelationCert_round_trip
          · constructor
            · intro x y heq
              exact layeredRelationCertToEventFlow_injective heq
            · intro h
              cases h

end BEDC.Derived.LayeredRelationCertUp
