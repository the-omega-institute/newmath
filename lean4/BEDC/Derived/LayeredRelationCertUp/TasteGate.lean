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
  | _tag0 :: chainA :: _tag1 :: chainB :: _tag2 :: layerMap :: _tag3 ::
      classifier :: _tag4 :: preserved :: _tag5 :: refused :: _tag6 :: exactness ::
      _tag7 :: failureBoundary :: _tag8 :: strength :: _tag9 :: transport :: _tag10 ::
      route :: _tag11 :: provenance :: _tag12 :: nameRow :: [] =>
      some
        (LayeredRelationCertUp.mk
          (layeredRelationCertDecodeBHist chainA)
          (layeredRelationCertDecodeBHist chainB)
          (layeredRelationCertDecodeBHist layerMap)
          (layeredRelationCertDecodeBHist classifier)
          (layeredRelationCertDecodeBHist preserved)
          (layeredRelationCertDecodeBHist refused)
          (layeredRelationCertDecodeBHist exactness)
          (layeredRelationCertDecodeBHist failureBoundary)
          (layeredRelationCertDecodeBHist strength)
          (layeredRelationCertDecodeBHist transport)
          (layeredRelationCertDecodeBHist route)
          (layeredRelationCertDecodeBHist provenance)
          (layeredRelationCertDecodeBHist nameRow))
  | _ => none

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

end BEDC.Derived.LayeredRelationCertUp
