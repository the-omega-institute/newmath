import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LayeredRelationCertUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LayeredRelationCertUp : Type where
  | mk :
      (sameSchema sourceLeft sourceRight layerMap classifier preserved notPreserved ledger
        exactness failure strength transport routes provenance nameCert : BHist) →
      LayeredRelationCertUp
  deriving DecidableEq

def layeredRelationCertEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: layeredRelationCertEncodeBHist h
  | BHist.e1 h => BMark.b1 :: layeredRelationCertEncodeBHist h

def layeredRelationCertDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (layeredRelationCertDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (layeredRelationCertDecodeBHist tail)

private theorem layeredRelationCert_decode_encode_bhist :
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

def layeredRelationCertFields : LayeredRelationCertUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LayeredRelationCertUp.mk sameSchema sourceLeft sourceRight layerMap classifier preserved
      notPreserved ledger exactness failure strength transport routes provenance nameCert =>
      [sameSchema, sourceLeft, sourceRight, layerMap, classifier, preserved, notPreserved,
        ledger, exactness, failure, strength, transport, routes, provenance, nameCert]

def layeredRelationCertToEventFlow : LayeredRelationCertUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (layeredRelationCertFields x).map layeredRelationCertEncodeBHist

def layeredRelationCertFromEventFlow : EventFlow → Option LayeredRelationCertUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | sameSchema :: rest0 =>
      match rest0 with
      | [] => none
      | sourceLeft :: rest1 =>
          match rest1 with
          | [] => none
          | sourceRight :: rest2 =>
              match rest2 with
              | [] => none
              | layerMap :: rest3 =>
                  match rest3 with
                  | [] => none
                  | classifier :: rest4 =>
                      match rest4 with
                      | [] => none
                      | preserved :: rest5 =>
                          match rest5 with
                          | [] => none
                          | notPreserved :: rest6 =>
                              match rest6 with
                              | [] => none
                              | ledger :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | exactness :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | failure :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | strength :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transport :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | routes :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | provenance :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | nameCert :: rest14 =>
                                                              match rest14 with
                                                              | [] =>
                                                                  some
                                                                    (LayeredRelationCertUp.mk
                                                                      (layeredRelationCertDecodeBHist
                                                                        sameSchema)
                                                                      (layeredRelationCertDecodeBHist
                                                                        sourceLeft)
                                                                      (layeredRelationCertDecodeBHist
                                                                        sourceRight)
                                                                      (layeredRelationCertDecodeBHist
                                                                        layerMap)
                                                                      (layeredRelationCertDecodeBHist
                                                                        classifier)
                                                                      (layeredRelationCertDecodeBHist
                                                                        preserved)
                                                                      (layeredRelationCertDecodeBHist
                                                                        notPreserved)
                                                                      (layeredRelationCertDecodeBHist
                                                                        ledger)
                                                                      (layeredRelationCertDecodeBHist
                                                                        exactness)
                                                                      (layeredRelationCertDecodeBHist
                                                                        failure)
                                                                      (layeredRelationCertDecodeBHist
                                                                        strength)
                                                                      (layeredRelationCertDecodeBHist
                                                                        transport)
                                                                      (layeredRelationCertDecodeBHist
                                                                        routes)
                                                                      (layeredRelationCertDecodeBHist
                                                                        provenance)
                                                                      (layeredRelationCertDecodeBHist
                                                                        nameCert))
                                                              | _ :: _ => none

private theorem layeredRelationCert_round_trip :
    ∀ x : LayeredRelationCertUp,
      layeredRelationCertFromEventFlow (layeredRelationCertToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk sameSchema sourceLeft sourceRight layerMap classifier preserved notPreserved ledger
      exactness failure strength transport routes provenance nameCert =>
      change
        some
          (LayeredRelationCertUp.mk
            (layeredRelationCertDecodeBHist (layeredRelationCertEncodeBHist sameSchema))
            (layeredRelationCertDecodeBHist (layeredRelationCertEncodeBHist sourceLeft))
            (layeredRelationCertDecodeBHist (layeredRelationCertEncodeBHist sourceRight))
            (layeredRelationCertDecodeBHist (layeredRelationCertEncodeBHist layerMap))
            (layeredRelationCertDecodeBHist (layeredRelationCertEncodeBHist classifier))
            (layeredRelationCertDecodeBHist (layeredRelationCertEncodeBHist preserved))
            (layeredRelationCertDecodeBHist (layeredRelationCertEncodeBHist notPreserved))
            (layeredRelationCertDecodeBHist (layeredRelationCertEncodeBHist ledger))
            (layeredRelationCertDecodeBHist (layeredRelationCertEncodeBHist exactness))
            (layeredRelationCertDecodeBHist (layeredRelationCertEncodeBHist failure))
            (layeredRelationCertDecodeBHist (layeredRelationCertEncodeBHist strength))
            (layeredRelationCertDecodeBHist (layeredRelationCertEncodeBHist transport))
            (layeredRelationCertDecodeBHist (layeredRelationCertEncodeBHist routes))
            (layeredRelationCertDecodeBHist (layeredRelationCertEncodeBHist provenance))
            (layeredRelationCertDecodeBHist (layeredRelationCertEncodeBHist nameCert))) =
          some
            (LayeredRelationCertUp.mk sameSchema sourceLeft sourceRight layerMap classifier
              preserved notPreserved ledger exactness failure strength transport routes provenance
              nameCert)
      rw [layeredRelationCert_decode_encode_bhist sameSchema,
        layeredRelationCert_decode_encode_bhist sourceLeft,
        layeredRelationCert_decode_encode_bhist sourceRight,
        layeredRelationCert_decode_encode_bhist layerMap,
        layeredRelationCert_decode_encode_bhist classifier,
        layeredRelationCert_decode_encode_bhist preserved,
        layeredRelationCert_decode_encode_bhist notPreserved,
        layeredRelationCert_decode_encode_bhist ledger,
        layeredRelationCert_decode_encode_bhist exactness,
        layeredRelationCert_decode_encode_bhist failure,
        layeredRelationCert_decode_encode_bhist strength,
        layeredRelationCert_decode_encode_bhist transport,
        layeredRelationCert_decode_encode_bhist routes,
        layeredRelationCert_decode_encode_bhist provenance,
        layeredRelationCert_decode_encode_bhist nameCert]

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

private theorem layeredRelationCert_fields_faithful :
    ∀ x y : LayeredRelationCertUp,
      layeredRelationCertFields x = layeredRelationCertFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk sameSchema₁ sourceLeft₁ sourceRight₁ layerMap₁ classifier₁ preserved₁ notPreserved₁
      ledger₁ exactness₁ failure₁ strength₁ transport₁ routes₁ provenance₁ nameCert₁ =>
      cases y with
      | mk sameSchema₂ sourceLeft₂ sourceRight₂ layerMap₂ classifier₂ preserved₂
          notPreserved₂ ledger₂ exactness₂ failure₂ strength₂ transport₂ routes₂ provenance₂
          nameCert₂ =>
          cases hfields
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
  field_faithful := layeredRelationCert_fields_faithful

instance layeredRelationCertNontrivial : Nontrivial LayeredRelationCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LayeredRelationCertUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LayeredRelationCertUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LayeredRelationCertUp :=
  -- BEDC touchpoint anchor: BHist BMark
  layeredRelationCertChapterTasteGate

theorem LayeredRelationCertTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate LayeredRelationCertUp) ∧
      Nonempty (FieldFaithful LayeredRelationCertUp) ∧
        Nonempty (Nontrivial LayeredRelationCertUp) ∧
          (∀ h : BHist,
            layeredRelationCertDecodeBHist (layeredRelationCertEncodeBHist h) = h) ∧
            (∀ x : LayeredRelationCertUp,
              layeredRelationCertFromEventFlow (layeredRelationCertToEventFlow x) = some x) ∧
              (∀ x y : LayeredRelationCertUp,
                layeredRelationCertToEventFlow x = layeredRelationCertToEventFlow y → x = y) ∧
                layeredRelationCertEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨⟨layeredRelationCertChapterTasteGate⟩,
      ⟨layeredRelationCertFieldFaithful⟩,
      ⟨layeredRelationCertNontrivial⟩,
      layeredRelationCert_decode_encode_bhist,
      layeredRelationCert_round_trip,
      (fun _ _ heq => layeredRelationCertToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.LayeredRelationCertUp
