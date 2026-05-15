import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LayeredRelationDisplayUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LayeredRelationDisplayUp : Type where
  | mk :
      (sourceA sourceB sourceLedger classifier layerMap preserved notPreserved exactness
        failureBoundary transport route provenance name : BHist) →
      LayeredRelationDisplayUp
  deriving DecidableEq

def layeredRelationDisplayEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: layeredRelationDisplayEncodeBHist h
  | BHist.e1 h => BMark.b1 :: layeredRelationDisplayEncodeBHist h

def layeredRelationDisplayDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (layeredRelationDisplayDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (layeredRelationDisplayDecodeBHist tail)

private theorem LayeredRelationDisplayTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      layeredRelationDisplayDecodeBHist (layeredRelationDisplayEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def layeredRelationDisplayFields : LayeredRelationDisplayUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LayeredRelationDisplayUp.mk sourceA sourceB sourceLedger classifier layerMap preserved
      notPreserved exactness failureBoundary transport route provenance name =>
      [sourceA, sourceB, sourceLedger, classifier, layerMap, preserved, notPreserved,
        exactness, failureBoundary, transport, route, provenance, name]

def layeredRelationDisplayToEventFlow : LayeredRelationDisplayUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (layeredRelationDisplayFields x).map layeredRelationDisplayEncodeBHist

private def layeredRelationDisplayDecodePacket
    (sourceA sourceB sourceLedger classifier layerMap preserved notPreserved exactness
      failureBoundary transport route provenance name : RawEvent) : LayeredRelationDisplayUp :=
  -- BEDC touchpoint anchor: BHist BMark
  LayeredRelationDisplayUp.mk
    (layeredRelationDisplayDecodeBHist sourceA)
    (layeredRelationDisplayDecodeBHist sourceB)
    (layeredRelationDisplayDecodeBHist sourceLedger)
    (layeredRelationDisplayDecodeBHist classifier)
    (layeredRelationDisplayDecodeBHist layerMap)
    (layeredRelationDisplayDecodeBHist preserved)
    (layeredRelationDisplayDecodeBHist notPreserved)
    (layeredRelationDisplayDecodeBHist exactness)
    (layeredRelationDisplayDecodeBHist failureBoundary)
    (layeredRelationDisplayDecodeBHist transport)
    (layeredRelationDisplayDecodeBHist route)
    (layeredRelationDisplayDecodeBHist provenance)
    (layeredRelationDisplayDecodeBHist name)

def layeredRelationDisplayFromEventFlow : EventFlow → Option LayeredRelationDisplayUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | sourceA :: rest0 =>
      match rest0 with
      | [] => none
      | sourceB :: rest1 =>
          match rest1 with
          | [] => none
          | sourceLedger :: rest2 =>
              match rest2 with
              | [] => none
              | classifier :: rest3 =>
                  match rest3 with
                  | [] => none
                  | layerMap :: rest4 =>
                      match rest4 with
                      | [] => none
                      | preserved :: rest5 =>
                          match rest5 with
                          | [] => none
                          | notPreserved :: rest6 =>
                              match rest6 with
                              | [] => none
                              | exactness :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | failureBoundary :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | transport :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | route :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | provenance :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | name :: rest12 =>
                                                      match rest12 with
                                                      | [] =>
                                                          some
                                                            (layeredRelationDisplayDecodePacket
                                                              sourceA sourceB sourceLedger
                                                              classifier layerMap preserved
                                                              notPreserved exactness
                                                              failureBoundary transport route
                                                              provenance name)
                                                      | _ :: _ => none

private theorem LayeredRelationDisplayTasteGate_single_carrier_alignment_round :
    ∀ x : LayeredRelationDisplayUp,
      layeredRelationDisplayFromEventFlow (layeredRelationDisplayToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk sourceA sourceB sourceLedger classifier layerMap preserved notPreserved exactness
      failureBoundary transport route provenance name =>
      change
        some
          (layeredRelationDisplayDecodePacket
            (layeredRelationDisplayEncodeBHist sourceA)
            (layeredRelationDisplayEncodeBHist sourceB)
            (layeredRelationDisplayEncodeBHist sourceLedger)
            (layeredRelationDisplayEncodeBHist classifier)
            (layeredRelationDisplayEncodeBHist layerMap)
            (layeredRelationDisplayEncodeBHist preserved)
            (layeredRelationDisplayEncodeBHist notPreserved)
            (layeredRelationDisplayEncodeBHist exactness)
            (layeredRelationDisplayEncodeBHist failureBoundary)
            (layeredRelationDisplayEncodeBHist transport)
            (layeredRelationDisplayEncodeBHist route)
            (layeredRelationDisplayEncodeBHist provenance)
            (layeredRelationDisplayEncodeBHist name)) =
          some
            (LayeredRelationDisplayUp.mk sourceA sourceB sourceLedger classifier layerMap
              preserved notPreserved exactness failureBoundary transport route provenance name)
      unfold layeredRelationDisplayDecodePacket
      rw [LayeredRelationDisplayTasteGate_single_carrier_alignment_decode sourceA,
        LayeredRelationDisplayTasteGate_single_carrier_alignment_decode sourceB,
        LayeredRelationDisplayTasteGate_single_carrier_alignment_decode sourceLedger,
        LayeredRelationDisplayTasteGate_single_carrier_alignment_decode classifier,
        LayeredRelationDisplayTasteGate_single_carrier_alignment_decode layerMap,
        LayeredRelationDisplayTasteGate_single_carrier_alignment_decode preserved,
        LayeredRelationDisplayTasteGate_single_carrier_alignment_decode notPreserved,
        LayeredRelationDisplayTasteGate_single_carrier_alignment_decode exactness,
        LayeredRelationDisplayTasteGate_single_carrier_alignment_decode failureBoundary,
        LayeredRelationDisplayTasteGate_single_carrier_alignment_decode transport,
        LayeredRelationDisplayTasteGate_single_carrier_alignment_decode route,
        LayeredRelationDisplayTasteGate_single_carrier_alignment_decode provenance,
        LayeredRelationDisplayTasteGate_single_carrier_alignment_decode name]

private theorem LayeredRelationDisplayTasteGate_single_carrier_alignment_injective
    {x y : LayeredRelationDisplayUp} :
    layeredRelationDisplayToEventFlow x = layeredRelationDisplayToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      layeredRelationDisplayFromEventFlow (layeredRelationDisplayToEventFlow x) =
        layeredRelationDisplayFromEventFlow (layeredRelationDisplayToEventFlow y) :=
    congrArg layeredRelationDisplayFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LayeredRelationDisplayTasteGate_single_carrier_alignment_round x).symm
      (Eq.trans hread
        (LayeredRelationDisplayTasteGate_single_carrier_alignment_round y)))

private theorem layeredRelationDisplay_fields_faithful :
    ∀ x y : LayeredRelationDisplayUp,
      layeredRelationDisplayFields x = layeredRelationDisplayFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk sourceA1 sourceB1 sourceLedger1 classifier1 layerMap1 preserved1 notPreserved1
      exactness1 failureBoundary1 transport1 route1 provenance1 name1 =>
      cases y with
      | mk sourceA2 sourceB2 sourceLedger2 classifier2 layerMap2 preserved2 notPreserved2
          exactness2 failureBoundary2 transport2 route2 provenance2 name2 =>
          injection hfields with hSourceA tail0
          injection tail0 with hSourceB tail1
          injection tail1 with hSourceLedger tail2
          injection tail2 with hClassifier tail3
          injection tail3 with hLayerMap tail4
          injection tail4 with hPreserved tail5
          injection tail5 with hNotPreserved tail6
          injection tail6 with hExactness tail7
          injection tail7 with hFailureBoundary tail8
          injection tail8 with hTransport tail9
          injection tail9 with hRoute tail10
          injection tail10 with hProvenance tail11
          injection tail11 with hName _
          cases hSourceA
          cases hSourceB
          cases hSourceLedger
          cases hClassifier
          cases hLayerMap
          cases hPreserved
          cases hNotPreserved
          cases hExactness
          cases hFailureBoundary
          cases hTransport
          cases hRoute
          cases hProvenance
          cases hName
          rfl

instance layeredRelationDisplayBHistCarrier : BHistCarrier LayeredRelationDisplayUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := layeredRelationDisplayToEventFlow
  fromEventFlow := layeredRelationDisplayFromEventFlow

instance layeredRelationDisplayChapterTasteGate :
    ChapterTasteGate LayeredRelationDisplayUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change layeredRelationDisplayFromEventFlow (layeredRelationDisplayToEventFlow x) = some x
    exact LayeredRelationDisplayTasteGate_single_carrier_alignment_round x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LayeredRelationDisplayTasteGate_single_carrier_alignment_injective heq)

instance layeredRelationDisplayFieldFaithful : FieldFaithful LayeredRelationDisplayUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := layeredRelationDisplayFields
  field_faithful := layeredRelationDisplay_fields_faithful

instance layeredRelationDisplayNontrivial : Nontrivial LayeredRelationDisplayUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LayeredRelationDisplayUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      LayeredRelationDisplayUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LayeredRelationDisplayUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change layeredRelationDisplayFromEventFlow (layeredRelationDisplayToEventFlow x) = some x
    exact LayeredRelationDisplayTasteGate_single_carrier_alignment_round x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LayeredRelationDisplayTasteGate_single_carrier_alignment_injective heq)

theorem LayeredRelationDisplayTasteGate_single_carrier_alignment :
    (∀ h : BHist, layeredRelationDisplayDecodeBHist
        (layeredRelationDisplayEncodeBHist h) = h) ∧
      (∀ x : LayeredRelationDisplayUp,
        layeredRelationDisplayFromEventFlow (layeredRelationDisplayToEventFlow x) = some x) ∧
        (∀ x y : LayeredRelationDisplayUp,
          layeredRelationDisplayToEventFlow x = layeredRelationDisplayToEventFlow y →
            x = y) ∧
          layeredRelationDisplayEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact And.intro LayeredRelationDisplayTasteGate_single_carrier_alignment_decode
    (And.intro LayeredRelationDisplayTasteGate_single_carrier_alignment_round
      (And.intro
        (by
          intro x y heq
          exact LayeredRelationDisplayTasteGate_single_carrier_alignment_injective heq)
        rfl))

end BEDC.Derived.LayeredRelationDisplayUp
