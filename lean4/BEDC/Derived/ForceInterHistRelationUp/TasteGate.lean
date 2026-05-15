import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ForceInterHistRelationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ForceInterHistRelationUp : Type where
  | mk :
      (source classifier layerMap refusal invariant locality observerBridge transport
        continuation provenance localName : BHist) →
      ForceInterHistRelationUp
  deriving DecidableEq

def forceInterHistRelationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: forceInterHistRelationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: forceInterHistRelationEncodeBHist h

def forceInterHistRelationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (forceInterHistRelationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (forceInterHistRelationDecodeBHist tail)

private theorem forceInterHistRelationDecode_encode_bhist :
    ∀ h : BHist, forceInterHistRelationDecodeBHist (forceInterHistRelationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def forceInterHistRelationFields : ForceInterHistRelationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ForceInterHistRelationUp.mk source classifier layerMap refusal invariant locality
      observerBridge transport continuation provenance localName =>
      [source, classifier, layerMap, refusal, invariant, locality, observerBridge, transport,
        continuation, provenance, localName]

def forceInterHistRelationToEventFlow : ForceInterHistRelationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ForceInterHistRelationUp.mk source classifier layerMap refusal invariant locality
      observerBridge transport continuation provenance localName =>
      [[BMark.b0],
        forceInterHistRelationEncodeBHist source,
        [BMark.b1, BMark.b0],
        forceInterHistRelationEncodeBHist classifier,
        [BMark.b1, BMark.b1, BMark.b0],
        forceInterHistRelationEncodeBHist layerMap,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        forceInterHistRelationEncodeBHist refusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        forceInterHistRelationEncodeBHist invariant,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        forceInterHistRelationEncodeBHist locality,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        forceInterHistRelationEncodeBHist observerBridge,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        forceInterHistRelationEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        forceInterHistRelationEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        forceInterHistRelationEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        forceInterHistRelationEncodeBHist localName]

def forceInterHistRelationFromEventFlow : EventFlow → Option ForceInterHistRelationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | source :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | classifier :: rest3 =>
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
                              | refusal :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | invariant :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | locality :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | observerBridge :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | transport :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | continuation ::
                                                                          rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match rest18
                                                                                with
                                                                              | [] => none
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
                                                                                                (ForceInterHistRelationUp.mk
                                                                                                  (forceInterHistRelationDecodeBHist
                                                                                                    source)
                                                                                                  (forceInterHistRelationDecodeBHist
                                                                                                    classifier)
                                                                                                  (forceInterHistRelationDecodeBHist
                                                                                                    layerMap)
                                                                                                  (forceInterHistRelationDecodeBHist
                                                                                                    refusal)
                                                                                                  (forceInterHistRelationDecodeBHist
                                                                                                    invariant)
                                                                                                  (forceInterHistRelationDecodeBHist
                                                                                                    locality)
                                                                                                  (forceInterHistRelationDecodeBHist
                                                                                                    observerBridge)
                                                                                                  (forceInterHistRelationDecodeBHist
                                                                                                    transport)
                                                                                                  (forceInterHistRelationDecodeBHist
                                                                                                    continuation)
                                                                                                  (forceInterHistRelationDecodeBHist
                                                                                                    provenance)
                                                                                                  (forceInterHistRelationDecodeBHist
                                                                                                    localName))
                                                                                          | _ :: _ =>
                                                                                              none

private theorem forceInterHistRelation_round_trip :
    ∀ x : ForceInterHistRelationUp,
      forceInterHistRelationFromEventFlow (forceInterHistRelationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source classifier layerMap refusal invariant locality observerBridge transport
      continuation provenance localName =>
      change
        some
          (ForceInterHistRelationUp.mk
            (forceInterHistRelationDecodeBHist (forceInterHistRelationEncodeBHist source))
            (forceInterHistRelationDecodeBHist (forceInterHistRelationEncodeBHist classifier))
            (forceInterHistRelationDecodeBHist (forceInterHistRelationEncodeBHist layerMap))
            (forceInterHistRelationDecodeBHist (forceInterHistRelationEncodeBHist refusal))
            (forceInterHistRelationDecodeBHist (forceInterHistRelationEncodeBHist invariant))
            (forceInterHistRelationDecodeBHist (forceInterHistRelationEncodeBHist locality))
            (forceInterHistRelationDecodeBHist
              (forceInterHistRelationEncodeBHist observerBridge))
            (forceInterHistRelationDecodeBHist (forceInterHistRelationEncodeBHist transport))
            (forceInterHistRelationDecodeBHist (forceInterHistRelationEncodeBHist continuation))
            (forceInterHistRelationDecodeBHist (forceInterHistRelationEncodeBHist provenance))
            (forceInterHistRelationDecodeBHist (forceInterHistRelationEncodeBHist localName))) =
          some
            (ForceInterHistRelationUp.mk source classifier layerMap refusal invariant locality
              observerBridge transport continuation provenance localName)
      rw [forceInterHistRelationDecode_encode_bhist source,
        forceInterHistRelationDecode_encode_bhist classifier,
        forceInterHistRelationDecode_encode_bhist layerMap,
        forceInterHistRelationDecode_encode_bhist refusal,
        forceInterHistRelationDecode_encode_bhist invariant,
        forceInterHistRelationDecode_encode_bhist locality,
        forceInterHistRelationDecode_encode_bhist observerBridge,
        forceInterHistRelationDecode_encode_bhist transport,
        forceInterHistRelationDecode_encode_bhist continuation,
        forceInterHistRelationDecode_encode_bhist provenance,
        forceInterHistRelationDecode_encode_bhist localName]

private theorem forceInterHistRelationToEventFlow_injective {x y : ForceInterHistRelationUp} :
    forceInterHistRelationToEventFlow x = forceInterHistRelationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      forceInterHistRelationFromEventFlow (forceInterHistRelationToEventFlow x) =
        forceInterHistRelationFromEventFlow (forceInterHistRelationToEventFlow y) :=
    congrArg forceInterHistRelationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (forceInterHistRelation_round_trip x).symm
      (Eq.trans hread (forceInterHistRelation_round_trip y)))

private theorem ForceInterHistRelationTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : ForceInterHistRelationUp,
      forceInterHistRelationFields x = forceInterHistRelationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk source classifier layerMap refusal invariant locality observerBridge transport
      continuation provenance localName =>
      cases y with
      | mk source' classifier' layerMap' refusal' invariant' locality' observerBridge'
          transport' continuation' provenance' localName' =>
          injection hfields with hSource hTail0
          injection hTail0 with hClassifier hTail1
          injection hTail1 with hLayerMap hTail2
          injection hTail2 with hRefusal hTail3
          injection hTail3 with hInvariant hTail4
          injection hTail4 with hLocality hTail5
          injection hTail5 with hObserverBridge hTail6
          injection hTail6 with hTransport hTail7
          injection hTail7 with hContinuation hTail8
          injection hTail8 with hProvenance hTail9
          injection hTail9 with hLocalName _hNil
          cases hSource
          cases hClassifier
          cases hLayerMap
          cases hRefusal
          cases hInvariant
          cases hLocality
          cases hObserverBridge
          cases hTransport
          cases hContinuation
          cases hProvenance
          cases hLocalName
          rfl

instance forceInterHistRelationBHistCarrier : BHistCarrier ForceInterHistRelationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := forceInterHistRelationToEventFlow
  fromEventFlow := forceInterHistRelationFromEventFlow

instance forceInterHistRelationChapterTasteGate :
    ChapterTasteGate ForceInterHistRelationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change forceInterHistRelationFromEventFlow (forceInterHistRelationToEventFlow x) = some x
    exact forceInterHistRelation_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (forceInterHistRelationToEventFlow_injective heq)

instance forceInterHistRelationFieldFaithful : FieldFaithful ForceInterHistRelationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := forceInterHistRelationFields
  field_faithful := ForceInterHistRelationTasteGate_single_carrier_alignment_field_faithful

instance forceInterHistRelationNontrivial : Nontrivial ForceInterHistRelationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ForceInterHistRelationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ForceInterHistRelationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ForceInterHistRelationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  forceInterHistRelationChapterTasteGate

theorem ForceInterHistRelationTasteGate_single_carrier_alignment :
    (∀ h : BHist, forceInterHistRelationDecodeBHist (forceInterHistRelationEncodeBHist h) = h) ∧
      (∀ x : ForceInterHistRelationUp,
        forceInterHistRelationFromEventFlow (forceInterHistRelationToEventFlow x) = some x) ∧
        (∀ x y : ForceInterHistRelationUp,
          forceInterHistRelationToEventFlow x = forceInterHistRelationToEventFlow y → x = y) ∧
          forceInterHistRelationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨forceInterHistRelationDecode_encode_bhist,
      forceInterHistRelation_round_trip,
      (by
        intro x y heq
        exact forceInterHistRelationToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.ForceInterHistRelationUp
