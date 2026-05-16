import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealityConstrainedApproximationTowerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealityConstrainedApproximationTowerUp : Type where
  | mk :
      (onticSource observationData model physicalSignature classifier compression ledger
        hsameTransport contRoute provenance localName : BHist) →
      RealityConstrainedApproximationTowerUp
  deriving DecidableEq

def realityConstrainedApproximationTowerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realityConstrainedApproximationTowerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realityConstrainedApproximationTowerEncodeBHist h

def realityConstrainedApproximationTowerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realityConstrainedApproximationTowerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realityConstrainedApproximationTowerDecodeBHist tail)

private theorem realityConstrainedApproximationTowerDecode_encode_bhist :
    ∀ h : BHist,
      realityConstrainedApproximationTowerDecodeBHist
        (realityConstrainedApproximationTowerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem realityConstrainedApproximationTower_mk_congr
    {onticSource onticSource' observationData observationData' model model'
      physicalSignature physicalSignature' classifier classifier' compression compression'
      ledger ledger' hsameTransport hsameTransport' contRoute contRoute'
      provenance provenance' localName localName' : BHist}
    (hOnticSource : onticSource' = onticSource)
    (hObservationData : observationData' = observationData)
    (hModel : model' = model)
    (hPhysicalSignature : physicalSignature' = physicalSignature)
    (hClassifier : classifier' = classifier)
    (hCompression : compression' = compression)
    (hLedger : ledger' = ledger)
    (hHsameTransport : hsameTransport' = hsameTransport)
    (hContRoute : contRoute' = contRoute)
    (hProvenance : provenance' = provenance)
    (hLocalName : localName' = localName) :
    RealityConstrainedApproximationTowerUp.mk onticSource' observationData' model'
        physicalSignature' classifier' compression' ledger' hsameTransport' contRoute'
        provenance' localName' =
      RealityConstrainedApproximationTowerUp.mk onticSource observationData model
        physicalSignature classifier compression ledger hsameTransport contRoute provenance
        localName := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hOnticSource
  cases hObservationData
  cases hModel
  cases hPhysicalSignature
  cases hClassifier
  cases hCompression
  cases hLedger
  cases hHsameTransport
  cases hContRoute
  cases hProvenance
  cases hLocalName
  rfl

private theorem realityConstrainedApproximationTowerEncodeBHist_injective {h k : BHist} :
    realityConstrainedApproximationTowerEncodeBHist h =
      realityConstrainedApproximationTowerEncodeBHist k → h = k := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hdecode :
      realityConstrainedApproximationTowerDecodeBHist
          (realityConstrainedApproximationTowerEncodeBHist h) =
        realityConstrainedApproximationTowerDecodeBHist
          (realityConstrainedApproximationTowerEncodeBHist k) :=
    congrArg realityConstrainedApproximationTowerDecodeBHist heq
  exact Eq.trans (realityConstrainedApproximationTowerDecode_encode_bhist h).symm
    (Eq.trans hdecode (realityConstrainedApproximationTowerDecode_encode_bhist k))

def realityConstrainedApproximationTowerFields :
    RealityConstrainedApproximationTowerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealityConstrainedApproximationTowerUp.mk onticSource observationData model
      physicalSignature classifier compression ledger hsameTransport contRoute provenance
      localName =>
      [onticSource, observationData, model, physicalSignature, classifier, compression, ledger,
        hsameTransport, contRoute, provenance, localName]

def realityConstrainedApproximationTowerToEventFlow :
    RealityConstrainedApproximationTowerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealityConstrainedApproximationTowerUp.mk onticSource observationData model
      physicalSignature classifier compression ledger hsameTransport contRoute provenance
      localName =>
      [realityConstrainedApproximationTowerEncodeBHist onticSource,
        realityConstrainedApproximationTowerEncodeBHist observationData,
        realityConstrainedApproximationTowerEncodeBHist model,
        realityConstrainedApproximationTowerEncodeBHist physicalSignature,
        realityConstrainedApproximationTowerEncodeBHist classifier,
        realityConstrainedApproximationTowerEncodeBHist compression,
        realityConstrainedApproximationTowerEncodeBHist ledger,
        realityConstrainedApproximationTowerEncodeBHist hsameTransport,
        realityConstrainedApproximationTowerEncodeBHist contRoute,
        realityConstrainedApproximationTowerEncodeBHist provenance,
        realityConstrainedApproximationTowerEncodeBHist localName]

def realityConstrainedApproximationTowerFromEventFlow :
    EventFlow → Option RealityConstrainedApproximationTowerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | onticSource :: rest0 =>
      match rest0 with
      | [] => none
      | observationData :: rest1 =>
          match rest1 with
          | [] => none
          | model :: rest2 =>
              match rest2 with
              | [] => none
              | physicalSignature :: rest3 =>
                  match rest3 with
                  | [] => none
                  | classifier :: rest4 =>
                      match rest4 with
                      | [] => none
                      | compression :: rest5 =>
                          match rest5 with
                          | [] => none
                          | ledger :: rest6 =>
                              match rest6 with
                              | [] => none
                              | hsameTransport :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | contRoute :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | provenance :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | localName :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (RealityConstrainedApproximationTowerUp.mk
                                                      (realityConstrainedApproximationTowerDecodeBHist
                                                        onticSource)
                                                      (realityConstrainedApproximationTowerDecodeBHist
                                                        observationData)
                                                      (realityConstrainedApproximationTowerDecodeBHist
                                                        model)
                                                      (realityConstrainedApproximationTowerDecodeBHist
                                                        physicalSignature)
                                                      (realityConstrainedApproximationTowerDecodeBHist
                                                        classifier)
                                                      (realityConstrainedApproximationTowerDecodeBHist
                                                        compression)
                                                      (realityConstrainedApproximationTowerDecodeBHist
                                                        ledger)
                                                      (realityConstrainedApproximationTowerDecodeBHist
                                                        hsameTransport)
                                                      (realityConstrainedApproximationTowerDecodeBHist
                                                        contRoute)
                                                      (realityConstrainedApproximationTowerDecodeBHist
                                                        provenance)
                                                      (realityConstrainedApproximationTowerDecodeBHist
                                                        localName))
                                              | _ :: _ => none

private theorem realityConstrainedApproximationTower_round_trip :
    ∀ x : RealityConstrainedApproximationTowerUp,
      realityConstrainedApproximationTowerFromEventFlow
        (realityConstrainedApproximationTowerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk onticSource observationData model physicalSignature classifier compression ledger
      hsameTransport contRoute provenance localName =>
      exact
        congrArg some
          (realityConstrainedApproximationTower_mk_congr
            (realityConstrainedApproximationTowerDecode_encode_bhist onticSource)
            (realityConstrainedApproximationTowerDecode_encode_bhist observationData)
            (realityConstrainedApproximationTowerDecode_encode_bhist model)
            (realityConstrainedApproximationTowerDecode_encode_bhist physicalSignature)
            (realityConstrainedApproximationTowerDecode_encode_bhist classifier)
            (realityConstrainedApproximationTowerDecode_encode_bhist compression)
            (realityConstrainedApproximationTowerDecode_encode_bhist ledger)
            (realityConstrainedApproximationTowerDecode_encode_bhist hsameTransport)
            (realityConstrainedApproximationTowerDecode_encode_bhist contRoute)
            (realityConstrainedApproximationTowerDecode_encode_bhist provenance)
            (realityConstrainedApproximationTowerDecode_encode_bhist localName))

private theorem realityConstrainedApproximationTowerToEventFlow_injective
    {x y : RealityConstrainedApproximationTowerUp} :
    realityConstrainedApproximationTowerToEventFlow x =
      realityConstrainedApproximationTowerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk onticSource observationData model physicalSignature classifier compression ledger
      hsameTransport contRoute provenance localName =>
      cases y with
      | mk onticSource' observationData' model' physicalSignature' classifier' compression'
          ledger' hsameTransport' contRoute' provenance' localName' =>
          injection heq with hOnticSource tail1
          injection tail1 with hObservationData tail2
          injection tail2 with hModel tail3
          injection tail3 with hPhysicalSignature tail4
          injection tail4 with hClassifier tail5
          injection tail5 with hCompression tail6
          injection tail6 with hLedger tail7
          injection tail7 with hHsameTransport tail8
          injection tail8 with hContRoute tail9
          injection tail9 with hProvenance tail10
          injection tail10 with hLocalName _
          exact
            realityConstrainedApproximationTower_mk_congr
              (realityConstrainedApproximationTowerEncodeBHist_injective hOnticSource)
              (realityConstrainedApproximationTowerEncodeBHist_injective hObservationData)
              (realityConstrainedApproximationTowerEncodeBHist_injective hModel)
              (realityConstrainedApproximationTowerEncodeBHist_injective hPhysicalSignature)
              (realityConstrainedApproximationTowerEncodeBHist_injective hClassifier)
              (realityConstrainedApproximationTowerEncodeBHist_injective hCompression)
              (realityConstrainedApproximationTowerEncodeBHist_injective hLedger)
              (realityConstrainedApproximationTowerEncodeBHist_injective hHsameTransport)
              (realityConstrainedApproximationTowerEncodeBHist_injective hContRoute)
              (realityConstrainedApproximationTowerEncodeBHist_injective hProvenance)
              (realityConstrainedApproximationTowerEncodeBHist_injective hLocalName)

private theorem realityConstrainedApproximationTower_field_faithful :
    ∀ x y : RealityConstrainedApproximationTowerUp,
      realityConstrainedApproximationTowerFields x =
        realityConstrainedApproximationTowerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk onticSource observationData model physicalSignature classifier compression ledger
      hsameTransport contRoute provenance localName =>
      cases y with
      | mk onticSource' observationData' model' physicalSignature' classifier' compression'
          ledger' hsameTransport' contRoute' provenance' localName' =>
          cases hfields
          rfl

instance realityConstrainedApproximationTowerBHistCarrier :
    BHistCarrier RealityConstrainedApproximationTowerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realityConstrainedApproximationTowerToEventFlow
  fromEventFlow := realityConstrainedApproximationTowerFromEventFlow

instance realityConstrainedApproximationTowerChapterTasteGate :
    ChapterTasteGate RealityConstrainedApproximationTowerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realityConstrainedApproximationTowerFromEventFlow
        (realityConstrainedApproximationTowerToEventFlow x) = some x
    exact realityConstrainedApproximationTower_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realityConstrainedApproximationTowerToEventFlow_injective heq)

instance realityConstrainedApproximationTowerFieldFaithful :
    FieldFaithful RealityConstrainedApproximationTowerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realityConstrainedApproximationTowerFields
  field_faithful := realityConstrainedApproximationTower_field_faithful

instance realityConstrainedApproximationTowerNontrivial :
    Nontrivial RealityConstrainedApproximationTowerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealityConstrainedApproximationTowerUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      RealityConstrainedApproximationTowerUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealityConstrainedApproximationTowerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realityConstrainedApproximationTowerChapterTasteGate

theorem RealityConstrainedApproximationTowerTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      realityConstrainedApproximationTowerDecodeBHist
        (realityConstrainedApproximationTowerEncodeBHist h) = h) ∧
      (∀ x : RealityConstrainedApproximationTowerUp,
        realityConstrainedApproximationTowerFromEventFlow
          (realityConstrainedApproximationTowerToEventFlow x) = some x) ∧
        (∀ x y : RealityConstrainedApproximationTowerUp,
          realityConstrainedApproximationTowerToEventFlow x =
            realityConstrainedApproximationTowerToEventFlow y → x = y) ∧
          realityConstrainedApproximationTowerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro h
    induction h with
    | Empty =>
        rfl
    | e0 h ih =>
        exact congrArg BHist.e0 ih
    | e1 h ih =>
        exact congrArg BHist.e1 ih
  · constructor
    · intro x
      cases x with
      | mk onticSource observationData model physicalSignature classifier compression ledger
          hsameTransport contRoute provenance localName =>
          exact
            congrArg some
              (realityConstrainedApproximationTower_mk_congr
                (realityConstrainedApproximationTowerDecode_encode_bhist onticSource)
                (realityConstrainedApproximationTowerDecode_encode_bhist observationData)
                (realityConstrainedApproximationTowerDecode_encode_bhist model)
                (realityConstrainedApproximationTowerDecode_encode_bhist physicalSignature)
                (realityConstrainedApproximationTowerDecode_encode_bhist classifier)
                (realityConstrainedApproximationTowerDecode_encode_bhist compression)
                (realityConstrainedApproximationTowerDecode_encode_bhist ledger)
                (realityConstrainedApproximationTowerDecode_encode_bhist hsameTransport)
                (realityConstrainedApproximationTowerDecode_encode_bhist contRoute)
                (realityConstrainedApproximationTowerDecode_encode_bhist provenance)
                (realityConstrainedApproximationTowerDecode_encode_bhist localName))
    · constructor
      · intro x y heq
        exact realityConstrainedApproximationTowerToEventFlow_injective heq
      · rfl

end BEDC.Derived.RealityConstrainedApproximationTowerUp
