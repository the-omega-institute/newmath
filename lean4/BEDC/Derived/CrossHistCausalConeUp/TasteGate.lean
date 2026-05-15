import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CrossHistCausalConeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CrossHistCausalConeUp : Type where
  | mk :
      (source target slotWindow affectedRoute maxRate observerSymmetry refusalRow
        hsameTransport contReplay packageProvenance localName : BHist) ->
      CrossHistCausalConeUp
  deriving DecidableEq

def crossHistCausalConeEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: crossHistCausalConeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: crossHistCausalConeEncodeBHist h

def crossHistCausalConeDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (crossHistCausalConeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (crossHistCausalConeDecodeBHist tail)

private theorem crossHistCausalConeDecode_encode_bhist :
    forall h : BHist,
      crossHistCausalConeDecodeBHist (crossHistCausalConeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def crossHistCausalConeToEventFlow : CrossHistCausalConeUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CrossHistCausalConeUp.mk source target slotWindow affectedRoute maxRate
      observerSymmetry refusalRow hsameTransport contReplay packageProvenance localName =>
      [[BMark.b0],
        crossHistCausalConeEncodeBHist source,
        [BMark.b1, BMark.b0],
        crossHistCausalConeEncodeBHist target,
        [BMark.b1, BMark.b1, BMark.b0],
        crossHistCausalConeEncodeBHist slotWindow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        crossHistCausalConeEncodeBHist affectedRoute,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        crossHistCausalConeEncodeBHist maxRate,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        crossHistCausalConeEncodeBHist observerSymmetry,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        crossHistCausalConeEncodeBHist refusalRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        crossHistCausalConeEncodeBHist hsameTransport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        crossHistCausalConeEncodeBHist contReplay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        crossHistCausalConeEncodeBHist packageProvenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        crossHistCausalConeEncodeBHist localName]

def crossHistCausalConeFromEventFlow : EventFlow -> Option CrossHistCausalConeUp
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
              | target :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | slotWindow :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | affectedRoute :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | maxRate :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | observerSymmetry :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | refusalRow :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | hsameTransport :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | contReplay :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | packageProvenance :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | localName :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] =>
                                                                                              some
                                                                                                (CrossHistCausalConeUp.mk
                                                                                                  (crossHistCausalConeDecodeBHist
                                                                                                    source)
                                                                                                  (crossHistCausalConeDecodeBHist
                                                                                                    target)
                                                                                                  (crossHistCausalConeDecodeBHist
                                                                                                    slotWindow)
                                                                                                  (crossHistCausalConeDecodeBHist
                                                                                                    affectedRoute)
                                                                                                  (crossHistCausalConeDecodeBHist
                                                                                                    maxRate)
                                                                                                  (crossHistCausalConeDecodeBHist
                                                                                                    observerSymmetry)
                                                                                                  (crossHistCausalConeDecodeBHist
                                                                                                    refusalRow)
                                                                                                  (crossHistCausalConeDecodeBHist
                                                                                                    hsameTransport)
                                                                                                  (crossHistCausalConeDecodeBHist
                                                                                                    contReplay)
                                                                                                  (crossHistCausalConeDecodeBHist
                                                                                                    packageProvenance)
                                                                                                  (crossHistCausalConeDecodeBHist
                                                                                                    localName))
                                                                                          | _ :: _ => none

private theorem crossHistCausalCone_round_trip :
    forall x : CrossHistCausalConeUp,
      crossHistCausalConeFromEventFlow (crossHistCausalConeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source target slotWindow affectedRoute maxRate observerSymmetry refusalRow
      hsameTransport contReplay packageProvenance localName =>
      change
        some
          (CrossHistCausalConeUp.mk
            (crossHistCausalConeDecodeBHist (crossHistCausalConeEncodeBHist source))
            (crossHistCausalConeDecodeBHist (crossHistCausalConeEncodeBHist target))
            (crossHistCausalConeDecodeBHist (crossHistCausalConeEncodeBHist slotWindow))
            (crossHistCausalConeDecodeBHist (crossHistCausalConeEncodeBHist affectedRoute))
            (crossHistCausalConeDecodeBHist (crossHistCausalConeEncodeBHist maxRate))
            (crossHistCausalConeDecodeBHist
              (crossHistCausalConeEncodeBHist observerSymmetry))
            (crossHistCausalConeDecodeBHist (crossHistCausalConeEncodeBHist refusalRow))
            (crossHistCausalConeDecodeBHist
              (crossHistCausalConeEncodeBHist hsameTransport))
            (crossHistCausalConeDecodeBHist (crossHistCausalConeEncodeBHist contReplay))
            (crossHistCausalConeDecodeBHist
              (crossHistCausalConeEncodeBHist packageProvenance))
            (crossHistCausalConeDecodeBHist (crossHistCausalConeEncodeBHist localName))) =
          some
            (CrossHistCausalConeUp.mk source target slotWindow affectedRoute maxRate
              observerSymmetry refusalRow hsameTransport contReplay packageProvenance
              localName)
      rw [crossHistCausalConeDecode_encode_bhist source,
        crossHistCausalConeDecode_encode_bhist target,
        crossHistCausalConeDecode_encode_bhist slotWindow,
        crossHistCausalConeDecode_encode_bhist affectedRoute,
        crossHistCausalConeDecode_encode_bhist maxRate,
        crossHistCausalConeDecode_encode_bhist observerSymmetry,
        crossHistCausalConeDecode_encode_bhist refusalRow,
        crossHistCausalConeDecode_encode_bhist hsameTransport,
        crossHistCausalConeDecode_encode_bhist contReplay,
        crossHistCausalConeDecode_encode_bhist packageProvenance,
        crossHistCausalConeDecode_encode_bhist localName]

private theorem crossHistCausalConeToEventFlow_injective
    {x y : CrossHistCausalConeUp} :
    crossHistCausalConeToEventFlow x = crossHistCausalConeToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      crossHistCausalConeFromEventFlow (crossHistCausalConeToEventFlow x) =
        crossHistCausalConeFromEventFlow (crossHistCausalConeToEventFlow y) :=
    congrArg crossHistCausalConeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (crossHistCausalCone_round_trip x).symm
      (Eq.trans hread (crossHistCausalCone_round_trip y)))

instance crossHistCausalConeBHistCarrier : BHistCarrier CrossHistCausalConeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := crossHistCausalConeToEventFlow
  fromEventFlow := crossHistCausalConeFromEventFlow

instance crossHistCausalConeChapterTasteGate : ChapterTasteGate CrossHistCausalConeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change crossHistCausalConeFromEventFlow (crossHistCausalConeToEventFlow x) = some x
    exact crossHistCausalCone_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (crossHistCausalConeToEventFlow_injective heq)

def crossHistCausalConeFields : CrossHistCausalConeUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CrossHistCausalConeUp.mk source target slotWindow affectedRoute maxRate
      observerSymmetry refusalRow hsameTransport contReplay packageProvenance localName =>
      [source, target, slotWindow, affectedRoute, maxRate, observerSymmetry, refusalRow,
        hsameTransport, contReplay, packageProvenance, localName]

private theorem crossHistCausalCone_field_faithful_concrete :
    forall x y : CrossHistCausalConeUp,
      crossHistCausalConeFields x = crossHistCausalConeFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk source target slotWindow affectedRoute maxRate observerSymmetry refusalRow
      hsameTransport contReplay packageProvenance localName =>
      cases y with
      | mk source' target' slotWindow' affectedRoute' maxRate' observerSymmetry'
          refusalRow' hsameTransport' contReplay' packageProvenance' localName' =>
          change
            [source, target, slotWindow, affectedRoute, maxRate, observerSymmetry,
                refusalRow, hsameTransport, contReplay, packageProvenance, localName] =
              [source', target', slotWindow', affectedRoute', maxRate',
                observerSymmetry', refusalRow', hsameTransport', contReplay',
                packageProvenance', localName'] at hfields
          injection hfields with hSource hTail0
          injection hTail0 with hTarget hTail1
          injection hTail1 with hSlotWindow hTail2
          injection hTail2 with hAffectedRoute hTail3
          injection hTail3 with hMaxRate hTail4
          injection hTail4 with hObserverSymmetry hTail5
          injection hTail5 with hRefusalRow hTail6
          injection hTail6 with hHsameTransport hTail7
          injection hTail7 with hContReplay hTail8
          injection hTail8 with hPackageProvenance hTail9
          injection hTail9 with hLocalName _hNil
          cases hSource
          cases hTarget
          cases hSlotWindow
          cases hAffectedRoute
          cases hMaxRate
          cases hObserverSymmetry
          cases hRefusalRow
          cases hHsameTransport
          cases hContReplay
          cases hPackageProvenance
          cases hLocalName
          rfl

instance crossHistCausalConeFieldFaithful : FieldFaithful CrossHistCausalConeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := crossHistCausalConeFields
  field_faithful := crossHistCausalCone_field_faithful_concrete

instance crossHistCausalConeNontrivial : Nontrivial CrossHistCausalConeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CrossHistCausalConeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CrossHistCausalConeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CrossHistCausalConeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  crossHistCausalConeChapterTasteGate

theorem CrossHistCausalConeTasteGate_single_carrier_alignment :
    (forall h : BHist, crossHistCausalConeDecodeBHist (crossHistCausalConeEncodeBHist h) = h) ∧
      (forall x : CrossHistCausalConeUp,
        crossHistCausalConeFromEventFlow (crossHistCausalConeToEventFlow x) = some x) ∧
        (forall x y : CrossHistCausalConeUp,
          crossHistCausalConeToEventFlow x = crossHistCausalConeToEventFlow y -> x = y) ∧
          (forall x : CrossHistCausalConeUp, forall w : RawEvent, forall m : BMark,
            List.Mem w (crossHistCausalConeToEventFlow x) -> List.Mem m w ->
              m = BMark.b0 ∨ m = BMark.b1) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact crossHistCausalConeDecode_encode_bhist
  · constructor
    · exact crossHistCausalCone_round_trip
    · constructor
      · intro x y heq
        exact crossHistCausalConeToEventFlow_injective heq
      · intro _x _w m _hw _hm
        cases m with
        | b0 =>
            exact Or.inl rfl
        | b1 =>
            exact Or.inr rfl

end BEDC.Derived.CrossHistCausalConeUp
