import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CrossHistCausalRateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CrossHistCausalRateUp : Type where
  | mk :
      (observerA observerB causalRoutes maximumRate observerSymmetry noGlobalFrame transports
        continuation provenance localName : BHist) →
        CrossHistCausalRateUp
  deriving DecidableEq

def crossHistCausalRateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: crossHistCausalRateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: crossHistCausalRateEncodeBHist h

def crossHistCausalRateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (crossHistCausalRateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (crossHistCausalRateDecodeBHist tail)

private theorem crossHistCausalRateDecode_encode_bhist :
    ∀ h : BHist, crossHistCausalRateDecodeBHist (crossHistCausalRateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def crossHistCausalRateToEventFlow : CrossHistCausalRateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CrossHistCausalRateUp.mk observerA observerB causalRoutes maximumRate observerSymmetry
      noGlobalFrame transports continuation provenance localName =>
      [[BMark.b0],
        crossHistCausalRateEncodeBHist observerA,
        [BMark.b1, BMark.b0],
        crossHistCausalRateEncodeBHist observerB,
        [BMark.b1, BMark.b1, BMark.b0],
        crossHistCausalRateEncodeBHist causalRoutes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        crossHistCausalRateEncodeBHist maximumRate,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        crossHistCausalRateEncodeBHist observerSymmetry,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        crossHistCausalRateEncodeBHist noGlobalFrame,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        crossHistCausalRateEncodeBHist transports,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        crossHistCausalRateEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        crossHistCausalRateEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        crossHistCausalRateEncodeBHist localName]

def crossHistCausalRateFromEventFlow : EventFlow → Option CrossHistCausalRateUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | observerA :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | observerB :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | causalRoutes :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | maximumRate :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | observerSymmetry :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | noGlobalFrame :: rest11 =>
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
                                                              | continuation :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | provenance ::
                                                                          rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match
                                                                                rest18
                                                                              with
                                                                              | [] => none
                                                                              | localName ::
                                                                                  rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (CrossHistCausalRateUp.mk
                                                                                          (crossHistCausalRateDecodeBHist
                                                                                            observerA)
                                                                                          (crossHistCausalRateDecodeBHist
                                                                                            observerB)
                                                                                          (crossHistCausalRateDecodeBHist
                                                                                            causalRoutes)
                                                                                          (crossHistCausalRateDecodeBHist
                                                                                            maximumRate)
                                                                                          (crossHistCausalRateDecodeBHist
                                                                                            observerSymmetry)
                                                                                          (crossHistCausalRateDecodeBHist
                                                                                            noGlobalFrame)
                                                                                          (crossHistCausalRateDecodeBHist
                                                                                            transports)
                                                                                          (crossHistCausalRateDecodeBHist
                                                                                            continuation)
                                                                                          (crossHistCausalRateDecodeBHist
                                                                                            provenance)
                                                                                          (crossHistCausalRateDecodeBHist
                                                                                            localName))
                                                                                  | _ :: _ =>
                                                                                      none

private theorem crossHistCausalRate_round_trip :
    ∀ x : CrossHistCausalRateUp,
      crossHistCausalRateFromEventFlow (crossHistCausalRateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk observerA observerB causalRoutes maximumRate observerSymmetry noGlobalFrame transports
      continuation provenance localName =>
      change
        some (CrossHistCausalRateUp.mk
          (crossHistCausalRateDecodeBHist (crossHistCausalRateEncodeBHist observerA))
          (crossHistCausalRateDecodeBHist (crossHistCausalRateEncodeBHist observerB))
          (crossHistCausalRateDecodeBHist (crossHistCausalRateEncodeBHist causalRoutes))
          (crossHistCausalRateDecodeBHist (crossHistCausalRateEncodeBHist maximumRate))
          (crossHistCausalRateDecodeBHist (crossHistCausalRateEncodeBHist observerSymmetry))
          (crossHistCausalRateDecodeBHist (crossHistCausalRateEncodeBHist noGlobalFrame))
          (crossHistCausalRateDecodeBHist (crossHistCausalRateEncodeBHist transports))
          (crossHistCausalRateDecodeBHist (crossHistCausalRateEncodeBHist continuation))
          (crossHistCausalRateDecodeBHist (crossHistCausalRateEncodeBHist provenance))
          (crossHistCausalRateDecodeBHist (crossHistCausalRateEncodeBHist localName))) =
          some (CrossHistCausalRateUp.mk observerA observerB causalRoutes maximumRate
            observerSymmetry noGlobalFrame transports continuation provenance localName)
      rw [crossHistCausalRateDecode_encode_bhist observerA,
        crossHistCausalRateDecode_encode_bhist observerB,
        crossHistCausalRateDecode_encode_bhist causalRoutes,
        crossHistCausalRateDecode_encode_bhist maximumRate,
        crossHistCausalRateDecode_encode_bhist observerSymmetry,
        crossHistCausalRateDecode_encode_bhist noGlobalFrame,
        crossHistCausalRateDecode_encode_bhist transports,
        crossHistCausalRateDecode_encode_bhist continuation,
        crossHistCausalRateDecode_encode_bhist provenance,
        crossHistCausalRateDecode_encode_bhist localName]

private theorem crossHistCausalRateToEventFlow_injective {x y : CrossHistCausalRateUp} :
    crossHistCausalRateToEventFlow x = crossHistCausalRateToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      crossHistCausalRateFromEventFlow (crossHistCausalRateToEventFlow x) =
        crossHistCausalRateFromEventFlow (crossHistCausalRateToEventFlow y) :=
    congrArg crossHistCausalRateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (crossHistCausalRate_round_trip x).symm
      (Eq.trans hread (crossHistCausalRate_round_trip y)))

instance crossHistCausalRateBHistCarrier : BHistCarrier CrossHistCausalRateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := crossHistCausalRateToEventFlow
  fromEventFlow := crossHistCausalRateFromEventFlow

instance crossHistCausalRateChapterTasteGate : ChapterTasteGate CrossHistCausalRateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change crossHistCausalRateFromEventFlow (crossHistCausalRateToEventFlow x) = some x
    exact crossHistCausalRate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (crossHistCausalRateToEventFlow_injective heq)

instance crossHistCausalRateNontrivial : Nontrivial CrossHistCausalRateUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CrossHistCausalRateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CrossHistCausalRateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

instance crossHistCausalRateFieldFaithful : FieldFaithful CrossHistCausalRateUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields
    | CrossHistCausalRateUp.mk observerA observerB causalRoutes maximumRate observerSymmetry
        noGlobalFrame transports continuation provenance localName =>
        [observerA, observerB, causalRoutes, maximumRate, observerSymmetry, noGlobalFrame,
          transports, continuation, provenance, localName]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk observerA observerB causalRoutes maximumRate observerSymmetry noGlobalFrame transports
        continuation provenance localName =>
        cases y with
        | mk observerA' observerB' causalRoutes' maximumRate' observerSymmetry'
            noGlobalFrame' transports' continuation' provenance' localName' =>
            change
              [observerA, observerB, causalRoutes, maximumRate, observerSymmetry, noGlobalFrame,
                  transports, continuation, provenance, localName] =
                [observerA', observerB', causalRoutes', maximumRate', observerSymmetry',
                  noGlobalFrame', transports', continuation', provenance', localName'] at hfields
            injection hfields with hObserverA hTail0
            injection hTail0 with hObserverB hTail1
            injection hTail1 with hCausalRoutes hTail2
            injection hTail2 with hMaximumRate hTail3
            injection hTail3 with hObserverSymmetry hTail4
            injection hTail4 with hNoGlobalFrame hTail5
            injection hTail5 with hTransports hTail6
            injection hTail6 with hContinuation hTail7
            injection hTail7 with hProvenance hTail8
            injection hTail8 with hLocalName _hNil
            cases hObserverA
            cases hObserverB
            cases hCausalRoutes
            cases hMaximumRate
            cases hObserverSymmetry
            cases hNoGlobalFrame
            cases hTransports
            cases hContinuation
            cases hProvenance
            cases hLocalName
            rfl

def taste_gate : ChapterTasteGate CrossHistCausalRateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  crossHistCausalRateChapterTasteGate

theorem CrossHistCausalRateTasteGate_single_carrier_alignment :
    (∀ h : BHist, crossHistCausalRateDecodeBHist (crossHistCausalRateEncodeBHist h) = h) ∧
      (∀ x : CrossHistCausalRateUp,
        crossHistCausalRateFromEventFlow (crossHistCausalRateToEventFlow x) = some x) ∧
        (∀ x y : CrossHistCausalRateUp,
          crossHistCausalRateToEventFlow x = crossHistCausalRateToEventFlow y → x = y) ∧
          crossHistCausalRateEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact crossHistCausalRateDecode_encode_bhist
  · constructor
    · exact crossHistCausalRate_round_trip
    · constructor
      · intro x y heq
        exact crossHistCausalRateToEventFlow_injective heq
      · rfl

end BEDC.Derived.CrossHistCausalRateUp
