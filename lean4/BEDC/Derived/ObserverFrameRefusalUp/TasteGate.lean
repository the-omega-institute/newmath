import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ObserverFrameRefusalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ObserverFrameRefusalUp : Type where
  | mk :
      (observer coordinate locality rate refusal transport routes provenance name : BHist) →
      ObserverFrameRefusalUp
  deriving DecidableEq

def observerFrameRefusalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: observerFrameRefusalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: observerFrameRefusalEncodeBHist h

def observerFrameRefusalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (observerFrameRefusalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (observerFrameRefusalDecodeBHist tail)

private theorem observerFrameRefusalDecodeEncodeBHist :
    ∀ h : BHist, observerFrameRefusalDecodeBHist (observerFrameRefusalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def observerFrameRefusalFields : ObserverFrameRefusalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ObserverFrameRefusalUp.mk observer coordinate locality rate refusal transport routes
      provenance name =>
      [observer, coordinate, locality, rate, refusal, transport, routes, provenance, name]

def observerFrameRefusalToEventFlow : ObserverFrameRefusalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ObserverFrameRefusalUp.mk observer coordinate locality rate refusal transport routes
      provenance name =>
      [observerFrameRefusalEncodeBHist observer,
        observerFrameRefusalEncodeBHist coordinate,
        observerFrameRefusalEncodeBHist locality,
        observerFrameRefusalEncodeBHist rate,
        observerFrameRefusalEncodeBHist refusal,
        observerFrameRefusalEncodeBHist transport,
        observerFrameRefusalEncodeBHist routes,
        observerFrameRefusalEncodeBHist provenance,
        observerFrameRefusalEncodeBHist name]

def observerFrameRefusalFromEventFlow : EventFlow → Option ObserverFrameRefusalUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | observer :: rest0 =>
      match rest0 with
      | [] => none
      | coordinate :: rest1 =>
          match rest1 with
          | [] => none
          | locality :: rest2 =>
              match rest2 with
              | [] => none
              | rate :: rest3 =>
                  match rest3 with
                  | [] => none
                  | refusal :: rest4 =>
                      match rest4 with
                      | [] => none
                      | transport :: rest5 =>
                          match rest5 with
                          | [] => none
                          | routes :: rest6 =>
                              match rest6 with
                              | [] => none
                              | provenance :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | name :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (ObserverFrameRefusalUp.mk
                                              (observerFrameRefusalDecodeBHist observer)
                                              (observerFrameRefusalDecodeBHist coordinate)
                                              (observerFrameRefusalDecodeBHist locality)
                                              (observerFrameRefusalDecodeBHist rate)
                                              (observerFrameRefusalDecodeBHist refusal)
                                              (observerFrameRefusalDecodeBHist transport)
                                              (observerFrameRefusalDecodeBHist routes)
                                              (observerFrameRefusalDecodeBHist provenance)
                                              (observerFrameRefusalDecodeBHist name))
                                      | _ :: _ => none

private theorem observerFrameRefusal_round_trip :
    ∀ x : ObserverFrameRefusalUp,
      observerFrameRefusalFromEventFlow (observerFrameRefusalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk observer coordinate locality rate refusal transport routes provenance name =>
      change
        some
          (ObserverFrameRefusalUp.mk
            (observerFrameRefusalDecodeBHist (observerFrameRefusalEncodeBHist observer))
            (observerFrameRefusalDecodeBHist (observerFrameRefusalEncodeBHist coordinate))
            (observerFrameRefusalDecodeBHist (observerFrameRefusalEncodeBHist locality))
            (observerFrameRefusalDecodeBHist (observerFrameRefusalEncodeBHist rate))
            (observerFrameRefusalDecodeBHist (observerFrameRefusalEncodeBHist refusal))
            (observerFrameRefusalDecodeBHist (observerFrameRefusalEncodeBHist transport))
            (observerFrameRefusalDecodeBHist (observerFrameRefusalEncodeBHist routes))
            (observerFrameRefusalDecodeBHist (observerFrameRefusalEncodeBHist provenance))
            (observerFrameRefusalDecodeBHist (observerFrameRefusalEncodeBHist name))) =
          some
            (ObserverFrameRefusalUp.mk observer coordinate locality rate refusal transport
              routes provenance name)
      rw [observerFrameRefusalDecodeEncodeBHist observer,
        observerFrameRefusalDecodeEncodeBHist coordinate,
        observerFrameRefusalDecodeEncodeBHist locality,
        observerFrameRefusalDecodeEncodeBHist rate,
        observerFrameRefusalDecodeEncodeBHist refusal,
        observerFrameRefusalDecodeEncodeBHist transport,
        observerFrameRefusalDecodeEncodeBHist routes,
        observerFrameRefusalDecodeEncodeBHist provenance,
        observerFrameRefusalDecodeEncodeBHist name]

private theorem observerFrameRefusalToEventFlow_injective {x y : ObserverFrameRefusalUp} :
    observerFrameRefusalToEventFlow x = observerFrameRefusalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      observerFrameRefusalFromEventFlow (observerFrameRefusalToEventFlow x) =
        observerFrameRefusalFromEventFlow (observerFrameRefusalToEventFlow y) :=
    congrArg observerFrameRefusalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (observerFrameRefusal_round_trip x).symm
      (Eq.trans hread (observerFrameRefusal_round_trip y)))

private theorem observerFrameRefusalFieldFaithful :
    ∀ x y : ObserverFrameRefusalUp,
      observerFrameRefusalFields x = observerFrameRefusalFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk observer1 coordinate1 locality1 rate1 refusal1 transport1 routes1 provenance1 name1 =>
      cases y with
      | mk observer2 coordinate2 locality2 rate2 refusal2 transport2 routes2 provenance2 name2 =>
          cases h
          rfl

instance observerFrameRefusalBHistCarrier : BHistCarrier ObserverFrameRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := observerFrameRefusalToEventFlow
  fromEventFlow := observerFrameRefusalFromEventFlow

instance observerFrameRefusalChapterTasteGate : ChapterTasteGate ObserverFrameRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change observerFrameRefusalFromEventFlow (observerFrameRefusalToEventFlow x) = some x
    exact observerFrameRefusal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (observerFrameRefusalToEventFlow_injective heq)

instance observerFrameRefusalFieldFaithfulInstance : FieldFaithful ObserverFrameRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := observerFrameRefusalFields
  field_faithful := observerFrameRefusalFieldFaithful

instance observerFrameRefusalNontrivial : Nontrivial ObserverFrameRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ObserverFrameRefusalUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ObserverFrameRefusalUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem ObserverFrameRefusalTasteGate_single_carrier_alignment :
    (∀ h : BHist, observerFrameRefusalDecodeBHist (observerFrameRefusalEncodeBHist h) = h) ∧
      (∀ x : ObserverFrameRefusalUp,
        observerFrameRefusalFromEventFlow (observerFrameRefusalToEventFlow x) = some x) ∧
      (∀ x y : ObserverFrameRefusalUp,
        observerFrameRefusalToEventFlow x = observerFrameRefusalToEventFlow y → x = y) ∧
      observerFrameRefusalEncodeBHist BHist.Empty = ([] : List BMark) ∧
      (∀ x y : ObserverFrameRefusalUp, observerFrameRefusalFields x =
        observerFrameRefusalFields y → x = y) ∧
      (∃ x y : ObserverFrameRefusalUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact observerFrameRefusalDecodeEncodeBHist
  · constructor
    · exact observerFrameRefusal_round_trip
    · constructor
      · intro x y heq
        exact observerFrameRefusalToEventFlow_injective heq
      · constructor
        · rfl
        · constructor
          · exact observerFrameRefusalFieldFaithful
          · exact
              ⟨ObserverFrameRefusalUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
                ObserverFrameRefusalUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
                by
                  intro h
                  cases h⟩

end BEDC.Derived.ObserverFrameRefusalUp
