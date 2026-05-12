import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ContinuationAutomatonUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ContinuationAutomatonUp : Type where
  | mk :
      (states initial accepting transition behaviour transport route provenance name : BHist) →
        ContinuationAutomatonUp
  deriving DecidableEq

def continuationAutomatonEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: continuationAutomatonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: continuationAutomatonEncodeBHist h

def continuationAutomatonDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (continuationAutomatonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (continuationAutomatonDecodeBHist tail)

private theorem continuationAutomatonDecode_encode_bhist :
    ∀ h : BHist, continuationAutomatonDecodeBHist (continuationAutomatonEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem continuationAutomaton_mk_congr
    {states states' initial initial' accepting accepting' transition transition' behaviour
      behaviour' transport transport' route route' provenance provenance' name name' : BHist}
    (hStates : states' = states)
    (hInitial : initial' = initial)
    (hAccepting : accepting' = accepting)
    (hTransition : transition' = transition)
    (hBehaviour : behaviour' = behaviour)
    (hTransport : transport' = transport)
    (hRoute : route' = route)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    ContinuationAutomatonUp.mk states' initial' accepting' transition' behaviour' transport' route'
        provenance' name' =
      ContinuationAutomatonUp.mk states initial accepting transition behaviour transport route
        provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hStates
  cases hInitial
  cases hAccepting
  cases hTransition
  cases hBehaviour
  cases hTransport
  cases hRoute
  cases hProvenance
  cases hName
  rfl

def continuationAutomatonToEventFlow : ContinuationAutomatonUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ContinuationAutomatonUp.mk states initial accepting transition behaviour transport route
      provenance name =>
      [[BMark.b0],
        continuationAutomatonEncodeBHist states,
        [BMark.b1, BMark.b0],
        continuationAutomatonEncodeBHist initial,
        [BMark.b1, BMark.b1, BMark.b0],
        continuationAutomatonEncodeBHist accepting,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        continuationAutomatonEncodeBHist transition,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        continuationAutomatonEncodeBHist behaviour,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        continuationAutomatonEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        continuationAutomatonEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        continuationAutomatonEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        continuationAutomatonEncodeBHist name]

def continuationAutomatonFromEventFlow : EventFlow → Option ContinuationAutomatonUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | states :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | initial :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | accepting :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | transition :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | behaviour :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transport :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | route :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | name :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (ContinuationAutomatonUp.mk
                                                                                  (continuationAutomatonDecodeBHist
                                                                                    states)
                                                                                  (continuationAutomatonDecodeBHist
                                                                                    initial)
                                                                                  (continuationAutomatonDecodeBHist
                                                                                    accepting)
                                                                                  (continuationAutomatonDecodeBHist
                                                                                    transition)
                                                                                  (continuationAutomatonDecodeBHist
                                                                                    behaviour)
                                                                                  (continuationAutomatonDecodeBHist
                                                                                    transport)
                                                                                  (continuationAutomatonDecodeBHist
                                                                                    route)
                                                                                  (continuationAutomatonDecodeBHist
                                                                                    provenance)
                                                                                  (continuationAutomatonDecodeBHist
                                                                                    name))
                                                                          | _ :: _ => none

private theorem continuationAutomaton_round_trip :
    ∀ x : ContinuationAutomatonUp,
      continuationAutomatonFromEventFlow (continuationAutomatonToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk states initial accepting transition behaviour transport route provenance name =>
      change
        some
          (ContinuationAutomatonUp.mk
            (continuationAutomatonDecodeBHist (continuationAutomatonEncodeBHist states))
            (continuationAutomatonDecodeBHist (continuationAutomatonEncodeBHist initial))
            (continuationAutomatonDecodeBHist (continuationAutomatonEncodeBHist accepting))
            (continuationAutomatonDecodeBHist (continuationAutomatonEncodeBHist transition))
            (continuationAutomatonDecodeBHist (continuationAutomatonEncodeBHist behaviour))
            (continuationAutomatonDecodeBHist (continuationAutomatonEncodeBHist transport))
            (continuationAutomatonDecodeBHist (continuationAutomatonEncodeBHist route))
            (continuationAutomatonDecodeBHist (continuationAutomatonEncodeBHist provenance))
            (continuationAutomatonDecodeBHist (continuationAutomatonEncodeBHist name))) =
          some
            (ContinuationAutomatonUp.mk states initial accepting transition behaviour transport
              route provenance name)
      exact
        congrArg some
          (continuationAutomaton_mk_congr
            (continuationAutomatonDecode_encode_bhist states)
            (continuationAutomatonDecode_encode_bhist initial)
            (continuationAutomatonDecode_encode_bhist accepting)
            (continuationAutomatonDecode_encode_bhist transition)
            (continuationAutomatonDecode_encode_bhist behaviour)
            (continuationAutomatonDecode_encode_bhist transport)
            (continuationAutomatonDecode_encode_bhist route)
            (continuationAutomatonDecode_encode_bhist provenance)
            (continuationAutomatonDecode_encode_bhist name))

private theorem continuationAutomatonToEventFlow_injective {x y : ContinuationAutomatonUp} :
    continuationAutomatonToEventFlow x = continuationAutomatonToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      continuationAutomatonFromEventFlow (continuationAutomatonToEventFlow x) =
        continuationAutomatonFromEventFlow (continuationAutomatonToEventFlow y) :=
    congrArg continuationAutomatonFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (continuationAutomaton_round_trip x).symm
      (Eq.trans hread (continuationAutomaton_round_trip y)))

instance continuationAutomatonBHistCarrier : BHistCarrier ContinuationAutomatonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := continuationAutomatonToEventFlow
  fromEventFlow := continuationAutomatonFromEventFlow

instance continuationAutomatonChapterTasteGate : ChapterTasteGate ContinuationAutomatonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change continuationAutomatonFromEventFlow (continuationAutomatonToEventFlow x) = some x
    exact continuationAutomaton_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (continuationAutomatonToEventFlow_injective heq)

def taste_gate : ChapterTasteGate ContinuationAutomatonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  continuationAutomatonChapterTasteGate

theorem ContinuationAutomatonTasteGate_single_carrier_alignment :
    (∀ h : BHist, continuationAutomatonDecodeBHist (continuationAutomatonEncodeBHist h) = h) ∧
      (∀ x : ContinuationAutomatonUp,
        continuationAutomatonFromEventFlow (continuationAutomatonToEventFlow x) = some x) ∧
        (∀ x y : ContinuationAutomatonUp,
          continuationAutomatonToEventFlow x = continuationAutomatonToEventFlow y → x = y) ∧
          continuationAutomatonEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact continuationAutomatonDecode_encode_bhist
  · constructor
    · exact continuationAutomaton_round_trip
    · constructor
      · intro x y heq
        exact continuationAutomatonToEventFlow_injective heq
      · rfl

end BEDC.Derived.ContinuationAutomatonUp
