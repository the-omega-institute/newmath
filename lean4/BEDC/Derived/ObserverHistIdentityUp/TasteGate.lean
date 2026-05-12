import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ObserverHistIdentityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ObserverHistIdentityUp : Type where
  | mk : (history observation ledger route provenance name : BHist) → ObserverHistIdentityUp
  deriving DecidableEq

def observerHistIdentityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: observerHistIdentityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: observerHistIdentityEncodeBHist h

def observerHistIdentityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (observerHistIdentityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (observerHistIdentityDecodeBHist tail)

private theorem observerHistIdentityDecode_encode_bhist :
    ∀ h : BHist, observerHistIdentityDecodeBHist (observerHistIdentityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem observerHistIdentity_mk_congr
    {history history' observation observation' ledger ledger' route route' provenance provenance'
      name name' : BHist}
    (hHistory : history' = history)
    (hObservation : observation' = observation)
    (hLedger : ledger' = ledger)
    (hRoute : route' = route)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    ObserverHistIdentityUp.mk history' observation' ledger' route' provenance' name' =
      ObserverHistIdentityUp.mk history observation ledger route provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hHistory
  cases hObservation
  cases hLedger
  cases hRoute
  cases hProvenance
  cases hName
  rfl

def observerHistIdentityToEventFlow : ObserverHistIdentityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ObserverHistIdentityUp.mk history observation ledger route provenance name =>
      [[BMark.b0],
        observerHistIdentityEncodeBHist history,
        [BMark.b1, BMark.b0],
        observerHistIdentityEncodeBHist observation,
        [BMark.b1, BMark.b1, BMark.b0],
        observerHistIdentityEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerHistIdentityEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerHistIdentityEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerHistIdentityEncodeBHist name]

def observerHistIdentityFromEventFlow : EventFlow → Option ObserverHistIdentityUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | history :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | observation :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | ledger :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | route :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | provenance :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | name :: rest11 =>
                                                  match rest11 with
                                                  | [] =>
                                                      some
                                                        (ObserverHistIdentityUp.mk
                                                          (observerHistIdentityDecodeBHist history)
                                                          (observerHistIdentityDecodeBHist
                                                            observation)
                                                          (observerHistIdentityDecodeBHist ledger)
                                                          (observerHistIdentityDecodeBHist route)
                                                          (observerHistIdentityDecodeBHist
                                                            provenance)
                                                          (observerHistIdentityDecodeBHist name))
                                                  | _ :: _ => none

private theorem observerHistIdentity_round_trip :
    ∀ x : ObserverHistIdentityUp,
      observerHistIdentityFromEventFlow (observerHistIdentityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk history observation ledger route provenance name =>
      change
        some
          (ObserverHistIdentityUp.mk
            (observerHistIdentityDecodeBHist (observerHistIdentityEncodeBHist history))
            (observerHistIdentityDecodeBHist (observerHistIdentityEncodeBHist observation))
            (observerHistIdentityDecodeBHist (observerHistIdentityEncodeBHist ledger))
            (observerHistIdentityDecodeBHist (observerHistIdentityEncodeBHist route))
            (observerHistIdentityDecodeBHist (observerHistIdentityEncodeBHist provenance))
            (observerHistIdentityDecodeBHist (observerHistIdentityEncodeBHist name))) =
          some (ObserverHistIdentityUp.mk history observation ledger route provenance name)
      exact
        congrArg some
          (observerHistIdentity_mk_congr
            (observerHistIdentityDecode_encode_bhist history)
            (observerHistIdentityDecode_encode_bhist observation)
            (observerHistIdentityDecode_encode_bhist ledger)
            (observerHistIdentityDecode_encode_bhist route)
            (observerHistIdentityDecode_encode_bhist provenance)
            (observerHistIdentityDecode_encode_bhist name))

private theorem observerHistIdentityToEventFlow_injective {x y : ObserverHistIdentityUp} :
    observerHistIdentityToEventFlow x = observerHistIdentityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      observerHistIdentityFromEventFlow (observerHistIdentityToEventFlow x) =
        observerHistIdentityFromEventFlow (observerHistIdentityToEventFlow y) :=
    congrArg observerHistIdentityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (observerHistIdentity_round_trip x).symm
      (Eq.trans hread (observerHistIdentity_round_trip y)))

instance observerHistIdentityBHistCarrier : BHistCarrier ObserverHistIdentityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := observerHistIdentityToEventFlow
  fromEventFlow := observerHistIdentityFromEventFlow

instance observerHistIdentityChapterTasteGate : ChapterTasteGate ObserverHistIdentityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change observerHistIdentityFromEventFlow (observerHistIdentityToEventFlow x) = some x
    exact observerHistIdentity_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (observerHistIdentityToEventFlow_injective heq)

def taste_gate : ChapterTasteGate ObserverHistIdentityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  observerHistIdentityChapterTasteGate

theorem ObserverHistIdentityTasteGate_single_carrier_alignment :
    (∀ h : BHist, observerHistIdentityDecodeBHist (observerHistIdentityEncodeBHist h) = h) ∧
      (∀ x : ObserverHistIdentityUp,
        observerHistIdentityFromEventFlow (observerHistIdentityToEventFlow x) = some x) ∧
        (∀ x y : ObserverHistIdentityUp,
          observerHistIdentityToEventFlow x = observerHistIdentityToEventFlow y → x = y) ∧
          observerHistIdentityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact observerHistIdentityDecode_encode_bhist
  · constructor
    · exact observerHistIdentity_round_trip
    · constructor
      · intro x y heq
        exact observerHistIdentityToEventFlow_injective heq
      · rfl

end BEDC.Derived.ObserverHistIdentityUp
