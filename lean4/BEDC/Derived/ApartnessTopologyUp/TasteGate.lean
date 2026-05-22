import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ApartnessTopologyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ApartnessTopologyUp : Type where
  | mk :
      (gap openWindow topology metric locatedSet window readback dyadic realSeal generatedRow transport
        replay provenance localName : BHist) →
        ApartnessTopologyUp
  deriving DecidableEq

def apartnessTopologyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: apartnessTopologyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: apartnessTopologyEncodeBHist h

def apartnessTopologyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (apartnessTopologyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (apartnessTopologyDecodeBHist tail)

private theorem apartnessTopologyDecodeEncodeBHist :
    ∀ h : BHist, apartnessTopologyDecodeBHist (apartnessTopologyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def apartnessTopologyFields : ApartnessTopologyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ApartnessTopologyUp.mk gap openWindow topology metric locatedSet window readback dyadic realSeal
      generatedRow transport replay provenance localName =>
      [gap, openWindow, topology, metric, locatedSet, window, readback, dyadic, realSeal, generatedRow,
        transport, replay, provenance, localName]

def apartnessTopologyToEventFlow : ApartnessTopologyUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (apartnessTopologyFields x).map apartnessTopologyEncodeBHist

def apartnessTopologyFromEventFlow : EventFlow → Option ApartnessTopologyUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | gap :: rest0 =>
      match rest0 with
      | [] => none
      | openWindow :: rest1 =>
          match rest1 with
          | [] => none
          | topology :: rest2 =>
              match rest2 with
              | [] => none
              | metric :: rest3 =>
                  match rest3 with
                  | [] => none
                  | locatedSet :: rest4 =>
                      match rest4 with
                      | [] => none
                      | window :: rest5 =>
                          match rest5 with
                          | [] => none
                          | readback :: rest6 =>
                              match rest6 with
                              | [] => none
                              | dyadic :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | realSeal :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | generatedRow :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | transport :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | replay :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | provenance :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | localName :: rest13 =>
                                                          match rest13 with
                                                          | [] =>
                                                              some
                                                                (ApartnessTopologyUp.mk
                                                                  (apartnessTopologyDecodeBHist gap)
                                                                  (apartnessTopologyDecodeBHist
                                                                    openWindow)
                                                                  (apartnessTopologyDecodeBHist topology)
                                                                  (apartnessTopologyDecodeBHist metric)
                                                                  (apartnessTopologyDecodeBHist
                                                                    locatedSet)
                                                                  (apartnessTopologyDecodeBHist window)
                                                                  (apartnessTopologyDecodeBHist readback)
                                                                  (apartnessTopologyDecodeBHist dyadic)
                                                                  (apartnessTopologyDecodeBHist realSeal)
                                                                  (apartnessTopologyDecodeBHist
                                                                    generatedRow)
                                                                  (apartnessTopologyDecodeBHist transport)
                                                                  (apartnessTopologyDecodeBHist replay)
                                                                  (apartnessTopologyDecodeBHist
                                                                    provenance)
                                                                  (apartnessTopologyDecodeBHist localName))
                                                          | _ :: _ => none

private theorem apartnessTopology_round_trip :
    ∀ x : ApartnessTopologyUp,
      apartnessTopologyFromEventFlow (apartnessTopologyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk gap openWindow topology metric locatedSet window readback dyadic realSeal generatedRow transport
      replay provenance localName =>
      change
        some
          (ApartnessTopologyUp.mk
            (apartnessTopologyDecodeBHist (apartnessTopologyEncodeBHist gap))
            (apartnessTopologyDecodeBHist (apartnessTopologyEncodeBHist openWindow))
            (apartnessTopologyDecodeBHist (apartnessTopologyEncodeBHist topology))
            (apartnessTopologyDecodeBHist (apartnessTopologyEncodeBHist metric))
            (apartnessTopologyDecodeBHist (apartnessTopologyEncodeBHist locatedSet))
            (apartnessTopologyDecodeBHist (apartnessTopologyEncodeBHist window))
            (apartnessTopologyDecodeBHist (apartnessTopologyEncodeBHist readback))
            (apartnessTopologyDecodeBHist (apartnessTopologyEncodeBHist dyadic))
            (apartnessTopologyDecodeBHist (apartnessTopologyEncodeBHist realSeal))
            (apartnessTopologyDecodeBHist (apartnessTopologyEncodeBHist generatedRow))
            (apartnessTopologyDecodeBHist (apartnessTopologyEncodeBHist transport))
            (apartnessTopologyDecodeBHist (apartnessTopologyEncodeBHist replay))
            (apartnessTopologyDecodeBHist (apartnessTopologyEncodeBHist provenance))
            (apartnessTopologyDecodeBHist (apartnessTopologyEncodeBHist localName))) =
          some
            (ApartnessTopologyUp.mk gap openWindow topology metric locatedSet window readback
              dyadic realSeal generatedRow transport replay provenance localName)
      rw [apartnessTopologyDecodeEncodeBHist gap,
        apartnessTopologyDecodeEncodeBHist openWindow,
        apartnessTopologyDecodeEncodeBHist topology,
        apartnessTopologyDecodeEncodeBHist metric,
        apartnessTopologyDecodeEncodeBHist locatedSet,
        apartnessTopologyDecodeEncodeBHist window,
        apartnessTopologyDecodeEncodeBHist readback,
        apartnessTopologyDecodeEncodeBHist dyadic,
        apartnessTopologyDecodeEncodeBHist realSeal,
        apartnessTopologyDecodeEncodeBHist generatedRow,
        apartnessTopologyDecodeEncodeBHist transport,
        apartnessTopologyDecodeEncodeBHist replay,
        apartnessTopologyDecodeEncodeBHist provenance,
        apartnessTopologyDecodeEncodeBHist localName]

private theorem apartnessTopologyToEventFlow_injective {x y : ApartnessTopologyUp} :
    apartnessTopologyToEventFlow x = apartnessTopologyToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      apartnessTopologyFromEventFlow (apartnessTopologyToEventFlow x) =
        apartnessTopologyFromEventFlow (apartnessTopologyToEventFlow y) :=
    congrArg apartnessTopologyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (apartnessTopology_round_trip x).symm
      (Eq.trans hread (apartnessTopology_round_trip y)))

instance apartnessTopologyBHistCarrier : BHistCarrier ApartnessTopologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := apartnessTopologyToEventFlow
  fromEventFlow := apartnessTopologyFromEventFlow

instance apartnessTopologyChapterTasteGate : ChapterTasteGate ApartnessTopologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change apartnessTopologyFromEventFlow (apartnessTopologyToEventFlow x) = some x
    exact apartnessTopology_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (apartnessTopologyToEventFlow_injective heq)

def taste_gate : ChapterTasteGate ApartnessTopologyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  apartnessTopologyChapterTasteGate

theorem ApartnessTopologyTasteGate_single_carrier_alignment :
    (∀ h : BHist, apartnessTopologyDecodeBHist (apartnessTopologyEncodeBHist h) = h) ∧
      (∀ x : ApartnessTopologyUp,
        apartnessTopologyFromEventFlow (apartnessTopologyToEventFlow x) = some x) ∧
        (∀ x y : ApartnessTopologyUp,
          apartnessTopologyToEventFlow x = apartnessTopologyToEventFlow y → x = y) ∧
          apartnessTopologyEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact apartnessTopologyDecodeEncodeBHist
  · constructor
    · exact apartnessTopology_round_trip
    · constructor
      · intro x y heq
        exact apartnessTopologyToEventFlow_injective heq
      · rfl

end BEDC.Derived.ApartnessTopologyUp
