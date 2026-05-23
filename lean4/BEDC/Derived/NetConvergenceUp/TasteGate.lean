import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NetConvergenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NetConvergenceUp : Type where
  | mk :
      (directed tail entourage optionalSource filter schedule readback realSeal transport replay
        provenance localName : BHist) →
        NetConvergenceUp
  deriving DecidableEq

def netConvergenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: netConvergenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: netConvergenceEncodeBHist h

def netConvergenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (netConvergenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (netConvergenceDecodeBHist tail)

private theorem netConvergenceDecodeEncodeBHist :
    ∀ h : BHist, netConvergenceDecodeBHist (netConvergenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def netConvergenceFields : NetConvergenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NetConvergenceUp.mk directed tail entourage optionalSource filter schedule readback realSeal
      transport replay provenance localName =>
      [directed, tail, entourage, optionalSource, filter, schedule, readback, realSeal, transport,
        replay, provenance, localName]

def netConvergenceToEventFlow : NetConvergenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (netConvergenceFields x).map netConvergenceEncodeBHist

def netConvergenceFromEventFlow : EventFlow → Option NetConvergenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | directed :: rest0 =>
      match rest0 with
      | [] => none
      | tail :: rest1 =>
          match rest1 with
          | [] => none
          | entourage :: rest2 =>
              match rest2 with
              | [] => none
              | optionalSource :: rest3 =>
                  match rest3 with
                  | [] => none
                  | filter :: rest4 =>
                      match rest4 with
                      | [] => none
                      | schedule :: rest5 =>
                          match rest5 with
                          | [] => none
                          | readback :: rest6 =>
                              match rest6 with
                              | [] => none
                              | realSeal :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | transport :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | replay :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | provenance :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | localName :: rest11 =>
                                                  match rest11 with
                                                  | [] =>
                                                      some
                                                        (NetConvergenceUp.mk
                                                          (netConvergenceDecodeBHist directed)
                                                          (netConvergenceDecodeBHist tail)
                                                          (netConvergenceDecodeBHist entourage)
                                                          (netConvergenceDecodeBHist optionalSource)
                                                          (netConvergenceDecodeBHist filter)
                                                          (netConvergenceDecodeBHist schedule)
                                                          (netConvergenceDecodeBHist readback)
                                                          (netConvergenceDecodeBHist realSeal)
                                                          (netConvergenceDecodeBHist transport)
                                                          (netConvergenceDecodeBHist replay)
                                                          (netConvergenceDecodeBHist provenance)
                                                          (netConvergenceDecodeBHist localName))
                                                  | _ :: _ => none

private theorem netConvergence_round_trip :
    ∀ x : NetConvergenceUp,
      netConvergenceFromEventFlow (netConvergenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk directed tail entourage optionalSource filter schedule readback realSeal transport replay
      provenance localName =>
      change
        some
          (NetConvergenceUp.mk
            (netConvergenceDecodeBHist (netConvergenceEncodeBHist directed))
            (netConvergenceDecodeBHist (netConvergenceEncodeBHist tail))
            (netConvergenceDecodeBHist (netConvergenceEncodeBHist entourage))
            (netConvergenceDecodeBHist (netConvergenceEncodeBHist optionalSource))
            (netConvergenceDecodeBHist (netConvergenceEncodeBHist filter))
            (netConvergenceDecodeBHist (netConvergenceEncodeBHist schedule))
            (netConvergenceDecodeBHist (netConvergenceEncodeBHist readback))
            (netConvergenceDecodeBHist (netConvergenceEncodeBHist realSeal))
            (netConvergenceDecodeBHist (netConvergenceEncodeBHist transport))
            (netConvergenceDecodeBHist (netConvergenceEncodeBHist replay))
            (netConvergenceDecodeBHist (netConvergenceEncodeBHist provenance))
            (netConvergenceDecodeBHist (netConvergenceEncodeBHist localName))) =
          some
            (NetConvergenceUp.mk directed tail entourage optionalSource filter schedule readback
              realSeal transport replay provenance localName)
      rw [netConvergenceDecodeEncodeBHist directed,
        netConvergenceDecodeEncodeBHist tail,
        netConvergenceDecodeEncodeBHist entourage,
        netConvergenceDecodeEncodeBHist optionalSource,
        netConvergenceDecodeEncodeBHist filter,
        netConvergenceDecodeEncodeBHist schedule,
        netConvergenceDecodeEncodeBHist readback,
        netConvergenceDecodeEncodeBHist realSeal,
        netConvergenceDecodeEncodeBHist transport,
        netConvergenceDecodeEncodeBHist replay,
        netConvergenceDecodeEncodeBHist provenance,
        netConvergenceDecodeEncodeBHist localName]

private theorem netConvergenceToEventFlow_injective {x y : NetConvergenceUp} :
    netConvergenceToEventFlow x = netConvergenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      netConvergenceFromEventFlow (netConvergenceToEventFlow x) =
        netConvergenceFromEventFlow (netConvergenceToEventFlow y) :=
    congrArg netConvergenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (netConvergence_round_trip x).symm
      (Eq.trans hread (netConvergence_round_trip y)))

instance netConvergenceBHistCarrier : BHistCarrier NetConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := netConvergenceToEventFlow
  fromEventFlow := netConvergenceFromEventFlow

instance netConvergenceChapterTasteGate : ChapterTasteGate NetConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change netConvergenceFromEventFlow (netConvergenceToEventFlow x) = some x
    exact netConvergence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (netConvergenceToEventFlow_injective heq)

def taste_gate : ChapterTasteGate NetConvergenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  netConvergenceChapterTasteGate

theorem NetConvergenceTasteGate_single_carrier_alignment :
    (∀ h : BHist, netConvergenceDecodeBHist (netConvergenceEncodeBHist h) = h) ∧
      (∀ x : NetConvergenceUp,
        netConvergenceFromEventFlow (netConvergenceToEventFlow x) = some x) ∧
        (∀ x y : NetConvergenceUp,
          netConvergenceToEventFlow x = netConvergenceToEventFlow y → x = y) ∧
          netConvergenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact netConvergenceDecodeEncodeBHist
  · constructor
    · exact netConvergence_round_trip
    · constructor
      · intro x y heq
        exact netConvergenceToEventFlow_injective heq
      · rfl

end BEDC.Derived.NetConvergenceUp
