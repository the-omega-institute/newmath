import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TauberianRemainderUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TauberianRemainderUp : Type where
  | mk :
      (abel cesaro sideCondition dyadicBudget regularReadback realSeal transport replay
        provenance localName : BHist) ->
        TauberianRemainderUp
  deriving DecidableEq

def tauberianRemainderEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: tauberianRemainderEncodeBHist h
  | BHist.e1 h => BMark.b1 :: tauberianRemainderEncodeBHist h

def tauberianRemainderDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (tauberianRemainderDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (tauberianRemainderDecodeBHist tail)

private theorem TauberianRemainderTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, tauberianRemainderDecodeBHist (tauberianRemainderEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def tauberianRemainderFields : TauberianRemainderUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TauberianRemainderUp.mk abel cesaro sideCondition dyadicBudget regularReadback realSeal
      transport replay provenance localName =>
      [abel, cesaro, sideCondition, dyadicBudget, regularReadback, realSeal, transport, replay,
        provenance, localName]

def tauberianRemainderToEventFlow : TauberianRemainderUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (tauberianRemainderFields x).map tauberianRemainderEncodeBHist

def tauberianRemainderFromEventFlow : EventFlow -> Option TauberianRemainderUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | abel :: rest0 =>
      match rest0 with
      | [] => none
      | cesaro :: rest1 =>
          match rest1 with
          | [] => none
          | sideCondition :: rest2 =>
              match rest2 with
              | [] => none
              | dyadicBudget :: rest3 =>
                  match rest3 with
                  | [] => none
                  | regularReadback :: rest4 =>
                      match rest4 with
                      | [] => none
                      | realSeal :: rest5 =>
                          match rest5 with
                          | [] => none
                          | transport :: rest6 =>
                              match rest6 with
                              | [] => none
                              | replay :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | provenance :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | localName :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (TauberianRemainderUp.mk
                                                  (tauberianRemainderDecodeBHist abel)
                                                  (tauberianRemainderDecodeBHist cesaro)
                                                  (tauberianRemainderDecodeBHist sideCondition)
                                                  (tauberianRemainderDecodeBHist dyadicBudget)
                                                  (tauberianRemainderDecodeBHist
                                                    regularReadback)
                                                  (tauberianRemainderDecodeBHist realSeal)
                                                  (tauberianRemainderDecodeBHist transport)
                                                  (tauberianRemainderDecodeBHist replay)
                                                  (tauberianRemainderDecodeBHist provenance)
                                                  (tauberianRemainderDecodeBHist localName))
                                          | _ :: _ => none

private theorem TauberianRemainderTasteGate_single_carrier_alignment_round_trip :
    ∀ x : TauberianRemainderUp,
      tauberianRemainderFromEventFlow (tauberianRemainderToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk abel cesaro sideCondition dyadicBudget regularReadback realSeal transport replay
      provenance localName =>
      change
        some
          (TauberianRemainderUp.mk
            (tauberianRemainderDecodeBHist (tauberianRemainderEncodeBHist abel))
            (tauberianRemainderDecodeBHist (tauberianRemainderEncodeBHist cesaro))
            (tauberianRemainderDecodeBHist (tauberianRemainderEncodeBHist sideCondition))
            (tauberianRemainderDecodeBHist (tauberianRemainderEncodeBHist dyadicBudget))
            (tauberianRemainderDecodeBHist (tauberianRemainderEncodeBHist regularReadback))
            (tauberianRemainderDecodeBHist (tauberianRemainderEncodeBHist realSeal))
            (tauberianRemainderDecodeBHist (tauberianRemainderEncodeBHist transport))
            (tauberianRemainderDecodeBHist (tauberianRemainderEncodeBHist replay))
            (tauberianRemainderDecodeBHist (tauberianRemainderEncodeBHist provenance))
            (tauberianRemainderDecodeBHist (tauberianRemainderEncodeBHist localName))) =
          some
            (TauberianRemainderUp.mk abel cesaro sideCondition dyadicBudget regularReadback
              realSeal transport replay provenance localName)
      rw [TauberianRemainderTasteGate_single_carrier_alignment_decode_encode abel,
        TauberianRemainderTasteGate_single_carrier_alignment_decode_encode cesaro,
        TauberianRemainderTasteGate_single_carrier_alignment_decode_encode sideCondition,
        TauberianRemainderTasteGate_single_carrier_alignment_decode_encode dyadicBudget,
        TauberianRemainderTasteGate_single_carrier_alignment_decode_encode regularReadback,
        TauberianRemainderTasteGate_single_carrier_alignment_decode_encode realSeal,
        TauberianRemainderTasteGate_single_carrier_alignment_decode_encode transport,
        TauberianRemainderTasteGate_single_carrier_alignment_decode_encode replay,
        TauberianRemainderTasteGate_single_carrier_alignment_decode_encode provenance,
        TauberianRemainderTasteGate_single_carrier_alignment_decode_encode localName]

private theorem TauberianRemainderTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : TauberianRemainderUp} :
    tauberianRemainderToEventFlow x = tauberianRemainderToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      tauberianRemainderFromEventFlow (tauberianRemainderToEventFlow x) =
        tauberianRemainderFromEventFlow (tauberianRemainderToEventFlow y) :=
    congrArg tauberianRemainderFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (TauberianRemainderTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (TauberianRemainderTasteGate_single_carrier_alignment_round_trip y)))

instance tauberianRemainderBHistCarrier : BHistCarrier TauberianRemainderUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := tauberianRemainderToEventFlow
  fromEventFlow := tauberianRemainderFromEventFlow

instance tauberianRemainderChapterTasteGate : ChapterTasteGate TauberianRemainderUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change tauberianRemainderFromEventFlow (tauberianRemainderToEventFlow x) = some x
    exact TauberianRemainderTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (TauberianRemainderTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def TauberianRemainderTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate TauberianRemainderUp :=
  -- BEDC touchpoint anchor: BHist BMark
  tauberianRemainderChapterTasteGate

theorem TauberianRemainderTasteGate_single_carrier_alignment :
    (∀ h : BHist, tauberianRemainderDecodeBHist (tauberianRemainderEncodeBHist h) = h) ∧
      (∀ x : TauberianRemainderUp,
        tauberianRemainderFromEventFlow (tauberianRemainderToEventFlow x) = some x) ∧
        (∀ x y : TauberianRemainderUp,
          tauberianRemainderToEventFlow x = tauberianRemainderToEventFlow y -> x = y) ∧
          tauberianRemainderEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact TauberianRemainderTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact TauberianRemainderTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact TauberianRemainderTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · rfl

end BEDC.Derived.TauberianRemainderUp
