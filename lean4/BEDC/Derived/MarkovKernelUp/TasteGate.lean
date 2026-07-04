import BEDC.Derived.MarkovKernelUp
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MarkovKernelUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def markovKernelEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: markovKernelEncodeBHist h
  | BHist.e1 h => BMark.b1 :: markovKernelEncodeBHist h

def markovKernelDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (markovKernelDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (markovKernelDecodeBHist tail)

theorem MarkovKernelTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, markovKernelDecodeBHist (markovKernelEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def markovKernelToEventFlow : MarkovKernelUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (markovKernelFields x).map markovKernelEncodeBHist

def markovKernelFromEventFlow : EventFlow → Option MarkovKernelUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | S :: rest0 =>
      match rest0 with
      | [] => none
      | T :: rest1 =>
          match rest1 with
          | [] => none
          | AT :: rest2 =>
              match rest2 with
              | [] => none
              | k :: rest3 =>
                  match rest3 with
                  | [] => none
                  | N :: rest4 =>
                      match rest4 with
                      | [] => none
                      | E :: rest5 =>
                          match rest5 with
                          | [] => none
                          | H :: rest6 =>
                              match rest6 with
                              | [] => none
                              | _C :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | P :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | L :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (MarkovKernelUp.mk
                                                  (markovKernelDecodeBHist S)
                                                  (markovKernelDecodeBHist T)
                                                  (markovKernelDecodeBHist AT)
                                                  (markovKernelDecodeBHist k)
                                                  (markovKernelDecodeBHist N)
                                                  (markovKernelDecodeBHist E)
                                                  (markovKernelDecodeBHist H)
                                                  (markovKernelDecodeBHist P)
                                                  (markovKernelDecodeBHist L))
                                          | _ :: _ => none

theorem MarkovKernelTasteGate_single_carrier_alignment_round_trip :
    ∀ x : MarkovKernelUp,
      markovKernelFromEventFlow (markovKernelToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S T AT k N E H P L =>
      change
        some
          (MarkovKernelUp.mk
            (markovKernelDecodeBHist (markovKernelEncodeBHist S))
            (markovKernelDecodeBHist (markovKernelEncodeBHist T))
            (markovKernelDecodeBHist (markovKernelEncodeBHist AT))
            (markovKernelDecodeBHist (markovKernelEncodeBHist k))
            (markovKernelDecodeBHist (markovKernelEncodeBHist N))
            (markovKernelDecodeBHist (markovKernelEncodeBHist E))
            (markovKernelDecodeBHist (markovKernelEncodeBHist H))
            (markovKernelDecodeBHist (markovKernelEncodeBHist P))
            (markovKernelDecodeBHist (markovKernelEncodeBHist L))) =
          some (MarkovKernelUp.mk S T AT k N E H P L)
      rw [MarkovKernelTasteGate_single_carrier_alignment_decode_encode S,
        MarkovKernelTasteGate_single_carrier_alignment_decode_encode T,
        MarkovKernelTasteGate_single_carrier_alignment_decode_encode AT,
        MarkovKernelTasteGate_single_carrier_alignment_decode_encode k,
        MarkovKernelTasteGate_single_carrier_alignment_decode_encode N,
        MarkovKernelTasteGate_single_carrier_alignment_decode_encode E,
        MarkovKernelTasteGate_single_carrier_alignment_decode_encode H,
        MarkovKernelTasteGate_single_carrier_alignment_decode_encode P,
        MarkovKernelTasteGate_single_carrier_alignment_decode_encode L]

theorem MarkovKernelTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MarkovKernelUp} :
    markovKernelToEventFlow x = markovKernelToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      markovKernelFromEventFlow (markovKernelToEventFlow x) =
        markovKernelFromEventFlow (markovKernelToEventFlow y) :=
    congrArg markovKernelFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (MarkovKernelTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (MarkovKernelTasteGate_single_carrier_alignment_round_trip y)))

instance markovKernelBHistCarrier : BHistCarrier MarkovKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := markovKernelToEventFlow
  fromEventFlow := markovKernelFromEventFlow

instance markovKernelChapterTasteGate : ChapterTasteGate MarkovKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x => MarkovKernelTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MarkovKernelTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate MarkovKernelUp :=
  -- BEDC touchpoint anchor: BHist BMark
  markovKernelChapterTasteGate

theorem MarkovKernelTasteGate_single_carrier_alignment :
    (∀ h : BHist, markovKernelDecodeBHist (markovKernelEncodeBHist h) = h) ∧
      (∀ x : MarkovKernelUp, markovKernelFromEventFlow (markovKernelToEventFlow x) = some x) ∧
        (∀ x y : MarkovKernelUp,
          markovKernelToEventFlow x = markovKernelToEventFlow y → x = y) ∧
          markovKernelEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact MarkovKernelTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact MarkovKernelTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact MarkovKernelTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · rfl

end BEDC.Derived.MarkovKernelUp
