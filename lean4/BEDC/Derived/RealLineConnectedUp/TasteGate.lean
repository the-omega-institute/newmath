import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealLineConnectedUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealLineConnectedUp : Type where
  | mk
      (realSourceRow intervalChainRow intermediateRow continuousMapRow dyadicRow windowRow
        readbackRow terminalSealRow transportRow replayRow provenanceRow localNameRow : BHist) :
      RealLineConnectedUp

def realLineConnectedEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realLineConnectedEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realLineConnectedEncodeBHist h

def realLineConnectedDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realLineConnectedDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realLineConnectedDecodeBHist tail)

private theorem realLineConnectedDecode_encode_bhist :
    ∀ h : BHist, realLineConnectedDecodeBHist (realLineConnectedEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realLineConnectedFields : RealLineConnectedUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealLineConnectedUp.mk realSourceRow intervalChainRow intermediateRow continuousMapRow
      dyadicRow windowRow readbackRow terminalSealRow transportRow replayRow provenanceRow
      localNameRow =>
      [realSourceRow, intervalChainRow, intermediateRow, continuousMapRow, dyadicRow, windowRow,
        readbackRow, terminalSealRow, transportRow, replayRow, provenanceRow, localNameRow]

def realLineConnectedToEventFlow : RealLineConnectedUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realLineConnectedFields x).map realLineConnectedEncodeBHist

def realLineConnectedFromEventFlow : EventFlow → Option RealLineConnectedUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | R :: rest0 =>
      match rest0 with
      | [] => none
      | J :: rest1 =>
        match rest1 with
        | [] => none
        | V :: rest2 =>
          match rest2 with
          | [] => none
          | F :: rest3 =>
            match rest3 with
            | [] => none
            | D :: rest4 =>
              match rest4 with
              | [] => none
              | W :: rest5 =>
                match rest5 with
                | [] => none
                | Q :: rest6 =>
                  match rest6 with
                  | [] => none
                  | E :: rest7 =>
                    match rest7 with
                    | [] => none
                    | H :: rest8 =>
                      match rest8 with
                      | [] => none
                      | C :: rest9 =>
                        match rest9 with
                        | [] => none
                        | P :: rest10 =>
                          match rest10 with
                          | [] => none
                          | N :: rest11 =>
                            match rest11 with
                            | [] =>
                              some
                                (RealLineConnectedUp.mk
                                  (realLineConnectedDecodeBHist R)
                                  (realLineConnectedDecodeBHist J)
                                  (realLineConnectedDecodeBHist V)
                                  (realLineConnectedDecodeBHist F)
                                  (realLineConnectedDecodeBHist D)
                                  (realLineConnectedDecodeBHist W)
                                  (realLineConnectedDecodeBHist Q)
                                  (realLineConnectedDecodeBHist E)
                                  (realLineConnectedDecodeBHist H)
                                  (realLineConnectedDecodeBHist C)
                                  (realLineConnectedDecodeBHist P)
                                  (realLineConnectedDecodeBHist N))
                            | _ :: _ => none

private theorem realLineConnected_round_trip :
    ∀ x : RealLineConnectedUp,
      realLineConnectedFromEventFlow (realLineConnectedToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk realSourceRow intervalChainRow intermediateRow continuousMapRow dyadicRow windowRow
      readbackRow terminalSealRow transportRow replayRow provenanceRow localNameRow =>
      change
        some
          (RealLineConnectedUp.mk
            (realLineConnectedDecodeBHist (realLineConnectedEncodeBHist realSourceRow))
            (realLineConnectedDecodeBHist (realLineConnectedEncodeBHist intervalChainRow))
            (realLineConnectedDecodeBHist (realLineConnectedEncodeBHist intermediateRow))
            (realLineConnectedDecodeBHist (realLineConnectedEncodeBHist continuousMapRow))
            (realLineConnectedDecodeBHist (realLineConnectedEncodeBHist dyadicRow))
            (realLineConnectedDecodeBHist (realLineConnectedEncodeBHist windowRow))
            (realLineConnectedDecodeBHist (realLineConnectedEncodeBHist readbackRow))
            (realLineConnectedDecodeBHist (realLineConnectedEncodeBHist terminalSealRow))
            (realLineConnectedDecodeBHist (realLineConnectedEncodeBHist transportRow))
            (realLineConnectedDecodeBHist (realLineConnectedEncodeBHist replayRow))
            (realLineConnectedDecodeBHist (realLineConnectedEncodeBHist provenanceRow))
            (realLineConnectedDecodeBHist (realLineConnectedEncodeBHist localNameRow))) =
          some
            (RealLineConnectedUp.mk realSourceRow intervalChainRow intermediateRow
              continuousMapRow dyadicRow windowRow readbackRow terminalSealRow transportRow
              replayRow provenanceRow localNameRow)
      rw [realLineConnectedDecode_encode_bhist realSourceRow,
        realLineConnectedDecode_encode_bhist intervalChainRow,
        realLineConnectedDecode_encode_bhist intermediateRow,
        realLineConnectedDecode_encode_bhist continuousMapRow,
        realLineConnectedDecode_encode_bhist dyadicRow,
        realLineConnectedDecode_encode_bhist windowRow,
        realLineConnectedDecode_encode_bhist readbackRow,
        realLineConnectedDecode_encode_bhist terminalSealRow,
        realLineConnectedDecode_encode_bhist transportRow,
        realLineConnectedDecode_encode_bhist replayRow,
        realLineConnectedDecode_encode_bhist provenanceRow,
        realLineConnectedDecode_encode_bhist localNameRow]

private theorem realLineConnectedToEventFlow_injective {x y : RealLineConnectedUp} :
    realLineConnectedToEventFlow x = realLineConnectedToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realLineConnectedFromEventFlow (realLineConnectedToEventFlow x) =
        realLineConnectedFromEventFlow (realLineConnectedToEventFlow y) :=
    congrArg realLineConnectedFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realLineConnected_round_trip x).symm
      (Eq.trans hread (realLineConnected_round_trip y)))

instance realLineConnectedBHistCarrier : BHistCarrier RealLineConnectedUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realLineConnectedToEventFlow
  fromEventFlow := realLineConnectedFromEventFlow

instance realLineConnectedChapterTasteGate : ChapterTasteGate RealLineConnectedUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realLineConnectedFromEventFlow (realLineConnectedToEventFlow x) = some x
    exact realLineConnected_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realLineConnectedToEventFlow_injective heq)

theorem RealLineConnectedTasteGate_single_carrier_alignment :
    (∀ h : BHist, realLineConnectedDecodeBHist (realLineConnectedEncodeBHist h) = h) ∧
      (∀ x : RealLineConnectedUp,
        realLineConnectedFromEventFlow (realLineConnectedToEventFlow x) = some x) ∧
        (∀ x y : RealLineConnectedUp,
          realLineConnectedToEventFlow x = realLineConnectedToEventFlow y → x = y) ∧
          realLineConnectedEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact realLineConnectedDecode_encode_bhist
  · constructor
    · exact realLineConnected_round_trip
    · constructor
      · intro x y heq
        exact realLineConnectedToEventFlow_injective heq
      · rfl

end BEDC.Derived.RealLineConnectedUp
