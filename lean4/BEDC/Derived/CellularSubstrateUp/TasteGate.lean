import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CellularSubstrateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CellularSubstrateUp : Type where
  | mk (S N U G H C P L : BHist) : CellularSubstrateUp
  deriving DecidableEq

def cellularSubstrateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cellularSubstrateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cellularSubstrateEncodeBHist h

def cellularSubstrateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cellularSubstrateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cellularSubstrateDecodeBHist tail)

private theorem cellularSubstrate_decode_encode_bhist :
    ∀ h : BHist, cellularSubstrateDecodeBHist (cellularSubstrateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cellularSubstrateToEventFlow : CellularSubstrateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CellularSubstrateUp.mk S N U G H C P L =>
      [[BMark.b0], cellularSubstrateEncodeBHist S,
        [BMark.b1, BMark.b0], cellularSubstrateEncodeBHist N,
        [BMark.b1, BMark.b1, BMark.b0], cellularSubstrateEncodeBHist U,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0], cellularSubstrateEncodeBHist G,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cellularSubstrateEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cellularSubstrateEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cellularSubstrateEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        cellularSubstrateEncodeBHist L]

def cellularSubstrateFromEventFlow : EventFlow → Option CellularSubstrateUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | S :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | N :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | U :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | G :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | H :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | C :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | P :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | L :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (CellularSubstrateUp.mk
                                                                          (cellularSubstrateDecodeBHist
                                                                            S)
                                                                          (cellularSubstrateDecodeBHist
                                                                            N)
                                                                          (cellularSubstrateDecodeBHist
                                                                            U)
                                                                          (cellularSubstrateDecodeBHist
                                                                            G)
                                                                          (cellularSubstrateDecodeBHist
                                                                            H)
                                                                          (cellularSubstrateDecodeBHist
                                                                            C)
                                                                          (cellularSubstrateDecodeBHist
                                                                            P)
                                                                          (cellularSubstrateDecodeBHist
                                                                            L))
                                                                  | _ :: _ => none

private theorem cellularSubstrate_round_trip :
    ∀ x : CellularSubstrateUp,
      cellularSubstrateFromEventFlow (cellularSubstrateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S N U G H C P L =>
      change
        some
          (CellularSubstrateUp.mk
            (cellularSubstrateDecodeBHist (cellularSubstrateEncodeBHist S))
            (cellularSubstrateDecodeBHist (cellularSubstrateEncodeBHist N))
            (cellularSubstrateDecodeBHist (cellularSubstrateEncodeBHist U))
            (cellularSubstrateDecodeBHist (cellularSubstrateEncodeBHist G))
            (cellularSubstrateDecodeBHist (cellularSubstrateEncodeBHist H))
            (cellularSubstrateDecodeBHist (cellularSubstrateEncodeBHist C))
            (cellularSubstrateDecodeBHist (cellularSubstrateEncodeBHist P))
            (cellularSubstrateDecodeBHist (cellularSubstrateEncodeBHist L))) =
          some (CellularSubstrateUp.mk S N U G H C P L)
      rw [cellularSubstrate_decode_encode_bhist S, cellularSubstrate_decode_encode_bhist N,
        cellularSubstrate_decode_encode_bhist U, cellularSubstrate_decode_encode_bhist G,
        cellularSubstrate_decode_encode_bhist H, cellularSubstrate_decode_encode_bhist C,
        cellularSubstrate_decode_encode_bhist P, cellularSubstrate_decode_encode_bhist L]

private theorem cellularSubstrateToEventFlow_injective {x y : CellularSubstrateUp} :
    cellularSubstrateToEventFlow x = cellularSubstrateToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cellularSubstrateFromEventFlow (cellularSubstrateToEventFlow x) =
        cellularSubstrateFromEventFlow (cellularSubstrateToEventFlow y) :=
    congrArg cellularSubstrateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cellularSubstrate_round_trip x).symm
      (Eq.trans hread (cellularSubstrate_round_trip y)))

def cellularSubstrateFields : CellularSubstrateUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CellularSubstrateUp.mk S N U G H C P L => [S, N, U, G, H, C, P, L]

private theorem cellularSubstrate_field_faithful :
    ∀ x y : CellularSubstrateUp, cellularSubstrateFields x = cellularSubstrateFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S N U G H C P L =>
      cases y with
      | mk S' N' U' G' H' C' P' L' =>
          cases hfields
          rfl

instance cellularSubstrateBHistCarrier : BHistCarrier CellularSubstrateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cellularSubstrateToEventFlow
  fromEventFlow := cellularSubstrateFromEventFlow

instance cellularSubstrateChapterTasteGate : ChapterTasteGate CellularSubstrateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cellularSubstrateFromEventFlow (cellularSubstrateToEventFlow x) = some x
    exact cellularSubstrate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cellularSubstrateToEventFlow_injective heq)

instance cellularSubstrateFieldFaithful : FieldFaithful CellularSubstrateUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cellularSubstrateFields
  field_faithful := cellularSubstrate_field_faithful

instance cellularSubstrateNontrivial : Nontrivial CellularSubstrateUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CellularSubstrateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      CellularSubstrateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CellularSubstrateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cellularSubstrateChapterTasteGate

theorem CellularSubstrateTasteGate_single_carrier_alignment :
    (∀ h : BHist, cellularSubstrateDecodeBHist (cellularSubstrateEncodeBHist h) = h) ∧
      (∀ x : CellularSubstrateUp,
        cellularSubstrateFromEventFlow (cellularSubstrateToEventFlow x) = some x) ∧
        (∀ x y : CellularSubstrateUp,
          cellularSubstrateToEventFlow x = cellularSubstrateToEventFlow y → x = y) ∧
          cellularSubstrateEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : CellularSubstrateUp, cellularSubstrateFields x = cellularSubstrateFields y →
              x = y) ∧
              (∃ x y : CellularSubstrateUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact cellularSubstrate_decode_encode_bhist
  · constructor
    · exact cellularSubstrate_round_trip
    · constructor
      · intro x y heq
        exact cellularSubstrateToEventFlow_injective heq
      · constructor
        · rfl
        · constructor
          · exact cellularSubstrate_field_faithful
          · exact
              ⟨CellularSubstrateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
                CellularSubstrateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
                by
                  intro h
                  cases h⟩

end BEDC.Derived.CellularSubstrateUp
