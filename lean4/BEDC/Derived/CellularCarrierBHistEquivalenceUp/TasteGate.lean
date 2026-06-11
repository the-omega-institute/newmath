import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CellularCarrierBHistEquivalenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CellularCarrierBHistEquivalenceUp : Type where
  | mk (W B D R K H C P N : BHist) : CellularCarrierBHistEquivalenceUp
  deriving DecidableEq

def cellularCarrierBHistEquivalenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cellularCarrierBHistEquivalenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cellularCarrierBHistEquivalenceEncodeBHist h

def cellularCarrierBHistEquivalenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cellularCarrierBHistEquivalenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cellularCarrierBHistEquivalenceDecodeBHist tail)

private theorem CellularCarrierBHistEquivalenceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cellularCarrierBHistEquivalenceDecodeBHist
          (cellularCarrierBHistEquivalenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cellularCarrierBHistEquivalenceFields :
    CellularCarrierBHistEquivalenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CellularCarrierBHistEquivalenceUp.mk W B D R K H C P N => [W, B, D, R, K, H, C, P, N]

def cellularCarrierBHistEquivalenceToEventFlow :
    CellularCarrierBHistEquivalenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map cellularCarrierBHistEquivalenceEncodeBHist
      (cellularCarrierBHistEquivalenceFields x)

def cellularCarrierBHistEquivalenceFromEventFlow
    (ef : EventFlow) : Option CellularCarrierBHistEquivalenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match ef with
  | [] => none
  | W :: rest0 =>
      match rest0 with
      | [] => none
      | B :: rest1 =>
          match rest1 with
          | [] => none
          | D :: rest2 =>
              match rest2 with
              | [] => none
              | R :: rest3 =>
                  match rest3 with
                  | [] => none
                  | K :: rest4 =>
                      match rest4 with
                      | [] => none
                      | H :: rest5 =>
                          match rest5 with
                          | [] => none
                          | C :: rest6 =>
                              match rest6 with
                              | [] => none
                              | P :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | N :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (CellularCarrierBHistEquivalenceUp.mk
                                              (cellularCarrierBHistEquivalenceDecodeBHist W)
                                              (cellularCarrierBHistEquivalenceDecodeBHist B)
                                              (cellularCarrierBHistEquivalenceDecodeBHist D)
                                              (cellularCarrierBHistEquivalenceDecodeBHist R)
                                              (cellularCarrierBHistEquivalenceDecodeBHist K)
                                              (cellularCarrierBHistEquivalenceDecodeBHist H)
                                              (cellularCarrierBHistEquivalenceDecodeBHist C)
                                              (cellularCarrierBHistEquivalenceDecodeBHist P)
                                              (cellularCarrierBHistEquivalenceDecodeBHist N))
                                      | _ :: _ => none

private theorem CellularCarrierBHistEquivalenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CellularCarrierBHistEquivalenceUp,
      cellularCarrierBHistEquivalenceFromEventFlow
          (cellularCarrierBHistEquivalenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk W B D R K H C P N =>
      change
        some
          (CellularCarrierBHistEquivalenceUp.mk
            (cellularCarrierBHistEquivalenceDecodeBHist
              (cellularCarrierBHistEquivalenceEncodeBHist W))
            (cellularCarrierBHistEquivalenceDecodeBHist
              (cellularCarrierBHistEquivalenceEncodeBHist B))
            (cellularCarrierBHistEquivalenceDecodeBHist
              (cellularCarrierBHistEquivalenceEncodeBHist D))
            (cellularCarrierBHistEquivalenceDecodeBHist
              (cellularCarrierBHistEquivalenceEncodeBHist R))
            (cellularCarrierBHistEquivalenceDecodeBHist
              (cellularCarrierBHistEquivalenceEncodeBHist K))
            (cellularCarrierBHistEquivalenceDecodeBHist
              (cellularCarrierBHistEquivalenceEncodeBHist H))
            (cellularCarrierBHistEquivalenceDecodeBHist
              (cellularCarrierBHistEquivalenceEncodeBHist C))
            (cellularCarrierBHistEquivalenceDecodeBHist
              (cellularCarrierBHistEquivalenceEncodeBHist P))
            (cellularCarrierBHistEquivalenceDecodeBHist
              (cellularCarrierBHistEquivalenceEncodeBHist N))) =
          some (CellularCarrierBHistEquivalenceUp.mk W B D R K H C P N)
      rw [CellularCarrierBHistEquivalenceTasteGate_single_carrier_alignment_decode W,
        CellularCarrierBHistEquivalenceTasteGate_single_carrier_alignment_decode B,
        CellularCarrierBHistEquivalenceTasteGate_single_carrier_alignment_decode D,
        CellularCarrierBHistEquivalenceTasteGate_single_carrier_alignment_decode R,
        CellularCarrierBHistEquivalenceTasteGate_single_carrier_alignment_decode K,
        CellularCarrierBHistEquivalenceTasteGate_single_carrier_alignment_decode H,
        CellularCarrierBHistEquivalenceTasteGate_single_carrier_alignment_decode C,
        CellularCarrierBHistEquivalenceTasteGate_single_carrier_alignment_decode P,
        CellularCarrierBHistEquivalenceTasteGate_single_carrier_alignment_decode N]

private theorem CellularCarrierBHistEquivalenceTasteGate_single_carrier_alignment_injective
    {x y : CellularCarrierBHistEquivalenceUp} :
    cellularCarrierBHistEquivalenceToEventFlow x =
        cellularCarrierBHistEquivalenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cellularCarrierBHistEquivalenceFromEventFlow
          (cellularCarrierBHistEquivalenceToEventFlow x) =
        cellularCarrierBHistEquivalenceFromEventFlow
          (cellularCarrierBHistEquivalenceToEventFlow y) :=
    congrArg cellularCarrierBHistEquivalenceFromEventFlow heq
  have hsome : some x = some y :=
    Eq.trans
      (CellularCarrierBHistEquivalenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CellularCarrierBHistEquivalenceTasteGate_single_carrier_alignment_round_trip y))
  cases hsome
  rfl

private theorem CellularCarrierBHistEquivalenceTasteGate_single_carrier_alignment_fields :
    ∀ x y : CellularCarrierBHistEquivalenceUp,
      cellularCarrierBHistEquivalenceFields x =
          cellularCarrierBHistEquivalenceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk W1 B1 D1 R1 K1 H1 C1 P1 N1 =>
      cases y with
      | mk W2 B2 D2 R2 K2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance cellularCarrierBHistEquivalenceBHistCarrier :
    BHistCarrier CellularCarrierBHistEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cellularCarrierBHistEquivalenceToEventFlow
  fromEventFlow := cellularCarrierBHistEquivalenceFromEventFlow

instance cellularCarrierBHistEquivalenceChapterTasteGate :
    ChapterTasteGate CellularCarrierBHistEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cellularCarrierBHistEquivalenceFromEventFlow
          (cellularCarrierBHistEquivalenceToEventFlow x) = some x
    exact CellularCarrierBHistEquivalenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CellularCarrierBHistEquivalenceTasteGate_single_carrier_alignment_injective heq)

instance cellularCarrierBHistEquivalenceFieldFaithful :
    FieldFaithful CellularCarrierBHistEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cellularCarrierBHistEquivalenceFields
  field_faithful :=
    CellularCarrierBHistEquivalenceTasteGate_single_carrier_alignment_fields

instance cellularCarrierBHistEquivalenceNontrivial :
    Nontrivial CellularCarrierBHistEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CellularCarrierBHistEquivalenceUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CellularCarrierBHistEquivalenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CellularCarrierBHistEquivalenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cellularCarrierBHistEquivalenceChapterTasteGate

theorem CellularCarrierBHistEquivalenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cellularCarrierBHistEquivalenceDecodeBHist
        (cellularCarrierBHistEquivalenceEncodeBHist h) = h) ∧
      (∀ x : CellularCarrierBHistEquivalenceUp,
        cellularCarrierBHistEquivalenceFromEventFlow
          (cellularCarrierBHistEquivalenceToEventFlow x) = some x) ∧
        (∀ x y : CellularCarrierBHistEquivalenceUp,
          cellularCarrierBHistEquivalenceToEventFlow x =
              cellularCarrierBHistEquivalenceToEventFlow y → x = y) ∧
          cellularCarrierBHistEquivalenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact CellularCarrierBHistEquivalenceTasteGate_single_carrier_alignment_decode
  · constructor
    · exact CellularCarrierBHistEquivalenceTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact CellularCarrierBHistEquivalenceTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.CellularCarrierBHistEquivalenceUp
