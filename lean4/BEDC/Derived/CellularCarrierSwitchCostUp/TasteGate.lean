import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CellularCarrierSwitchCostUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CellularCarrierSwitchCostUp : Type where
  | mk (B O V R A K H C P N : BHist) : CellularCarrierSwitchCostUp
  deriving DecidableEq

def cellularCarrierSwitchCostEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cellularCarrierSwitchCostEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cellularCarrierSwitchCostEncodeBHist h

def cellularCarrierSwitchCostDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cellularCarrierSwitchCostDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cellularCarrierSwitchCostDecodeBHist tail)

private theorem cellularCarrierSwitchCost_decode_encode_bhist :
    forall h : BHist,
      cellularCarrierSwitchCostDecodeBHist (cellularCarrierSwitchCostEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cellularCarrierSwitchCostFields :
    CellularCarrierSwitchCostUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CellularCarrierSwitchCostUp.mk B O V R A K H C P N =>
      [B, O, V, R, A, K, H, C, P, N]

def cellularCarrierSwitchCostToEventFlow :
    CellularCarrierSwitchCostUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CellularCarrierSwitchCostUp.mk B O V R A K H C P N =>
      [cellularCarrierSwitchCostEncodeBHist B,
        cellularCarrierSwitchCostEncodeBHist O,
        cellularCarrierSwitchCostEncodeBHist V,
        cellularCarrierSwitchCostEncodeBHist R,
        cellularCarrierSwitchCostEncodeBHist A,
        cellularCarrierSwitchCostEncodeBHist K,
        cellularCarrierSwitchCostEncodeBHist H,
        cellularCarrierSwitchCostEncodeBHist C,
        cellularCarrierSwitchCostEncodeBHist P,
        cellularCarrierSwitchCostEncodeBHist N]

def cellularCarrierSwitchCostFromEventFlow :
    EventFlow -> Option CellularCarrierSwitchCostUp
  -- BEDC touchpoint anchor: BHist BMark
  | [B, O, V, R, A, K, H, C, P, N] =>
      some
        (CellularCarrierSwitchCostUp.mk
          (cellularCarrierSwitchCostDecodeBHist B)
          (cellularCarrierSwitchCostDecodeBHist O)
          (cellularCarrierSwitchCostDecodeBHist V)
          (cellularCarrierSwitchCostDecodeBHist R)
          (cellularCarrierSwitchCostDecodeBHist A)
          (cellularCarrierSwitchCostDecodeBHist K)
          (cellularCarrierSwitchCostDecodeBHist H)
          (cellularCarrierSwitchCostDecodeBHist C)
          (cellularCarrierSwitchCostDecodeBHist P)
          (cellularCarrierSwitchCostDecodeBHist N))
  | _ => none

private theorem cellularCarrierSwitchCost_round_trip :
    forall x : CellularCarrierSwitchCostUp,
      cellularCarrierSwitchCostFromEventFlow (cellularCarrierSwitchCostToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B O V R A K H C P N =>
      change
        some
          (CellularCarrierSwitchCostUp.mk
            (cellularCarrierSwitchCostDecodeBHist (cellularCarrierSwitchCostEncodeBHist B))
            (cellularCarrierSwitchCostDecodeBHist (cellularCarrierSwitchCostEncodeBHist O))
            (cellularCarrierSwitchCostDecodeBHist (cellularCarrierSwitchCostEncodeBHist V))
            (cellularCarrierSwitchCostDecodeBHist (cellularCarrierSwitchCostEncodeBHist R))
            (cellularCarrierSwitchCostDecodeBHist (cellularCarrierSwitchCostEncodeBHist A))
            (cellularCarrierSwitchCostDecodeBHist (cellularCarrierSwitchCostEncodeBHist K))
            (cellularCarrierSwitchCostDecodeBHist (cellularCarrierSwitchCostEncodeBHist H))
            (cellularCarrierSwitchCostDecodeBHist (cellularCarrierSwitchCostEncodeBHist C))
            (cellularCarrierSwitchCostDecodeBHist (cellularCarrierSwitchCostEncodeBHist P))
            (cellularCarrierSwitchCostDecodeBHist (cellularCarrierSwitchCostEncodeBHist N))) =
          some (CellularCarrierSwitchCostUp.mk B O V R A K H C P N)
      rw [cellularCarrierSwitchCost_decode_encode_bhist B,
        cellularCarrierSwitchCost_decode_encode_bhist O,
        cellularCarrierSwitchCost_decode_encode_bhist V,
        cellularCarrierSwitchCost_decode_encode_bhist R,
        cellularCarrierSwitchCost_decode_encode_bhist A,
        cellularCarrierSwitchCost_decode_encode_bhist K,
        cellularCarrierSwitchCost_decode_encode_bhist H,
        cellularCarrierSwitchCost_decode_encode_bhist C,
        cellularCarrierSwitchCost_decode_encode_bhist P,
        cellularCarrierSwitchCost_decode_encode_bhist N]

private theorem cellularCarrierSwitchCostToEventFlow_injective
    {x y : CellularCarrierSwitchCostUp} :
    cellularCarrierSwitchCostToEventFlow x = cellularCarrierSwitchCostToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cellularCarrierSwitchCostFromEventFlow (cellularCarrierSwitchCostToEventFlow x) =
        cellularCarrierSwitchCostFromEventFlow (cellularCarrierSwitchCostToEventFlow y) :=
    congrArg cellularCarrierSwitchCostFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cellularCarrierSwitchCost_round_trip x).symm
      (Eq.trans hread (cellularCarrierSwitchCost_round_trip y)))

private theorem cellularCarrierSwitchCost_field_faithful :
    forall x y : CellularCarrierSwitchCostUp,
      cellularCarrierSwitchCostFields x = cellularCarrierSwitchCostFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk B1 O1 V1 R1 A1 K1 H1 C1 P1 N1 =>
      cases y with
      | mk B2 O2 V2 R2 A2 K2 H2 C2 P2 N2 =>
          cases h
          rfl

instance cellularCarrierSwitchCostBHistCarrier :
    BHistCarrier CellularCarrierSwitchCostUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cellularCarrierSwitchCostToEventFlow
  fromEventFlow := cellularCarrierSwitchCostFromEventFlow

instance cellularCarrierSwitchCostChapterTasteGate :
    ChapterTasteGate CellularCarrierSwitchCostUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cellularCarrierSwitchCostFromEventFlow (cellularCarrierSwitchCostToEventFlow x) =
      some x
    exact cellularCarrierSwitchCost_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cellularCarrierSwitchCostToEventFlow_injective heq)

instance cellularCarrierSwitchCostFieldFaithful :
    FieldFaithful CellularCarrierSwitchCostUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cellularCarrierSwitchCostFields
  field_faithful := cellularCarrierSwitchCost_field_faithful

instance cellularCarrierSwitchCostNontrivial :
    Nontrivial CellularCarrierSwitchCostUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CellularCarrierSwitchCostUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CellularCarrierSwitchCostUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CellularCarrierSwitchCostUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cellularCarrierSwitchCostChapterTasteGate

theorem CellularCarrierSwitchCostTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cellularCarrierSwitchCostDecodeBHist
        (cellularCarrierSwitchCostEncodeBHist h) = h) ∧
      (∀ x y : CellularCarrierSwitchCostUp,
        cellularCarrierSwitchCostFields x =
          cellularCarrierSwitchCostFields y -> x = y) ∧
        (∃ x y : CellularCarrierSwitchCostUp, x ≠ y) ∧
          cellularCarrierSwitchCostEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨cellularCarrierSwitchCost_decode_encode_bhist,
      cellularCarrierSwitchCost_field_faithful,
      ⟨CellularCarrierSwitchCostUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        CellularCarrierSwitchCostUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        by
          intro h
          cases h⟩,
      rfl⟩

end BEDC.Derived.CellularCarrierSwitchCostUp
