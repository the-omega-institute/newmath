import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CellularBoundaryConditionUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CellularBoundaryConditionUp : Type where
  | mk : (E W R A H C P N : BHist) → CellularBoundaryConditionUp
  deriving DecidableEq

def cellularBoundaryConditionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cellularBoundaryConditionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cellularBoundaryConditionEncodeBHist h

def cellularBoundaryConditionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cellularBoundaryConditionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cellularBoundaryConditionDecodeBHist tail)

private theorem cellularBoundaryConditionDecode_encode_bhist :
    ∀ h : BHist,
      cellularBoundaryConditionDecodeBHist (cellularBoundaryConditionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cellularBoundaryConditionFields : CellularBoundaryConditionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CellularBoundaryConditionUp.mk E W R A H C P N => [E, W, R, A, H, C, P, N]

def cellularBoundaryConditionToEventFlow : CellularBoundaryConditionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CellularBoundaryConditionUp.mk E W R A H C P N =>
      [[BMark.b0],
        cellularBoundaryConditionEncodeBHist E,
        [BMark.b1, BMark.b0],
        cellularBoundaryConditionEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b0],
        cellularBoundaryConditionEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cellularBoundaryConditionEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cellularBoundaryConditionEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cellularBoundaryConditionEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cellularBoundaryConditionEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        cellularBoundaryConditionEncodeBHist N]

private def cellularBoundaryConditionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cellularBoundaryConditionEventAtDefault index rest

def cellularBoundaryConditionFromEventFlow (ef : EventFlow) :
    Option CellularBoundaryConditionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CellularBoundaryConditionUp.mk
      (cellularBoundaryConditionDecodeBHist (cellularBoundaryConditionEventAtDefault 1 ef))
      (cellularBoundaryConditionDecodeBHist (cellularBoundaryConditionEventAtDefault 3 ef))
      (cellularBoundaryConditionDecodeBHist (cellularBoundaryConditionEventAtDefault 5 ef))
      (cellularBoundaryConditionDecodeBHist (cellularBoundaryConditionEventAtDefault 7 ef))
      (cellularBoundaryConditionDecodeBHist (cellularBoundaryConditionEventAtDefault 9 ef))
      (cellularBoundaryConditionDecodeBHist (cellularBoundaryConditionEventAtDefault 11 ef))
      (cellularBoundaryConditionDecodeBHist (cellularBoundaryConditionEventAtDefault 13 ef))
      (cellularBoundaryConditionDecodeBHist (cellularBoundaryConditionEventAtDefault 15 ef)))

private theorem cellularBoundaryCondition_round_trip :
    ∀ x : CellularBoundaryConditionUp,
      cellularBoundaryConditionFromEventFlow (cellularBoundaryConditionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk E W R A H C P N =>
      change
        some
          (CellularBoundaryConditionUp.mk
            (cellularBoundaryConditionDecodeBHist (cellularBoundaryConditionEncodeBHist E))
            (cellularBoundaryConditionDecodeBHist (cellularBoundaryConditionEncodeBHist W))
            (cellularBoundaryConditionDecodeBHist (cellularBoundaryConditionEncodeBHist R))
            (cellularBoundaryConditionDecodeBHist (cellularBoundaryConditionEncodeBHist A))
            (cellularBoundaryConditionDecodeBHist (cellularBoundaryConditionEncodeBHist H))
            (cellularBoundaryConditionDecodeBHist (cellularBoundaryConditionEncodeBHist C))
            (cellularBoundaryConditionDecodeBHist (cellularBoundaryConditionEncodeBHist P))
            (cellularBoundaryConditionDecodeBHist (cellularBoundaryConditionEncodeBHist N))) =
          some (CellularBoundaryConditionUp.mk E W R A H C P N)
      rw [cellularBoundaryConditionDecode_encode_bhist E,
        cellularBoundaryConditionDecode_encode_bhist W,
        cellularBoundaryConditionDecode_encode_bhist R,
        cellularBoundaryConditionDecode_encode_bhist A,
        cellularBoundaryConditionDecode_encode_bhist H,
        cellularBoundaryConditionDecode_encode_bhist C,
        cellularBoundaryConditionDecode_encode_bhist P,
        cellularBoundaryConditionDecode_encode_bhist N]

private theorem cellularBoundaryConditionToEventFlow_injective
    {x y : CellularBoundaryConditionUp} :
    cellularBoundaryConditionToEventFlow x = cellularBoundaryConditionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cellularBoundaryConditionFromEventFlow (cellularBoundaryConditionToEventFlow x) =
        cellularBoundaryConditionFromEventFlow (cellularBoundaryConditionToEventFlow y) :=
    congrArg cellularBoundaryConditionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cellularBoundaryCondition_round_trip x).symm
      (Eq.trans hread (cellularBoundaryCondition_round_trip y)))

private theorem cellularBoundaryCondition_fields_faithful :
    ∀ x y : CellularBoundaryConditionUp,
      cellularBoundaryConditionFields x = cellularBoundaryConditionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk E₁ W₁ R₁ A₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk E₂ W₂ R₂ A₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance cellularBoundaryConditionBHistCarrier :
    BHistCarrier CellularBoundaryConditionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cellularBoundaryConditionToEventFlow
  fromEventFlow := cellularBoundaryConditionFromEventFlow

instance cellularBoundaryConditionChapterTasteGate :
    ChapterTasteGate CellularBoundaryConditionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cellularBoundaryConditionFromEventFlow (cellularBoundaryConditionToEventFlow x) =
      some x
    exact cellularBoundaryCondition_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cellularBoundaryConditionToEventFlow_injective heq)

instance cellularBoundaryConditionFieldFaithful :
    FieldFaithful CellularBoundaryConditionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cellularBoundaryConditionFields
  field_faithful := cellularBoundaryCondition_fields_faithful

instance cellularBoundaryConditionNontrivial :
    Nontrivial CellularBoundaryConditionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CellularBoundaryConditionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CellularBoundaryConditionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CellularBoundaryConditionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cellularBoundaryConditionChapterTasteGate

theorem CellularBoundaryConditionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cellularBoundaryConditionDecodeBHist (cellularBoundaryConditionEncodeBHist h) = h) ∧
      (∀ x : CellularBoundaryConditionUp,
        cellularBoundaryConditionFromEventFlow (cellularBoundaryConditionToEventFlow x) =
          some x) ∧
        (∀ x y : CellularBoundaryConditionUp,
          cellularBoundaryConditionToEventFlow x = cellularBoundaryConditionToEventFlow y →
            x = y) ∧
          cellularBoundaryConditionEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : CellularBoundaryConditionUp,
              cellularBoundaryConditionFields x = cellularBoundaryConditionFields y →
                x = y) ∧
              (∃ x y : CellularBoundaryConditionUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact cellularBoundaryConditionDecode_encode_bhist
  · constructor
    · exact cellularBoundaryCondition_round_trip
    · constructor
      · intro x y heq
        exact cellularBoundaryConditionToEventFlow_injective heq
      · constructor
        · rfl
        · constructor
          · exact cellularBoundaryCondition_fields_faithful
          · exact
              ⟨(cellularBoundaryConditionNontrivial.witness_pair).fst,
                (cellularBoundaryConditionNontrivial.witness_pair).snd.fst,
                (cellularBoundaryConditionNontrivial.witness_pair).snd.snd⟩

end BEDC.Derived.CellularBoundaryConditionUp.TasteGate

namespace BEDC.Derived.CellularBoundaryConditionUp

def taste_gate :
    BEDC.Meta.TasteGate.ChapterTasteGate TasteGate.CellularBoundaryConditionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  TasteGate.taste_gate

end BEDC.Derived.CellularBoundaryConditionUp
