import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CellularOrbitSynchronizationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CellularOrbitSynchronizationUp : Type where
  | mk (O0 O1 G B Q A T H C P N : BHist) : CellularOrbitSynchronizationUp
  deriving DecidableEq

def cellularOrbitSynchronizationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cellularOrbitSynchronizationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cellularOrbitSynchronizationEncodeBHist h

def cellularOrbitSynchronizationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cellularOrbitSynchronizationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cellularOrbitSynchronizationDecodeBHist tail)

private theorem CellularOrbitSynchronizationTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cellularOrbitSynchronizationDecodeBHist
        (cellularOrbitSynchronizationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cellularOrbitSynchronizationFields :
    CellularOrbitSynchronizationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CellularOrbitSynchronizationUp.mk O0 O1 G B Q A T H C P N =>
      [O0, O1, G, B, Q, A, T, H, C, P, N]

def cellularOrbitSynchronizationToEventFlow :
    CellularOrbitSynchronizationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cellularOrbitSynchronizationFields x).map
      cellularOrbitSynchronizationEncodeBHist

private def cellularOrbitSynchronizationEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      cellularOrbitSynchronizationEventAtDefault index rest

def cellularOrbitSynchronizationFromEventFlow
    (ef : EventFlow) : Option CellularOrbitSynchronizationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CellularOrbitSynchronizationUp.mk
      (cellularOrbitSynchronizationDecodeBHist
        (cellularOrbitSynchronizationEventAtDefault 0 ef))
      (cellularOrbitSynchronizationDecodeBHist
        (cellularOrbitSynchronizationEventAtDefault 1 ef))
      (cellularOrbitSynchronizationDecodeBHist
        (cellularOrbitSynchronizationEventAtDefault 2 ef))
      (cellularOrbitSynchronizationDecodeBHist
        (cellularOrbitSynchronizationEventAtDefault 3 ef))
      (cellularOrbitSynchronizationDecodeBHist
        (cellularOrbitSynchronizationEventAtDefault 4 ef))
      (cellularOrbitSynchronizationDecodeBHist
        (cellularOrbitSynchronizationEventAtDefault 5 ef))
      (cellularOrbitSynchronizationDecodeBHist
        (cellularOrbitSynchronizationEventAtDefault 6 ef))
      (cellularOrbitSynchronizationDecodeBHist
        (cellularOrbitSynchronizationEventAtDefault 7 ef))
      (cellularOrbitSynchronizationDecodeBHist
        (cellularOrbitSynchronizationEventAtDefault 8 ef))
      (cellularOrbitSynchronizationDecodeBHist
        (cellularOrbitSynchronizationEventAtDefault 9 ef))
      (cellularOrbitSynchronizationDecodeBHist
        (cellularOrbitSynchronizationEventAtDefault 10 ef)))

private theorem CellularOrbitSynchronizationTasteGate_single_carrier_alignment_round_trip
    (x : CellularOrbitSynchronizationUp) :
    cellularOrbitSynchronizationFromEventFlow
      (cellularOrbitSynchronizationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk O0 O1 G B Q A T H C P N =>
      change
        some
          (CellularOrbitSynchronizationUp.mk
            (cellularOrbitSynchronizationDecodeBHist
              (cellularOrbitSynchronizationEncodeBHist O0))
            (cellularOrbitSynchronizationDecodeBHist
              (cellularOrbitSynchronizationEncodeBHist O1))
            (cellularOrbitSynchronizationDecodeBHist
              (cellularOrbitSynchronizationEncodeBHist G))
            (cellularOrbitSynchronizationDecodeBHist
              (cellularOrbitSynchronizationEncodeBHist B))
            (cellularOrbitSynchronizationDecodeBHist
              (cellularOrbitSynchronizationEncodeBHist Q))
            (cellularOrbitSynchronizationDecodeBHist
              (cellularOrbitSynchronizationEncodeBHist A))
            (cellularOrbitSynchronizationDecodeBHist
              (cellularOrbitSynchronizationEncodeBHist T))
            (cellularOrbitSynchronizationDecodeBHist
              (cellularOrbitSynchronizationEncodeBHist H))
            (cellularOrbitSynchronizationDecodeBHist
              (cellularOrbitSynchronizationEncodeBHist C))
            (cellularOrbitSynchronizationDecodeBHist
              (cellularOrbitSynchronizationEncodeBHist P))
            (cellularOrbitSynchronizationDecodeBHist
              (cellularOrbitSynchronizationEncodeBHist N))) =
          some (CellularOrbitSynchronizationUp.mk O0 O1 G B Q A T H C P N)
      rw [CellularOrbitSynchronizationTasteGate_single_carrier_alignment_decode_encode O0,
        CellularOrbitSynchronizationTasteGate_single_carrier_alignment_decode_encode O1,
        CellularOrbitSynchronizationTasteGate_single_carrier_alignment_decode_encode G,
        CellularOrbitSynchronizationTasteGate_single_carrier_alignment_decode_encode B,
        CellularOrbitSynchronizationTasteGate_single_carrier_alignment_decode_encode Q,
        CellularOrbitSynchronizationTasteGate_single_carrier_alignment_decode_encode A,
        CellularOrbitSynchronizationTasteGate_single_carrier_alignment_decode_encode T,
        CellularOrbitSynchronizationTasteGate_single_carrier_alignment_decode_encode H,
        CellularOrbitSynchronizationTasteGate_single_carrier_alignment_decode_encode C,
        CellularOrbitSynchronizationTasteGate_single_carrier_alignment_decode_encode P,
        CellularOrbitSynchronizationTasteGate_single_carrier_alignment_decode_encode N]

private theorem CellularOrbitSynchronizationTasteGate_single_carrier_alignment_injective
    {x y : CellularOrbitSynchronizationUp} :
    cellularOrbitSynchronizationToEventFlow x =
      cellularOrbitSynchronizationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cellularOrbitSynchronizationFromEventFlow
          (cellularOrbitSynchronizationToEventFlow x) =
        cellularOrbitSynchronizationFromEventFlow
          (cellularOrbitSynchronizationToEventFlow y) :=
    congrArg cellularOrbitSynchronizationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CellularOrbitSynchronizationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CellularOrbitSynchronizationTasteGate_single_carrier_alignment_round_trip y)))

private theorem CellularOrbitSynchronizationTasteGate_single_carrier_alignment_fields :
    ∀ x y : CellularOrbitSynchronizationUp,
      cellularOrbitSynchronizationFields x =
        cellularOrbitSynchronizationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk O0₁ O1₁ G₁ B₁ Q₁ A₁ T₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk O0₂ O1₂ G₂ B₂ Q₂ A₂ T₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance cellularOrbitSynchronizationBHistCarrier :
    BHistCarrier CellularOrbitSynchronizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cellularOrbitSynchronizationToEventFlow
  fromEventFlow := cellularOrbitSynchronizationFromEventFlow

instance cellularOrbitSynchronizationChapterTasteGate :
    ChapterTasteGate CellularOrbitSynchronizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cellularOrbitSynchronizationFromEventFlow
        (cellularOrbitSynchronizationToEventFlow x) = some x
    exact CellularOrbitSynchronizationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CellularOrbitSynchronizationTasteGate_single_carrier_alignment_injective heq)

instance cellularOrbitSynchronizationFieldFaithful :
    FieldFaithful CellularOrbitSynchronizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cellularOrbitSynchronizationFields
  field_faithful := CellularOrbitSynchronizationTasteGate_single_carrier_alignment_fields

instance cellularOrbitSynchronizationNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CellularOrbitSynchronizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CellularOrbitSynchronizationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CellularOrbitSynchronizationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem CellularOrbitSynchronizationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cellularOrbitSynchronizationDecodeBHist
        (cellularOrbitSynchronizationEncodeBHist h) = h) ∧
      (∀ x : CellularOrbitSynchronizationUp,
        cellularOrbitSynchronizationFromEventFlow
          (cellularOrbitSynchronizationToEventFlow x) = some x) ∧
        (∀ x y : CellularOrbitSynchronizationUp,
          cellularOrbitSynchronizationToEventFlow x =
            cellularOrbitSynchronizationToEventFlow y → x = y) ∧
          cellularOrbitSynchronizationEncodeBHist BHist.Empty =
            ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact CellularOrbitSynchronizationTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact CellularOrbitSynchronizationTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact CellularOrbitSynchronizationTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.CellularOrbitSynchronizationUp
