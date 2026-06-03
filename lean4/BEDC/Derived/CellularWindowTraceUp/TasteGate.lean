import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CellularWindowTraceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CellularWindowTraceUp : Type where
  | mk (w r i o B H C P N : BHist) : CellularWindowTraceUp
  deriving DecidableEq

def cellularWindowTraceEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cellularWindowTraceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cellularWindowTraceEncodeBHist h

def cellularWindowTraceDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cellularWindowTraceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cellularWindowTraceDecodeBHist tail)

private theorem CellularWindowTraceTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      cellularWindowTraceDecodeBHist (cellularWindowTraceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cellularWindowTraceFields :
    CellularWindowTraceUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CellularWindowTraceUp.mk w r i o B H C P N => [w, r, i, o, B, H, C, P, N]

def cellularWindowTraceToEventFlow :
    CellularWindowTraceUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cellularWindowTraceFields x).map cellularWindowTraceEncodeBHist

private def cellularWindowTraceEventAtDefault :
    Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      cellularWindowTraceEventAtDefault index rest

def cellularWindowTraceFromEventFlow
    (ef : EventFlow) : Option CellularWindowTraceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CellularWindowTraceUp.mk
      (cellularWindowTraceDecodeBHist (cellularWindowTraceEventAtDefault 0 ef))
      (cellularWindowTraceDecodeBHist (cellularWindowTraceEventAtDefault 1 ef))
      (cellularWindowTraceDecodeBHist (cellularWindowTraceEventAtDefault 2 ef))
      (cellularWindowTraceDecodeBHist (cellularWindowTraceEventAtDefault 3 ef))
      (cellularWindowTraceDecodeBHist (cellularWindowTraceEventAtDefault 4 ef))
      (cellularWindowTraceDecodeBHist (cellularWindowTraceEventAtDefault 5 ef))
      (cellularWindowTraceDecodeBHist (cellularWindowTraceEventAtDefault 6 ef))
      (cellularWindowTraceDecodeBHist (cellularWindowTraceEventAtDefault 7 ef))
      (cellularWindowTraceDecodeBHist (cellularWindowTraceEventAtDefault 8 ef)))

private theorem CellularWindowTraceTasteGate_single_carrier_alignment_round_trip
    (x : CellularWindowTraceUp) :
    cellularWindowTraceFromEventFlow (cellularWindowTraceToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk w r i o B H C P N =>
      change
        some
          (CellularWindowTraceUp.mk
            (cellularWindowTraceDecodeBHist (cellularWindowTraceEncodeBHist w))
            (cellularWindowTraceDecodeBHist (cellularWindowTraceEncodeBHist r))
            (cellularWindowTraceDecodeBHist (cellularWindowTraceEncodeBHist i))
            (cellularWindowTraceDecodeBHist (cellularWindowTraceEncodeBHist o))
            (cellularWindowTraceDecodeBHist (cellularWindowTraceEncodeBHist B))
            (cellularWindowTraceDecodeBHist (cellularWindowTraceEncodeBHist H))
            (cellularWindowTraceDecodeBHist (cellularWindowTraceEncodeBHist C))
            (cellularWindowTraceDecodeBHist (cellularWindowTraceEncodeBHist P))
            (cellularWindowTraceDecodeBHist (cellularWindowTraceEncodeBHist N))) =
          some (CellularWindowTraceUp.mk w r i o B H C P N)
      rw [CellularWindowTraceTasteGate_single_carrier_alignment_decode_encode w,
        CellularWindowTraceTasteGate_single_carrier_alignment_decode_encode r,
        CellularWindowTraceTasteGate_single_carrier_alignment_decode_encode i,
        CellularWindowTraceTasteGate_single_carrier_alignment_decode_encode o,
        CellularWindowTraceTasteGate_single_carrier_alignment_decode_encode B,
        CellularWindowTraceTasteGate_single_carrier_alignment_decode_encode H,
        CellularWindowTraceTasteGate_single_carrier_alignment_decode_encode C,
        CellularWindowTraceTasteGate_single_carrier_alignment_decode_encode P,
        CellularWindowTraceTasteGate_single_carrier_alignment_decode_encode N]

private theorem CellularWindowTraceTasteGate_single_carrier_alignment_injective
    {x y : CellularWindowTraceUp} :
    cellularWindowTraceToEventFlow x = cellularWindowTraceToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cellularWindowTraceFromEventFlow (cellularWindowTraceToEventFlow x) =
        cellularWindowTraceFromEventFlow (cellularWindowTraceToEventFlow y) :=
    congrArg cellularWindowTraceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CellularWindowTraceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CellularWindowTraceTasteGate_single_carrier_alignment_round_trip y)))

private theorem CellularWindowTraceTasteGate_single_carrier_alignment_fields :
    forall x y : CellularWindowTraceUp,
      cellularWindowTraceFields x = cellularWindowTraceFields y ->
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk w1 r1 i1 o1 B1 H1 C1 P1 N1 =>
      cases y with
      | mk w2 r2 i2 o2 B2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance cellularWindowTraceBHistCarrier :
    BHistCarrier CellularWindowTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cellularWindowTraceToEventFlow
  fromEventFlow := cellularWindowTraceFromEventFlow

instance cellularWindowTraceChapterTasteGate :
    ChapterTasteGate CellularWindowTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cellularWindowTraceFromEventFlow (cellularWindowTraceToEventFlow x) = some x
    exact CellularWindowTraceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CellularWindowTraceTasteGate_single_carrier_alignment_injective heq)

instance cellularWindowTraceFieldFaithful :
    FieldFaithful CellularWindowTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cellularWindowTraceFields
  field_faithful := CellularWindowTraceTasteGate_single_carrier_alignment_fields

instance cellularWindowTraceNontrivial :
    Nontrivial CellularWindowTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CellularWindowTraceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CellularWindowTraceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def CellularWindowTraceTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate CellularWindowTraceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cellularWindowTraceChapterTasteGate

theorem CellularWindowTraceTasteGate_single_carrier_alignment :
    (forall h : BHist,
      cellularWindowTraceDecodeBHist (cellularWindowTraceEncodeBHist h) = h) ∧
      (forall x : CellularWindowTraceUp,
        cellularWindowTraceFromEventFlow (cellularWindowTraceToEventFlow x) =
          some x) ∧
        (forall x y : CellularWindowTraceUp,
          cellularWindowTraceToEventFlow x = cellularWindowTraceToEventFlow y ->
            x = y) ∧
          cellularWindowTraceEncodeBHist BHist.Empty =
            ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact CellularWindowTraceTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact CellularWindowTraceTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact CellularWindowTraceTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.CellularWindowTraceUp
