import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CellularSubstrateObservationBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CellularSubstrateObservationBoundaryUp : Type where
  | mk (R W M B A H C P N : BHist) : CellularSubstrateObservationBoundaryUp
  deriving DecidableEq

def cellularSubstrateObservationBoundaryEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cellularSubstrateObservationBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cellularSubstrateObservationBoundaryEncodeBHist h

def cellularSubstrateObservationBoundaryDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cellularSubstrateObservationBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cellularSubstrateObservationBoundaryDecodeBHist tail)

private theorem cellularSubstrateObservationBoundary_decode_encode :
    forall h : BHist,
      cellularSubstrateObservationBoundaryDecodeBHist
        (cellularSubstrateObservationBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cellularSubstrateObservationBoundaryFields :
    CellularSubstrateObservationBoundaryUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CellularSubstrateObservationBoundaryUp.mk R W M B A H C P N =>
      [R, W, M, B, A, H, C, P, N]

def cellularSubstrateObservationBoundaryToEventFlow :
    CellularSubstrateObservationBoundaryUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (cellularSubstrateObservationBoundaryFields x).map
        cellularSubstrateObservationBoundaryEncodeBHist

private def cellularSubstrateObservationBoundaryEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cellularSubstrateObservationBoundaryEventAt index rest

def cellularSubstrateObservationBoundaryFromEventFlow
    (ef : EventFlow) : Option CellularSubstrateObservationBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CellularSubstrateObservationBoundaryUp.mk
      (cellularSubstrateObservationBoundaryDecodeBHist
        (cellularSubstrateObservationBoundaryEventAt 0 ef))
      (cellularSubstrateObservationBoundaryDecodeBHist
        (cellularSubstrateObservationBoundaryEventAt 1 ef))
      (cellularSubstrateObservationBoundaryDecodeBHist
        (cellularSubstrateObservationBoundaryEventAt 2 ef))
      (cellularSubstrateObservationBoundaryDecodeBHist
        (cellularSubstrateObservationBoundaryEventAt 3 ef))
      (cellularSubstrateObservationBoundaryDecodeBHist
        (cellularSubstrateObservationBoundaryEventAt 4 ef))
      (cellularSubstrateObservationBoundaryDecodeBHist
        (cellularSubstrateObservationBoundaryEventAt 5 ef))
      (cellularSubstrateObservationBoundaryDecodeBHist
        (cellularSubstrateObservationBoundaryEventAt 6 ef))
      (cellularSubstrateObservationBoundaryDecodeBHist
        (cellularSubstrateObservationBoundaryEventAt 7 ef))
      (cellularSubstrateObservationBoundaryDecodeBHist
        (cellularSubstrateObservationBoundaryEventAt 8 ef)))

private theorem cellularSubstrateObservationBoundary_round_trip
    (x : CellularSubstrateObservationBoundaryUp) :
    cellularSubstrateObservationBoundaryFromEventFlow
        (cellularSubstrateObservationBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk R W M B A H C P N =>
      change
        some
          (CellularSubstrateObservationBoundaryUp.mk
            (cellularSubstrateObservationBoundaryDecodeBHist
              (cellularSubstrateObservationBoundaryEncodeBHist R))
            (cellularSubstrateObservationBoundaryDecodeBHist
              (cellularSubstrateObservationBoundaryEncodeBHist W))
            (cellularSubstrateObservationBoundaryDecodeBHist
              (cellularSubstrateObservationBoundaryEncodeBHist M))
            (cellularSubstrateObservationBoundaryDecodeBHist
              (cellularSubstrateObservationBoundaryEncodeBHist B))
            (cellularSubstrateObservationBoundaryDecodeBHist
              (cellularSubstrateObservationBoundaryEncodeBHist A))
            (cellularSubstrateObservationBoundaryDecodeBHist
              (cellularSubstrateObservationBoundaryEncodeBHist H))
            (cellularSubstrateObservationBoundaryDecodeBHist
              (cellularSubstrateObservationBoundaryEncodeBHist C))
            (cellularSubstrateObservationBoundaryDecodeBHist
              (cellularSubstrateObservationBoundaryEncodeBHist P))
            (cellularSubstrateObservationBoundaryDecodeBHist
              (cellularSubstrateObservationBoundaryEncodeBHist N))) =
          some (CellularSubstrateObservationBoundaryUp.mk R W M B A H C P N)
      rw [cellularSubstrateObservationBoundary_decode_encode R,
        cellularSubstrateObservationBoundary_decode_encode W,
        cellularSubstrateObservationBoundary_decode_encode M,
        cellularSubstrateObservationBoundary_decode_encode B,
        cellularSubstrateObservationBoundary_decode_encode A,
        cellularSubstrateObservationBoundary_decode_encode H,
        cellularSubstrateObservationBoundary_decode_encode C,
        cellularSubstrateObservationBoundary_decode_encode P,
        cellularSubstrateObservationBoundary_decode_encode N]

private theorem cellularSubstrateObservationBoundaryToEventFlow_injective
    {x y : CellularSubstrateObservationBoundaryUp} :
    cellularSubstrateObservationBoundaryToEventFlow x =
        cellularSubstrateObservationBoundaryToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cellularSubstrateObservationBoundaryFromEventFlow
          (cellularSubstrateObservationBoundaryToEventFlow x) =
        cellularSubstrateObservationBoundaryFromEventFlow
          (cellularSubstrateObservationBoundaryToEventFlow y) :=
    congrArg cellularSubstrateObservationBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cellularSubstrateObservationBoundary_round_trip x).symm
      (Eq.trans hread (cellularSubstrateObservationBoundary_round_trip y)))

private theorem cellularSubstrateObservationBoundaryFields_faithful :
    forall x y : CellularSubstrateObservationBoundaryUp,
      cellularSubstrateObservationBoundaryFields x =
          cellularSubstrateObservationBoundaryFields y ->
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R1 W1 M1 B1 A1 H1 C1 P1 N1 =>
      cases y with
      | mk R2 W2 M2 B2 A2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance cellularSubstrateObservationBoundaryBHistCarrier :
    BHistCarrier CellularSubstrateObservationBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cellularSubstrateObservationBoundaryToEventFlow
  fromEventFlow := cellularSubstrateObservationBoundaryFromEventFlow

instance cellularSubstrateObservationBoundaryChapterTasteGate :
    ChapterTasteGate CellularSubstrateObservationBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cellularSubstrateObservationBoundaryFromEventFlow
          (cellularSubstrateObservationBoundaryToEventFlow x) = some x
    exact cellularSubstrateObservationBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cellularSubstrateObservationBoundaryToEventFlow_injective heq)

instance cellularSubstrateObservationBoundaryFieldFaithful :
    FieldFaithful CellularSubstrateObservationBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cellularSubstrateObservationBoundaryFields
  field_faithful := cellularSubstrateObservationBoundaryFields_faithful

instance cellularSubstrateObservationBoundaryNontrivial :
    Nontrivial CellularSubstrateObservationBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CellularSubstrateObservationBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CellularSubstrateObservationBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CellularSubstrateObservationBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cellularSubstrateObservationBoundaryChapterTasteGate

theorem CellularSubstrateObservationBoundaryTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CellularSubstrateObservationBoundaryUp) ∧
      Nonempty (FieldFaithful CellularSubstrateObservationBoundaryUp) ∧
        Nonempty (Nontrivial CellularSubstrateObservationBoundaryUp) ∧
          (forall h : BHist,
            cellularSubstrateObservationBoundaryDecodeBHist
              (cellularSubstrateObservationBoundaryEncodeBHist h) = h) ∧
            (forall x : CellularSubstrateObservationBoundaryUp,
              cellularSubstrateObservationBoundaryFromEventFlow
                  (cellularSubstrateObservationBoundaryToEventFlow x) = some x) ∧
              (forall x y : CellularSubstrateObservationBoundaryUp,
                cellularSubstrateObservationBoundaryToEventFlow x =
                    cellularSubstrateObservationBoundaryToEventFlow y ->
                  x = y) ∧
                cellularSubstrateObservationBoundaryEncodeBHist BHist.Empty =
                  ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨cellularSubstrateObservationBoundaryChapterTasteGate⟩,
      ⟨cellularSubstrateObservationBoundaryFieldFaithful⟩,
      ⟨cellularSubstrateObservationBoundaryNontrivial⟩,
      cellularSubstrateObservationBoundary_decode_encode,
      cellularSubstrateObservationBoundary_round_trip,
      (fun _ _ heq => cellularSubstrateObservationBoundaryToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CellularSubstrateObservationBoundaryUp
