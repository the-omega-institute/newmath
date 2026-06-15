import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BoundaryPressureLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BoundaryPressureLedgerUp : Type where
  | mk (S O D P A K H C Q N : BHist) : BoundaryPressureLedgerUp
  deriving DecidableEq

def boundaryPressureLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: boundaryPressureLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: boundaryPressureLedgerEncodeBHist h

def boundaryPressureLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (boundaryPressureLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (boundaryPressureLedgerDecodeBHist tail)

private theorem boundaryPressureLedgerDecode_encode_bhist :
    ∀ h : BHist, boundaryPressureLedgerDecodeBHist (boundaryPressureLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def boundaryPressureLedgerFields : BoundaryPressureLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BoundaryPressureLedgerUp.mk S O D P A K H C Q N => [S, O, D, P, A, K, H, C, Q, N]

def boundaryPressureLedgerToEventFlow : BoundaryPressureLedgerUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (boundaryPressureLedgerFields x).map boundaryPressureLedgerEncodeBHist

private def boundaryPressureLedgerEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => boundaryPressureLedgerEventAtDefault index rest

def boundaryPressureLedgerFromEventFlow (ef : EventFlow) : Option BoundaryPressureLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BoundaryPressureLedgerUp.mk
      (boundaryPressureLedgerDecodeBHist (boundaryPressureLedgerEventAtDefault 0 ef))
      (boundaryPressureLedgerDecodeBHist (boundaryPressureLedgerEventAtDefault 1 ef))
      (boundaryPressureLedgerDecodeBHist (boundaryPressureLedgerEventAtDefault 2 ef))
      (boundaryPressureLedgerDecodeBHist (boundaryPressureLedgerEventAtDefault 3 ef))
      (boundaryPressureLedgerDecodeBHist (boundaryPressureLedgerEventAtDefault 4 ef))
      (boundaryPressureLedgerDecodeBHist (boundaryPressureLedgerEventAtDefault 5 ef))
      (boundaryPressureLedgerDecodeBHist (boundaryPressureLedgerEventAtDefault 6 ef))
      (boundaryPressureLedgerDecodeBHist (boundaryPressureLedgerEventAtDefault 7 ef))
      (boundaryPressureLedgerDecodeBHist (boundaryPressureLedgerEventAtDefault 8 ef))
      (boundaryPressureLedgerDecodeBHist (boundaryPressureLedgerEventAtDefault 9 ef)))

private theorem boundaryPressureLedger_round_trip :
    ∀ x : BoundaryPressureLedgerUp,
      boundaryPressureLedgerFromEventFlow (boundaryPressureLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S O D P A K H C Q N =>
      change
        some
          (BoundaryPressureLedgerUp.mk
            (boundaryPressureLedgerDecodeBHist (boundaryPressureLedgerEncodeBHist S))
            (boundaryPressureLedgerDecodeBHist (boundaryPressureLedgerEncodeBHist O))
            (boundaryPressureLedgerDecodeBHist (boundaryPressureLedgerEncodeBHist D))
            (boundaryPressureLedgerDecodeBHist (boundaryPressureLedgerEncodeBHist P))
            (boundaryPressureLedgerDecodeBHist (boundaryPressureLedgerEncodeBHist A))
            (boundaryPressureLedgerDecodeBHist (boundaryPressureLedgerEncodeBHist K))
            (boundaryPressureLedgerDecodeBHist (boundaryPressureLedgerEncodeBHist H))
            (boundaryPressureLedgerDecodeBHist (boundaryPressureLedgerEncodeBHist C))
            (boundaryPressureLedgerDecodeBHist (boundaryPressureLedgerEncodeBHist Q))
            (boundaryPressureLedgerDecodeBHist (boundaryPressureLedgerEncodeBHist N))) =
          some (BoundaryPressureLedgerUp.mk S O D P A K H C Q N)
      rw [boundaryPressureLedgerDecode_encode_bhist S, boundaryPressureLedgerDecode_encode_bhist O,
        boundaryPressureLedgerDecode_encode_bhist D, boundaryPressureLedgerDecode_encode_bhist P,
        boundaryPressureLedgerDecode_encode_bhist A, boundaryPressureLedgerDecode_encode_bhist K,
        boundaryPressureLedgerDecode_encode_bhist H, boundaryPressureLedgerDecode_encode_bhist C,
        boundaryPressureLedgerDecode_encode_bhist Q, boundaryPressureLedgerDecode_encode_bhist N]

private theorem boundaryPressureLedgerToEventFlow_injective {x y : BoundaryPressureLedgerUp} :
    boundaryPressureLedgerToEventFlow x = boundaryPressureLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      boundaryPressureLedgerFromEventFlow (boundaryPressureLedgerToEventFlow x) =
        boundaryPressureLedgerFromEventFlow (boundaryPressureLedgerToEventFlow y) :=
    congrArg boundaryPressureLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (boundaryPressureLedger_round_trip x).symm
      (Eq.trans hread (boundaryPressureLedger_round_trip y)))

private theorem boundaryPressureLedger_fields_faithful :
    ∀ x y : BoundaryPressureLedgerUp, boundaryPressureLedgerFields x = boundaryPressureLedgerFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 O1 D1 P1 A1 K1 H1 C1 Q1 N1 =>
      cases y with
      | mk S2 O2 D2 P2 A2 K2 H2 C2 Q2 N2 =>
          cases hfields
          rfl

instance boundaryPressureLedgerBHistCarrier : BHistCarrier BoundaryPressureLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := boundaryPressureLedgerToEventFlow
  fromEventFlow := boundaryPressureLedgerFromEventFlow

instance boundaryPressureLedgerChapterTasteGate : ChapterTasteGate BoundaryPressureLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change boundaryPressureLedgerFromEventFlow (boundaryPressureLedgerToEventFlow x) = some x
    exact boundaryPressureLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (boundaryPressureLedgerToEventFlow_injective heq)

instance boundaryPressureLedgerFieldFaithful : FieldFaithful BoundaryPressureLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := boundaryPressureLedgerFields
  field_faithful := boundaryPressureLedger_fields_faithful

instance boundaryPressureLedgerNontrivial : Nontrivial BoundaryPressureLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BoundaryPressureLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BoundaryPressureLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BoundaryPressureLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  boundaryPressureLedgerChapterTasteGate

def taste_gate_witness : FieldFaithful BoundaryPressureLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  boundaryPressureLedgerFieldFaithful

theorem BoundaryPressureLedgerTasteGate_single_carrier_alignment :
    (forall h : BHist, boundaryPressureLedgerDecodeBHist (boundaryPressureLedgerEncodeBHist h) = h) /\
      (forall x : BoundaryPressureLedgerUp,
        boundaryPressureLedgerFromEventFlow (boundaryPressureLedgerToEventFlow x) = some x) /\
        (forall x y : BoundaryPressureLedgerUp,
          boundaryPressureLedgerToEventFlow x = boundaryPressureLedgerToEventFlow y -> x = y) /\
          boundaryPressureLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨boundaryPressureLedgerDecode_encode_bhist, boundaryPressureLedger_round_trip,
      by
        intro x y heq
        exact boundaryPressureLedgerToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.BoundaryPressureLedgerUp
