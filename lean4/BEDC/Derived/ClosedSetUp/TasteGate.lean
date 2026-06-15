import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosedSetUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosedSetUp : Type where
  | mk (T M S F O B H C P N : BHist) : ClosedSetUp
  deriving DecidableEq

def closedSetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closedSetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closedSetEncodeBHist h

def closedSetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closedSetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closedSetDecodeBHist tail)

private theorem closedSetDecode_encode_bhist :
    ∀ h : BHist, closedSetDecodeBHist (closedSetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def closedSetFields : ClosedSetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedSetUp.mk T M S F O B H C P N => [T, M, S, F, O, B, H, C, P, N]

def closedSetToEventFlow : ClosedSetUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (closedSetFields x).map closedSetEncodeBHist

private def closedSetEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => closedSetEventAtDefault index rest

def closedSetFromEventFlow (ef : EventFlow) : Option ClosedSetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ClosedSetUp.mk
      (closedSetDecodeBHist (closedSetEventAtDefault 0 ef))
      (closedSetDecodeBHist (closedSetEventAtDefault 1 ef))
      (closedSetDecodeBHist (closedSetEventAtDefault 2 ef))
      (closedSetDecodeBHist (closedSetEventAtDefault 3 ef))
      (closedSetDecodeBHist (closedSetEventAtDefault 4 ef))
      (closedSetDecodeBHist (closedSetEventAtDefault 5 ef))
      (closedSetDecodeBHist (closedSetEventAtDefault 6 ef))
      (closedSetDecodeBHist (closedSetEventAtDefault 7 ef))
      (closedSetDecodeBHist (closedSetEventAtDefault 8 ef))
      (closedSetDecodeBHist (closedSetEventAtDefault 9 ef)))

private theorem closedSet_round_trip :
    ∀ x : ClosedSetUp, closedSetFromEventFlow (closedSetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T M S F O B H C P N =>
      change
        some
          (ClosedSetUp.mk
            (closedSetDecodeBHist (closedSetEncodeBHist T))
            (closedSetDecodeBHist (closedSetEncodeBHist M))
            (closedSetDecodeBHist (closedSetEncodeBHist S))
            (closedSetDecodeBHist (closedSetEncodeBHist F))
            (closedSetDecodeBHist (closedSetEncodeBHist O))
            (closedSetDecodeBHist (closedSetEncodeBHist B))
            (closedSetDecodeBHist (closedSetEncodeBHist H))
            (closedSetDecodeBHist (closedSetEncodeBHist C))
            (closedSetDecodeBHist (closedSetEncodeBHist P))
            (closedSetDecodeBHist (closedSetEncodeBHist N))) =
          some (ClosedSetUp.mk T M S F O B H C P N)
      rw [closedSetDecode_encode_bhist T, closedSetDecode_encode_bhist M,
        closedSetDecode_encode_bhist S, closedSetDecode_encode_bhist F,
        closedSetDecode_encode_bhist O, closedSetDecode_encode_bhist B,
        closedSetDecode_encode_bhist H, closedSetDecode_encode_bhist C,
        closedSetDecode_encode_bhist P, closedSetDecode_encode_bhist N]

private theorem closedSetToEventFlow_injective {x y : ClosedSetUp} :
    closedSetToEventFlow x = closedSetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closedSetFromEventFlow (closedSetToEventFlow x) =
        closedSetFromEventFlow (closedSetToEventFlow y) :=
    congrArg closedSetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (closedSet_round_trip x).symm (Eq.trans hread (closedSet_round_trip y)))

private theorem closedSet_fields_faithful :
    ∀ x y : ClosedSetUp, closedSetFields x = closedSetFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T1 M1 S1 F1 O1 B1 H1 C1 P1 N1 =>
      cases y with
      | mk T2 M2 S2 F2 O2 B2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance closedSetBHistCarrier : BHistCarrier ClosedSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedSetToEventFlow
  fromEventFlow := closedSetFromEventFlow

instance closedSetChapterTasteGate : ChapterTasteGate ClosedSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change closedSetFromEventFlow (closedSetToEventFlow x) = some x
    exact closedSet_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (closedSetToEventFlow_injective heq)

instance closedSetFieldFaithful : FieldFaithful ClosedSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := closedSetFields
  field_faithful := closedSet_fields_faithful

def taste_gate : ChapterTasteGate ClosedSetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  closedSetChapterTasteGate

theorem ClosedSetTasteGate_single_carrier_alignment :
    (∀ h : BHist, closedSetDecodeBHist (closedSetEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier ClosedSetUp) ∧ Nonempty (ChapterTasteGate ClosedSetUp) ∧
        closedSetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨closedSetDecode_encode_bhist, ⟨closedSetBHistCarrier⟩,
      ⟨closedSetChapterTasteGate⟩, rfl⟩

end BEDC.Derived.ClosedSetUp.TasteGate
