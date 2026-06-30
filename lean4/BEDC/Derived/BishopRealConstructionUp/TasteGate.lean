import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopRealConstructionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopRealConstructionUp : Type where
  | mk (D S Q R M E H C P N : BHist) : BishopRealConstructionUp
  deriving DecidableEq

def bishopRealConstructionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopRealConstructionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopRealConstructionEncodeBHist h

def bishopRealConstructionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopRealConstructionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopRealConstructionDecodeBHist tail)

private theorem BishopRealConstructionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, bishopRealConstructionDecodeBHist
      (bishopRealConstructionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopRealConstructionFields : BishopRealConstructionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopRealConstructionUp.mk D S Q R M E H C P N => [D, S, Q, R, M, E, H, C, P, N]

def bishopRealConstructionToEventFlow : BishopRealConstructionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bishopRealConstructionFields x).map bishopRealConstructionEncodeBHist

private def bishopRealConstructionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopRealConstructionEventAtDefault index rest

def bishopRealConstructionFromEventFlow (ef : EventFlow) : Option BishopRealConstructionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopRealConstructionUp.mk
      (bishopRealConstructionDecodeBHist (bishopRealConstructionEventAtDefault 0 ef))
      (bishopRealConstructionDecodeBHist (bishopRealConstructionEventAtDefault 1 ef))
      (bishopRealConstructionDecodeBHist (bishopRealConstructionEventAtDefault 2 ef))
      (bishopRealConstructionDecodeBHist (bishopRealConstructionEventAtDefault 3 ef))
      (bishopRealConstructionDecodeBHist (bishopRealConstructionEventAtDefault 4 ef))
      (bishopRealConstructionDecodeBHist (bishopRealConstructionEventAtDefault 5 ef))
      (bishopRealConstructionDecodeBHist (bishopRealConstructionEventAtDefault 6 ef))
      (bishopRealConstructionDecodeBHist (bishopRealConstructionEventAtDefault 7 ef))
      (bishopRealConstructionDecodeBHist (bishopRealConstructionEventAtDefault 8 ef))
      (bishopRealConstructionDecodeBHist (bishopRealConstructionEventAtDefault 9 ef)))

private theorem BishopRealConstructionTasteGate_single_carrier_alignment_round_trip
    (x : BishopRealConstructionUp) :
    bishopRealConstructionFromEventFlow (bishopRealConstructionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk D S Q R M E H C P N =>
      change
        some
          (BishopRealConstructionUp.mk
            (bishopRealConstructionDecodeBHist (bishopRealConstructionEncodeBHist D))
            (bishopRealConstructionDecodeBHist (bishopRealConstructionEncodeBHist S))
            (bishopRealConstructionDecodeBHist (bishopRealConstructionEncodeBHist Q))
            (bishopRealConstructionDecodeBHist (bishopRealConstructionEncodeBHist R))
            (bishopRealConstructionDecodeBHist (bishopRealConstructionEncodeBHist M))
            (bishopRealConstructionDecodeBHist (bishopRealConstructionEncodeBHist E))
            (bishopRealConstructionDecodeBHist (bishopRealConstructionEncodeBHist H))
            (bishopRealConstructionDecodeBHist (bishopRealConstructionEncodeBHist C))
            (bishopRealConstructionDecodeBHist (bishopRealConstructionEncodeBHist P))
            (bishopRealConstructionDecodeBHist (bishopRealConstructionEncodeBHist N))) =
          some (BishopRealConstructionUp.mk D S Q R M E H C P N)
      rw [BishopRealConstructionTasteGate_single_carrier_alignment_decode_encode D,
        BishopRealConstructionTasteGate_single_carrier_alignment_decode_encode S,
        BishopRealConstructionTasteGate_single_carrier_alignment_decode_encode Q,
        BishopRealConstructionTasteGate_single_carrier_alignment_decode_encode R,
        BishopRealConstructionTasteGate_single_carrier_alignment_decode_encode M,
        BishopRealConstructionTasteGate_single_carrier_alignment_decode_encode E,
        BishopRealConstructionTasteGate_single_carrier_alignment_decode_encode H,
        BishopRealConstructionTasteGate_single_carrier_alignment_decode_encode C,
        BishopRealConstructionTasteGate_single_carrier_alignment_decode_encode P,
        BishopRealConstructionTasteGate_single_carrier_alignment_decode_encode N]

private theorem BishopRealConstructionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopRealConstructionUp} :
    bishopRealConstructionToEventFlow x = bishopRealConstructionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopRealConstructionFromEventFlow (bishopRealConstructionToEventFlow x) =
        bishopRealConstructionFromEventFlow (bishopRealConstructionToEventFlow y) :=
    congrArg bishopRealConstructionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BishopRealConstructionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopRealConstructionTasteGate_single_carrier_alignment_round_trip y)))

private theorem BishopRealConstructionTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : BishopRealConstructionUp, bishopRealConstructionFields x =
      bishopRealConstructionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D1 S1 Q1 R1 M1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk D2 S2 Q2 R2 M2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance bishopRealConstructionBHistCarrier : BHistCarrier BishopRealConstructionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopRealConstructionToEventFlow
  fromEventFlow := bishopRealConstructionFromEventFlow

instance bishopRealConstructionChapterTasteGate : ChapterTasteGate BishopRealConstructionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopRealConstructionFromEventFlow
      (bishopRealConstructionToEventFlow x) = some x
    exact BishopRealConstructionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BishopRealConstructionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance bishopRealConstructionFieldFaithful : FieldFaithful BishopRealConstructionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopRealConstructionFields
  field_faithful := BishopRealConstructionTasteGate_single_carrier_alignment_fields_faithful

theorem BishopRealConstructionTasteGate_single_carrier_alignment :
    (∀ h : BHist, bishopRealConstructionDecodeBHist
      (bishopRealConstructionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier BishopRealConstructionUp) ∧
        Nonempty (ChapterTasteGate BishopRealConstructionUp) ∧
          bishopRealConstructionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨BishopRealConstructionTasteGate_single_carrier_alignment_decode_encode,
      ⟨bishopRealConstructionBHistCarrier⟩,
      ⟨bishopRealConstructionChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.BishopRealConstructionUp
