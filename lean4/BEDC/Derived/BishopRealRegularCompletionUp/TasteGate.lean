import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopRealRegularCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopRealRegularCompletionUp : Type where
  | mk (D S R M E H C P N : BHist) : BishopRealRegularCompletionUp
  deriving DecidableEq

def bishopRealRegularCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopRealRegularCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopRealRegularCompletionEncodeBHist h

def bishopRealRegularCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopRealRegularCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopRealRegularCompletionDecodeBHist tail)

private theorem BishopRealRegularCompletionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, bishopRealRegularCompletionDecodeBHist
      (bishopRealRegularCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopRealRegularCompletionFields : BishopRealRegularCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopRealRegularCompletionUp.mk D S R M E H C P N => [D, S, R, M, E, H, C, P, N]

def bishopRealRegularCompletionToEventFlow : BishopRealRegularCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bishopRealRegularCompletionFields x).map bishopRealRegularCompletionEncodeBHist

private def bishopRealRegularCompletionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopRealRegularCompletionEventAtDefault index rest

def bishopRealRegularCompletionFromEventFlow
    (ef : EventFlow) : Option BishopRealRegularCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopRealRegularCompletionUp.mk
      (bishopRealRegularCompletionDecodeBHist (bishopRealRegularCompletionEventAtDefault 0 ef))
      (bishopRealRegularCompletionDecodeBHist (bishopRealRegularCompletionEventAtDefault 1 ef))
      (bishopRealRegularCompletionDecodeBHist (bishopRealRegularCompletionEventAtDefault 2 ef))
      (bishopRealRegularCompletionDecodeBHist (bishopRealRegularCompletionEventAtDefault 3 ef))
      (bishopRealRegularCompletionDecodeBHist (bishopRealRegularCompletionEventAtDefault 4 ef))
      (bishopRealRegularCompletionDecodeBHist (bishopRealRegularCompletionEventAtDefault 5 ef))
      (bishopRealRegularCompletionDecodeBHist (bishopRealRegularCompletionEventAtDefault 6 ef))
      (bishopRealRegularCompletionDecodeBHist (bishopRealRegularCompletionEventAtDefault 7 ef))
      (bishopRealRegularCompletionDecodeBHist (bishopRealRegularCompletionEventAtDefault 8 ef)))

private theorem BishopRealRegularCompletionTasteGate_single_carrier_alignment_round_trip
    (x : BishopRealRegularCompletionUp) :
    bishopRealRegularCompletionFromEventFlow
      (bishopRealRegularCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk D S R M E H C P N =>
      change
        some
          (BishopRealRegularCompletionUp.mk
            (bishopRealRegularCompletionDecodeBHist
              (bishopRealRegularCompletionEncodeBHist D))
            (bishopRealRegularCompletionDecodeBHist
              (bishopRealRegularCompletionEncodeBHist S))
            (bishopRealRegularCompletionDecodeBHist
              (bishopRealRegularCompletionEncodeBHist R))
            (bishopRealRegularCompletionDecodeBHist
              (bishopRealRegularCompletionEncodeBHist M))
            (bishopRealRegularCompletionDecodeBHist
              (bishopRealRegularCompletionEncodeBHist E))
            (bishopRealRegularCompletionDecodeBHist
              (bishopRealRegularCompletionEncodeBHist H))
            (bishopRealRegularCompletionDecodeBHist
              (bishopRealRegularCompletionEncodeBHist C))
            (bishopRealRegularCompletionDecodeBHist
              (bishopRealRegularCompletionEncodeBHist P))
            (bishopRealRegularCompletionDecodeBHist
              (bishopRealRegularCompletionEncodeBHist N))) =
          some (BishopRealRegularCompletionUp.mk D S R M E H C P N)
      rw [BishopRealRegularCompletionTasteGate_single_carrier_alignment_decode_encode D,
        BishopRealRegularCompletionTasteGate_single_carrier_alignment_decode_encode S,
        BishopRealRegularCompletionTasteGate_single_carrier_alignment_decode_encode R,
        BishopRealRegularCompletionTasteGate_single_carrier_alignment_decode_encode M,
        BishopRealRegularCompletionTasteGate_single_carrier_alignment_decode_encode E,
        BishopRealRegularCompletionTasteGate_single_carrier_alignment_decode_encode H,
        BishopRealRegularCompletionTasteGate_single_carrier_alignment_decode_encode C,
        BishopRealRegularCompletionTasteGate_single_carrier_alignment_decode_encode P,
        BishopRealRegularCompletionTasteGate_single_carrier_alignment_decode_encode N]

private theorem BishopRealRegularCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopRealRegularCompletionUp} :
    bishopRealRegularCompletionToEventFlow x = bishopRealRegularCompletionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopRealRegularCompletionFromEventFlow (bishopRealRegularCompletionToEventFlow x) =
        bishopRealRegularCompletionFromEventFlow (bishopRealRegularCompletionToEventFlow y) :=
    congrArg bishopRealRegularCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopRealRegularCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopRealRegularCompletionTasteGate_single_carrier_alignment_round_trip y)))

private theorem BishopRealRegularCompletionTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : BishopRealRegularCompletionUp,
      bishopRealRegularCompletionFields x = bishopRealRegularCompletionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D1 S1 R1 M1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk D2 S2 R2 M2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance bishopRealRegularCompletionBHistCarrier :
    BHistCarrier BishopRealRegularCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopRealRegularCompletionToEventFlow
  fromEventFlow := bishopRealRegularCompletionFromEventFlow

instance bishopRealRegularCompletionChapterTasteGate :
    ChapterTasteGate BishopRealRegularCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopRealRegularCompletionFromEventFlow
      (bishopRealRegularCompletionToEventFlow x) = some x
    exact BishopRealRegularCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BishopRealRegularCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance bishopRealRegularCompletionFieldFaithful :
    FieldFaithful BishopRealRegularCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopRealRegularCompletionFields
  field_faithful := BishopRealRegularCompletionTasteGate_single_carrier_alignment_fields_faithful

theorem BishopRealRegularCompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist, bishopRealRegularCompletionDecodeBHist
      (bishopRealRegularCompletionEncodeBHist h) = h) ∧
      (∀ x : BishopRealRegularCompletionUp, bishopRealRegularCompletionFromEventFlow
        (bishopRealRegularCompletionToEventFlow x) = some x) ∧
        BHistCarrier.toEventFlow (X := BishopRealRegularCompletionUp)
          (BishopRealRegularCompletionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
          [[], [], [], [], [], [], [], [], []] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨BishopRealRegularCompletionTasteGate_single_carrier_alignment_decode_encode,
      BishopRealRegularCompletionTasteGate_single_carrier_alignment_round_trip,
      rfl⟩

end BEDC.Derived.BishopRealRegularCompletionUp
