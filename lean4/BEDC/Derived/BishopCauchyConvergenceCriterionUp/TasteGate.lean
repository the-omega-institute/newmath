import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopCauchyConvergenceCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopCauchyConvergenceCriterionUp : Type where
  | mk (S Q D R E H C P N : BHist) : BishopCauchyConvergenceCriterionUp
  deriving DecidableEq

def bishopCauchyConvergenceCriterionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopCauchyConvergenceCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopCauchyConvergenceCriterionEncodeBHist h

def bishopCauchyConvergenceCriterionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopCauchyConvergenceCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopCauchyConvergenceCriterionDecodeBHist tail)

private theorem BishopCauchyConvergenceCriterionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      bishopCauchyConvergenceCriterionDecodeBHist
        (bishopCauchyConvergenceCriterionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopCauchyConvergenceCriterionFields :
    BishopCauchyConvergenceCriterionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopCauchyConvergenceCriterionUp.mk S Q D R E H C P N =>
      [S, Q, D, R, E, H, C, P, N]

def bishopCauchyConvergenceCriterionToEventFlow :
    BishopCauchyConvergenceCriterionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (bishopCauchyConvergenceCriterionFields x).map
    bishopCauchyConvergenceCriterionEncodeBHist

private def bishopCauchyConvergenceCriterionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      bishopCauchyConvergenceCriterionEventAtDefault index rest

def bishopCauchyConvergenceCriterionFromEventFlow
    (ef : EventFlow) : Option BishopCauchyConvergenceCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopCauchyConvergenceCriterionUp.mk
      (bishopCauchyConvergenceCriterionDecodeBHist
        (bishopCauchyConvergenceCriterionEventAtDefault 0 ef))
      (bishopCauchyConvergenceCriterionDecodeBHist
        (bishopCauchyConvergenceCriterionEventAtDefault 1 ef))
      (bishopCauchyConvergenceCriterionDecodeBHist
        (bishopCauchyConvergenceCriterionEventAtDefault 2 ef))
      (bishopCauchyConvergenceCriterionDecodeBHist
        (bishopCauchyConvergenceCriterionEventAtDefault 3 ef))
      (bishopCauchyConvergenceCriterionDecodeBHist
        (bishopCauchyConvergenceCriterionEventAtDefault 4 ef))
      (bishopCauchyConvergenceCriterionDecodeBHist
        (bishopCauchyConvergenceCriterionEventAtDefault 5 ef))
      (bishopCauchyConvergenceCriterionDecodeBHist
        (bishopCauchyConvergenceCriterionEventAtDefault 6 ef))
      (bishopCauchyConvergenceCriterionDecodeBHist
        (bishopCauchyConvergenceCriterionEventAtDefault 7 ef))
      (bishopCauchyConvergenceCriterionDecodeBHist
        (bishopCauchyConvergenceCriterionEventAtDefault 8 ef)))

private theorem BishopCauchyConvergenceCriterionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BishopCauchyConvergenceCriterionUp,
      bishopCauchyConvergenceCriterionFromEventFlow
        (bishopCauchyConvergenceCriterionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk S Q D R E H C P N =>
      change
        some
          (BishopCauchyConvergenceCriterionUp.mk
            (bishopCauchyConvergenceCriterionDecodeBHist
              (bishopCauchyConvergenceCriterionEncodeBHist S))
            (bishopCauchyConvergenceCriterionDecodeBHist
              (bishopCauchyConvergenceCriterionEncodeBHist Q))
            (bishopCauchyConvergenceCriterionDecodeBHist
              (bishopCauchyConvergenceCriterionEncodeBHist D))
            (bishopCauchyConvergenceCriterionDecodeBHist
              (bishopCauchyConvergenceCriterionEncodeBHist R))
            (bishopCauchyConvergenceCriterionDecodeBHist
              (bishopCauchyConvergenceCriterionEncodeBHist E))
            (bishopCauchyConvergenceCriterionDecodeBHist
              (bishopCauchyConvergenceCriterionEncodeBHist H))
            (bishopCauchyConvergenceCriterionDecodeBHist
              (bishopCauchyConvergenceCriterionEncodeBHist C))
            (bishopCauchyConvergenceCriterionDecodeBHist
              (bishopCauchyConvergenceCriterionEncodeBHist P))
            (bishopCauchyConvergenceCriterionDecodeBHist
              (bishopCauchyConvergenceCriterionEncodeBHist N))) =
          some (BishopCauchyConvergenceCriterionUp.mk S Q D R E H C P N)
      rw [BishopCauchyConvergenceCriterionTasteGate_single_carrier_alignment_decode S,
        BishopCauchyConvergenceCriterionTasteGate_single_carrier_alignment_decode Q,
        BishopCauchyConvergenceCriterionTasteGate_single_carrier_alignment_decode D,
        BishopCauchyConvergenceCriterionTasteGate_single_carrier_alignment_decode R,
        BishopCauchyConvergenceCriterionTasteGate_single_carrier_alignment_decode E,
        BishopCauchyConvergenceCriterionTasteGate_single_carrier_alignment_decode H,
        BishopCauchyConvergenceCriterionTasteGate_single_carrier_alignment_decode C,
        BishopCauchyConvergenceCriterionTasteGate_single_carrier_alignment_decode P,
        BishopCauchyConvergenceCriterionTasteGate_single_carrier_alignment_decode N]

private theorem BishopCauchyConvergenceCriterionTasteGate_single_carrier_alignment_injective
    {x y : BishopCauchyConvergenceCriterionUp} :
    bishopCauchyConvergenceCriterionToEventFlow x =
      bishopCauchyConvergenceCriterionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopCauchyConvergenceCriterionFromEventFlow
          (bishopCauchyConvergenceCriterionToEventFlow x) =
        bishopCauchyConvergenceCriterionFromEventFlow
          (bishopCauchyConvergenceCriterionToEventFlow y) :=
    congrArg bishopCauchyConvergenceCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopCauchyConvergenceCriterionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopCauchyConvergenceCriterionTasteGate_single_carrier_alignment_round_trip y)))

private theorem BishopCauchyConvergenceCriterionTasteGate_single_carrier_alignment_fields :
    ∀ x y : BishopCauchyConvergenceCriterionUp,
      bishopCauchyConvergenceCriterionFields x =
        bishopCauchyConvergenceCriterionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 Q1 D1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 Q2 D2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance bishopCauchyConvergenceCriterionBHistCarrier :
    BHistCarrier BishopCauchyConvergenceCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopCauchyConvergenceCriterionToEventFlow
  fromEventFlow := bishopCauchyConvergenceCriterionFromEventFlow

instance bishopCauchyConvergenceCriterionChapterTasteGate :
    ChapterTasteGate BishopCauchyConvergenceCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopCauchyConvergenceCriterionFromEventFlow
        (bishopCauchyConvergenceCriterionToEventFlow x) = some x
    exact BishopCauchyConvergenceCriterionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BishopCauchyConvergenceCriterionTasteGate_single_carrier_alignment_injective heq)

instance bishopCauchyConvergenceCriterionFieldFaithful :
    FieldFaithful BishopCauchyConvergenceCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopCauchyConvergenceCriterionFields
  field_faithful :=
    BishopCauchyConvergenceCriterionTasteGate_single_carrier_alignment_fields

def taste_gate : ChapterTasteGate BishopCauchyConvergenceCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopCauchyConvergenceCriterionChapterTasteGate

theorem BishopCauchyConvergenceCriterionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      bishopCauchyConvergenceCriterionDecodeBHist
        (bishopCauchyConvergenceCriterionEncodeBHist h) = h) ∧
      (∀ x : BishopCauchyConvergenceCriterionUp,
        bishopCauchyConvergenceCriterionFromEventFlow
          (bishopCauchyConvergenceCriterionToEventFlow x) = some x) ∧
        (∀ x y : BishopCauchyConvergenceCriterionUp,
          bishopCauchyConvergenceCriterionToEventFlow x =
            bishopCauchyConvergenceCriterionToEventFlow y → x = y) ∧
          bishopCauchyConvergenceCriterionEncodeBHist BHist.Empty =
            ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨BishopCauchyConvergenceCriterionTasteGate_single_carrier_alignment_decode,
      BishopCauchyConvergenceCriterionTasteGate_single_carrier_alignment_round_trip,
      fun _x _y heq =>
        BishopCauchyConvergenceCriterionTasteGate_single_carrier_alignment_injective heq,
      rfl⟩

end BEDC.Derived.BishopCauchyConvergenceCriterionUp
