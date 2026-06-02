import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopCauchyApproximationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopCauchyApproximationUp : Type where
  | mk (R precision W D V E H C P N : BHist) : BishopCauchyApproximationUp
  deriving DecidableEq

def bishopCauchyApproximationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopCauchyApproximationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopCauchyApproximationEncodeBHist h

def bishopCauchyApproximationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopCauchyApproximationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopCauchyApproximationDecodeBHist tail)

private theorem BishopCauchyApproximationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      bishopCauchyApproximationDecodeBHist
        (bishopCauchyApproximationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopCauchyApproximationFields : BishopCauchyApproximationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopCauchyApproximationUp.mk R precision W D V E H C P N =>
      [R, precision, W, D, V, E, H, C, P, N]

def bishopCauchyApproximationToEventFlow : BishopCauchyApproximationUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (bishopCauchyApproximationFields x).map bishopCauchyApproximationEncodeBHist

private def bishopCauchyApproximationEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopCauchyApproximationEventAtDefault index rest

def bishopCauchyApproximationFromEventFlow
    (ef : EventFlow) : Option BishopCauchyApproximationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopCauchyApproximationUp.mk
      (bishopCauchyApproximationDecodeBHist
        (bishopCauchyApproximationEventAtDefault 0 ef))
      (bishopCauchyApproximationDecodeBHist
        (bishopCauchyApproximationEventAtDefault 1 ef))
      (bishopCauchyApproximationDecodeBHist
        (bishopCauchyApproximationEventAtDefault 2 ef))
      (bishopCauchyApproximationDecodeBHist
        (bishopCauchyApproximationEventAtDefault 3 ef))
      (bishopCauchyApproximationDecodeBHist
        (bishopCauchyApproximationEventAtDefault 4 ef))
      (bishopCauchyApproximationDecodeBHist
        (bishopCauchyApproximationEventAtDefault 5 ef))
      (bishopCauchyApproximationDecodeBHist
        (bishopCauchyApproximationEventAtDefault 6 ef))
      (bishopCauchyApproximationDecodeBHist
        (bishopCauchyApproximationEventAtDefault 7 ef))
      (bishopCauchyApproximationDecodeBHist
        (bishopCauchyApproximationEventAtDefault 8 ef))
      (bishopCauchyApproximationDecodeBHist
        (bishopCauchyApproximationEventAtDefault 9 ef)))

private theorem BishopCauchyApproximationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BishopCauchyApproximationUp,
      bishopCauchyApproximationFromEventFlow
        (bishopCauchyApproximationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R precision W D V E H C P N =>
      change
        some
          (BishopCauchyApproximationUp.mk
            (bishopCauchyApproximationDecodeBHist
              (bishopCauchyApproximationEncodeBHist R))
            (bishopCauchyApproximationDecodeBHist
              (bishopCauchyApproximationEncodeBHist precision))
            (bishopCauchyApproximationDecodeBHist
              (bishopCauchyApproximationEncodeBHist W))
            (bishopCauchyApproximationDecodeBHist
              (bishopCauchyApproximationEncodeBHist D))
            (bishopCauchyApproximationDecodeBHist
              (bishopCauchyApproximationEncodeBHist V))
            (bishopCauchyApproximationDecodeBHist
              (bishopCauchyApproximationEncodeBHist E))
            (bishopCauchyApproximationDecodeBHist
              (bishopCauchyApproximationEncodeBHist H))
            (bishopCauchyApproximationDecodeBHist
              (bishopCauchyApproximationEncodeBHist C))
            (bishopCauchyApproximationDecodeBHist
              (bishopCauchyApproximationEncodeBHist P))
            (bishopCauchyApproximationDecodeBHist
              (bishopCauchyApproximationEncodeBHist N))) =
          some (BishopCauchyApproximationUp.mk R precision W D V E H C P N)
      rw [BishopCauchyApproximationTasteGate_single_carrier_alignment_decode R,
        BishopCauchyApproximationTasteGate_single_carrier_alignment_decode precision,
        BishopCauchyApproximationTasteGate_single_carrier_alignment_decode W,
        BishopCauchyApproximationTasteGate_single_carrier_alignment_decode D,
        BishopCauchyApproximationTasteGate_single_carrier_alignment_decode V,
        BishopCauchyApproximationTasteGate_single_carrier_alignment_decode E,
        BishopCauchyApproximationTasteGate_single_carrier_alignment_decode H,
        BishopCauchyApproximationTasteGate_single_carrier_alignment_decode C,
        BishopCauchyApproximationTasteGate_single_carrier_alignment_decode P,
        BishopCauchyApproximationTasteGate_single_carrier_alignment_decode N]

private theorem BishopCauchyApproximationTasteGate_single_carrier_alignment_injective
    {x y : BishopCauchyApproximationUp} :
    bishopCauchyApproximationToEventFlow x = bishopCauchyApproximationToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopCauchyApproximationFromEventFlow (bishopCauchyApproximationToEventFlow x) =
        bishopCauchyApproximationFromEventFlow (bishopCauchyApproximationToEventFlow y) :=
    congrArg bishopCauchyApproximationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopCauchyApproximationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopCauchyApproximationTasteGate_single_carrier_alignment_round_trip y)))

private theorem BishopCauchyApproximationTasteGate_single_carrier_alignment_fields :
    ∀ x y : BishopCauchyApproximationUp,
      bishopCauchyApproximationFields x = bishopCauchyApproximationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R1 precision1 W1 D1 V1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk R2 precision2 W2 D2 V2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance bishopCauchyApproximationBHistCarrier :
    BHistCarrier BishopCauchyApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopCauchyApproximationToEventFlow
  fromEventFlow := bishopCauchyApproximationFromEventFlow

instance bishopCauchyApproximationChapterTasteGate :
    ChapterTasteGate BishopCauchyApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopCauchyApproximationFromEventFlow (bishopCauchyApproximationToEventFlow x) =
        some x
    exact BishopCauchyApproximationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BishopCauchyApproximationTasteGate_single_carrier_alignment_injective heq)

instance bishopCauchyApproximationFieldFaithful :
    FieldFaithful BishopCauchyApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopCauchyApproximationFields
  field_faithful := BishopCauchyApproximationTasteGate_single_carrier_alignment_fields

def taste_gate : ChapterTasteGate BishopCauchyApproximationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopCauchyApproximationChapterTasteGate

theorem BishopCauchyApproximationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      bishopCauchyApproximationDecodeBHist
        (bishopCauchyApproximationEncodeBHist h) = h) ∧
      (∀ x : BishopCauchyApproximationUp,
        bishopCauchyApproximationFromEventFlow
          (bishopCauchyApproximationToEventFlow x) = some x) ∧
        (∀ x y : BishopCauchyApproximationUp,
          bishopCauchyApproximationToEventFlow x =
            bishopCauchyApproximationToEventFlow y -> x = y) ∧
          bishopCauchyApproximationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨BishopCauchyApproximationTasteGate_single_carrier_alignment_decode,
      BishopCauchyApproximationTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        BishopCauchyApproximationTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.BishopCauchyApproximationUp
