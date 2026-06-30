import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopModulusConvergenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopModulusConvergenceUp : Type where
  | mk (S D M R E H C P N : BHist) : BishopModulusConvergenceUp
  deriving DecidableEq

def bishopModulusConvergenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopModulusConvergenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopModulusConvergenceEncodeBHist h

def bishopModulusConvergenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopModulusConvergenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopModulusConvergenceDecodeBHist tail)

private theorem BishopModulusConvergenceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      bishopModulusConvergenceDecodeBHist
        (bishopModulusConvergenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopModulusConvergenceFields :
    BishopModulusConvergenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopModulusConvergenceUp.mk S D M R E H C P N =>
      [S, D, M, R, E, H, C, P, N]

def bishopModulusConvergenceToEventFlow :
    BishopModulusConvergenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bishopModulusConvergenceFields x).map bishopModulusConvergenceEncodeBHist

private def bishopModulusConvergenceEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      bishopModulusConvergenceEventAtDefault index rest

def bishopModulusConvergenceFromEventFlow
    (ef : EventFlow) : Option BishopModulusConvergenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopModulusConvergenceUp.mk
      (bishopModulusConvergenceDecodeBHist
        (bishopModulusConvergenceEventAtDefault 0 ef))
      (bishopModulusConvergenceDecodeBHist
        (bishopModulusConvergenceEventAtDefault 1 ef))
      (bishopModulusConvergenceDecodeBHist
        (bishopModulusConvergenceEventAtDefault 2 ef))
      (bishopModulusConvergenceDecodeBHist
        (bishopModulusConvergenceEventAtDefault 3 ef))
      (bishopModulusConvergenceDecodeBHist
        (bishopModulusConvergenceEventAtDefault 4 ef))
      (bishopModulusConvergenceDecodeBHist
        (bishopModulusConvergenceEventAtDefault 5 ef))
      (bishopModulusConvergenceDecodeBHist
        (bishopModulusConvergenceEventAtDefault 6 ef))
      (bishopModulusConvergenceDecodeBHist
        (bishopModulusConvergenceEventAtDefault 7 ef))
      (bishopModulusConvergenceDecodeBHist
        (bishopModulusConvergenceEventAtDefault 8 ef)))

private theorem BishopModulusConvergenceTasteGate_single_carrier_alignment_round_trip
    (x : BishopModulusConvergenceUp) :
    bishopModulusConvergenceFromEventFlow
      (bishopModulusConvergenceToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S D M R E H C P N =>
      change
        some
          (BishopModulusConvergenceUp.mk
            (bishopModulusConvergenceDecodeBHist
              (bishopModulusConvergenceEncodeBHist S))
            (bishopModulusConvergenceDecodeBHist
              (bishopModulusConvergenceEncodeBHist D))
            (bishopModulusConvergenceDecodeBHist
              (bishopModulusConvergenceEncodeBHist M))
            (bishopModulusConvergenceDecodeBHist
              (bishopModulusConvergenceEncodeBHist R))
            (bishopModulusConvergenceDecodeBHist
              (bishopModulusConvergenceEncodeBHist E))
            (bishopModulusConvergenceDecodeBHist
              (bishopModulusConvergenceEncodeBHist H))
            (bishopModulusConvergenceDecodeBHist
              (bishopModulusConvergenceEncodeBHist C))
            (bishopModulusConvergenceDecodeBHist
              (bishopModulusConvergenceEncodeBHist P))
            (bishopModulusConvergenceDecodeBHist
              (bishopModulusConvergenceEncodeBHist N))) =
          some (BishopModulusConvergenceUp.mk S D M R E H C P N)
      rw [BishopModulusConvergenceTasteGate_single_carrier_alignment_decode_encode S,
        BishopModulusConvergenceTasteGate_single_carrier_alignment_decode_encode D,
        BishopModulusConvergenceTasteGate_single_carrier_alignment_decode_encode M,
        BishopModulusConvergenceTasteGate_single_carrier_alignment_decode_encode R,
        BishopModulusConvergenceTasteGate_single_carrier_alignment_decode_encode E,
        BishopModulusConvergenceTasteGate_single_carrier_alignment_decode_encode H,
        BishopModulusConvergenceTasteGate_single_carrier_alignment_decode_encode C,
        BishopModulusConvergenceTasteGate_single_carrier_alignment_decode_encode P,
        BishopModulusConvergenceTasteGate_single_carrier_alignment_decode_encode N]

private theorem BishopModulusConvergenceTasteGate_single_carrier_alignment_injective
    {x y : BishopModulusConvergenceUp} :
    bishopModulusConvergenceToEventFlow x =
      bishopModulusConvergenceToEventFlow y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopModulusConvergenceFromEventFlow
          (bishopModulusConvergenceToEventFlow x) =
        bishopModulusConvergenceFromEventFlow
          (bishopModulusConvergenceToEventFlow y) :=
    congrArg bishopModulusConvergenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopModulusConvergenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopModulusConvergenceTasteGate_single_carrier_alignment_round_trip y)))

private theorem BishopModulusConvergenceTasteGate_single_carrier_alignment_fields :
    ∀ x y : BishopModulusConvergenceUp,
      bishopModulusConvergenceFields x =
        bishopModulusConvergenceFields y →
          x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S₁ D₁ M₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ D₂ M₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance bishopModulusConvergenceBHistCarrier :
    BHistCarrier BishopModulusConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopModulusConvergenceToEventFlow
  fromEventFlow := bishopModulusConvergenceFromEventFlow

instance bishopModulusConvergenceFieldFaithful :
    FieldFaithful BishopModulusConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopModulusConvergenceFields
  field_faithful :=
    BishopModulusConvergenceTasteGate_single_carrier_alignment_fields

instance bishopModulusConvergenceChapterTasteGate :
    ChapterTasteGate BishopModulusConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopModulusConvergenceFromEventFlow
        (bishopModulusConvergenceToEventFlow x) = some x
    exact BishopModulusConvergenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BishopModulusConvergenceTasteGate_single_carrier_alignment_injective heq)

def BishopModulusConvergenceTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate BishopModulusConvergenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopModulusConvergenceChapterTasteGate

theorem BishopModulusConvergenceTasteGate_single_carrier_alignment :
    ChapterTasteGate BishopModulusConvergenceUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact bishopModulusConvergenceChapterTasteGate

end BEDC.Derived.BishopModulusConvergenceUp
