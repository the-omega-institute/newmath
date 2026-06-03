import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopLocatedCompletenessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopLocatedCompletenessUp : Type where
  | mk (I S R D E B H C P N : BHist) : BishopLocatedCompletenessUp

def bishopLocatedCompletenessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopLocatedCompletenessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopLocatedCompletenessEncodeBHist h

def bishopLocatedCompletenessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopLocatedCompletenessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopLocatedCompletenessDecodeBHist tail)

private theorem BishopLocatedCompletenessTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      bishopLocatedCompletenessDecodeBHist (bishopLocatedCompletenessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def bishopLocatedCompletenessFields : BishopLocatedCompletenessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopLocatedCompletenessUp.mk I S R D E B H C P N =>
      [I, S, R, D, E, B, H, C, P, N]

def bishopLocatedCompletenessToEventFlow : BishopLocatedCompletenessUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (bishopLocatedCompletenessFields x).map bishopLocatedCompletenessEncodeBHist

def bishopLocatedCompletenessFromEventFlow :
    EventFlow → Option BishopLocatedCompletenessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun eventFlow =>
    match eventFlow with
    | [] => none
    | _ :: [] => none
    | _ :: _ :: [] => none
    | _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
    | I :: S :: R :: D :: E :: B :: H :: C :: P :: N :: [] =>
      some
        (BishopLocatedCompletenessUp.mk
          (bishopLocatedCompletenessDecodeBHist I)
          (bishopLocatedCompletenessDecodeBHist S)
          (bishopLocatedCompletenessDecodeBHist R)
          (bishopLocatedCompletenessDecodeBHist D)
          (bishopLocatedCompletenessDecodeBHist E)
          (bishopLocatedCompletenessDecodeBHist B)
          (bishopLocatedCompletenessDecodeBHist H)
          (bishopLocatedCompletenessDecodeBHist C)
          (bishopLocatedCompletenessDecodeBHist P)
          (bishopLocatedCompletenessDecodeBHist N))
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ => none

def bishopLocatedCompletenessCarrier : BHistCarrier BishopLocatedCompletenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopLocatedCompletenessToEventFlow
  fromEventFlow := bishopLocatedCompletenessFromEventFlow

instance bishopLocatedCompletenessBHistCarrier :
    BHistCarrier BishopLocatedCompletenessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopLocatedCompletenessCarrier

private theorem BishopLocatedCompletenessTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BishopLocatedCompletenessUp,
      BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I S R D E B H C P N =>
      change
        some
            (BishopLocatedCompletenessUp.mk
              (bishopLocatedCompletenessDecodeBHist (bishopLocatedCompletenessEncodeBHist I))
              (bishopLocatedCompletenessDecodeBHist (bishopLocatedCompletenessEncodeBHist S))
              (bishopLocatedCompletenessDecodeBHist (bishopLocatedCompletenessEncodeBHist R))
              (bishopLocatedCompletenessDecodeBHist (bishopLocatedCompletenessEncodeBHist D))
              (bishopLocatedCompletenessDecodeBHist (bishopLocatedCompletenessEncodeBHist E))
              (bishopLocatedCompletenessDecodeBHist (bishopLocatedCompletenessEncodeBHist B))
              (bishopLocatedCompletenessDecodeBHist (bishopLocatedCompletenessEncodeBHist H))
              (bishopLocatedCompletenessDecodeBHist (bishopLocatedCompletenessEncodeBHist C))
              (bishopLocatedCompletenessDecodeBHist (bishopLocatedCompletenessEncodeBHist P))
              (bishopLocatedCompletenessDecodeBHist (bishopLocatedCompletenessEncodeBHist N))) =
          some (BishopLocatedCompletenessUp.mk I S R D E B H C P N)
      rw [BishopLocatedCompletenessTasteGate_single_carrier_alignment_decode_encode I]
      rw [BishopLocatedCompletenessTasteGate_single_carrier_alignment_decode_encode S]
      rw [BishopLocatedCompletenessTasteGate_single_carrier_alignment_decode_encode R]
      rw [BishopLocatedCompletenessTasteGate_single_carrier_alignment_decode_encode D]
      rw [BishopLocatedCompletenessTasteGate_single_carrier_alignment_decode_encode E]
      rw [BishopLocatedCompletenessTasteGate_single_carrier_alignment_decode_encode B]
      rw [BishopLocatedCompletenessTasteGate_single_carrier_alignment_decode_encode H]
      rw [BishopLocatedCompletenessTasteGate_single_carrier_alignment_decode_encode C]
      rw [BishopLocatedCompletenessTasteGate_single_carrier_alignment_decode_encode P]
      rw [BishopLocatedCompletenessTasteGate_single_carrier_alignment_decode_encode N]

private theorem BishopLocatedCompletenessTasteGate_single_carrier_alignment_ToEventFlow_injective
    {x y : BishopLocatedCompletenessUp} :
    BHistCarrier.toEventFlow x = BHistCarrier.toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x = BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) :=
        (BishopLocatedCompletenessTasteGate_single_carrier_alignment_round_trip x).symm
      _ = BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow y) :=
        congrArg BHistCarrier.fromEventFlow hxy
      _ = some y := BishopLocatedCompletenessTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

def bishopLocatedCompletenessGate :
    @ChapterTasteGate BishopLocatedCompletenessUp bishopLocatedCompletenessCarrier where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    exact BishopLocatedCompletenessTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BishopLocatedCompletenessTasteGate_single_carrier_alignment_ToEventFlow_injective heq)

instance bishopLocatedCompletenessChapterTasteGate :
    ChapterTasteGate BishopLocatedCompletenessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopLocatedCompletenessGate

theorem BishopLocatedCompletenessTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        bishopLocatedCompletenessDecodeBHist (bishopLocatedCompletenessEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier BishopLocatedCompletenessUp) ∧
        Nonempty (ChapterTasteGate BishopLocatedCompletenessUp) ∧
          bishopLocatedCompletenessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨BishopLocatedCompletenessTasteGate_single_carrier_alignment_decode_encode,
      ⟨⟨bishopLocatedCompletenessCarrier⟩, ⟨⟨bishopLocatedCompletenessGate⟩, rfl⟩⟩⟩

end BEDC.Derived.BishopLocatedCompletenessUp
