import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopCauchyModulusExtractionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopCauchyModulusExtractionUp : Type where
  | mk (S R D E M W H C P N : BHist) : BishopCauchyModulusExtractionUp
  deriving DecidableEq

def bishopCauchyModulusExtractionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopCauchyModulusExtractionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopCauchyModulusExtractionEncodeBHist h

def bishopCauchyModulusExtractionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopCauchyModulusExtractionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopCauchyModulusExtractionDecodeBHist tail)

private theorem BishopCauchyModulusExtractionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      bishopCauchyModulusExtractionDecodeBHist
        (bishopCauchyModulusExtractionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopCauchyModulusExtractionFields :
    BishopCauchyModulusExtractionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopCauchyModulusExtractionUp.mk S R D E M W H C P N =>
      [S, R, D, E, M, W, H, C, P, N]

def bishopCauchyModulusExtractionToEventFlow :
    BishopCauchyModulusExtractionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (bishopCauchyModulusExtractionFields x).map bishopCauchyModulusExtractionEncodeBHist

private def bishopCauchyModulusExtractionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopCauchyModulusExtractionEventAtDefault index rest

def bishopCauchyModulusExtractionFromEventFlow
    (ef : EventFlow) : Option BishopCauchyModulusExtractionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopCauchyModulusExtractionUp.mk
      (bishopCauchyModulusExtractionDecodeBHist
        (bishopCauchyModulusExtractionEventAtDefault 0 ef))
      (bishopCauchyModulusExtractionDecodeBHist
        (bishopCauchyModulusExtractionEventAtDefault 1 ef))
      (bishopCauchyModulusExtractionDecodeBHist
        (bishopCauchyModulusExtractionEventAtDefault 2 ef))
      (bishopCauchyModulusExtractionDecodeBHist
        (bishopCauchyModulusExtractionEventAtDefault 3 ef))
      (bishopCauchyModulusExtractionDecodeBHist
        (bishopCauchyModulusExtractionEventAtDefault 4 ef))
      (bishopCauchyModulusExtractionDecodeBHist
        (bishopCauchyModulusExtractionEventAtDefault 5 ef))
      (bishopCauchyModulusExtractionDecodeBHist
        (bishopCauchyModulusExtractionEventAtDefault 6 ef))
      (bishopCauchyModulusExtractionDecodeBHist
        (bishopCauchyModulusExtractionEventAtDefault 7 ef))
      (bishopCauchyModulusExtractionDecodeBHist
        (bishopCauchyModulusExtractionEventAtDefault 8 ef))
      (bishopCauchyModulusExtractionDecodeBHist
        (bishopCauchyModulusExtractionEventAtDefault 9 ef)))

private theorem BishopCauchyModulusExtractionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BishopCauchyModulusExtractionUp,
      bishopCauchyModulusExtractionFromEventFlow
        (bishopCauchyModulusExtractionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S R D E M W H C P N =>
      change
        some
          (BishopCauchyModulusExtractionUp.mk
            (bishopCauchyModulusExtractionDecodeBHist
              (bishopCauchyModulusExtractionEncodeBHist S))
            (bishopCauchyModulusExtractionDecodeBHist
              (bishopCauchyModulusExtractionEncodeBHist R))
            (bishopCauchyModulusExtractionDecodeBHist
              (bishopCauchyModulusExtractionEncodeBHist D))
            (bishopCauchyModulusExtractionDecodeBHist
              (bishopCauchyModulusExtractionEncodeBHist E))
            (bishopCauchyModulusExtractionDecodeBHist
              (bishopCauchyModulusExtractionEncodeBHist M))
            (bishopCauchyModulusExtractionDecodeBHist
              (bishopCauchyModulusExtractionEncodeBHist W))
            (bishopCauchyModulusExtractionDecodeBHist
              (bishopCauchyModulusExtractionEncodeBHist H))
            (bishopCauchyModulusExtractionDecodeBHist
              (bishopCauchyModulusExtractionEncodeBHist C))
            (bishopCauchyModulusExtractionDecodeBHist
              (bishopCauchyModulusExtractionEncodeBHist P))
            (bishopCauchyModulusExtractionDecodeBHist
              (bishopCauchyModulusExtractionEncodeBHist N))) =
          some (BishopCauchyModulusExtractionUp.mk S R D E M W H C P N)
      rw [BishopCauchyModulusExtractionTasteGate_single_carrier_alignment_decode S,
        BishopCauchyModulusExtractionTasteGate_single_carrier_alignment_decode R,
        BishopCauchyModulusExtractionTasteGate_single_carrier_alignment_decode D,
        BishopCauchyModulusExtractionTasteGate_single_carrier_alignment_decode E,
        BishopCauchyModulusExtractionTasteGate_single_carrier_alignment_decode M,
        BishopCauchyModulusExtractionTasteGate_single_carrier_alignment_decode W,
        BishopCauchyModulusExtractionTasteGate_single_carrier_alignment_decode H,
        BishopCauchyModulusExtractionTasteGate_single_carrier_alignment_decode C,
        BishopCauchyModulusExtractionTasteGate_single_carrier_alignment_decode P,
        BishopCauchyModulusExtractionTasteGate_single_carrier_alignment_decode N]

private theorem BishopCauchyModulusExtractionTasteGate_single_carrier_alignment_injective
    {x y : BishopCauchyModulusExtractionUp} :
    bishopCauchyModulusExtractionToEventFlow x =
      bishopCauchyModulusExtractionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopCauchyModulusExtractionFromEventFlow
          (bishopCauchyModulusExtractionToEventFlow x) =
        bishopCauchyModulusExtractionFromEventFlow
          (bishopCauchyModulusExtractionToEventFlow y) :=
    congrArg bishopCauchyModulusExtractionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopCauchyModulusExtractionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopCauchyModulusExtractionTasteGate_single_carrier_alignment_round_trip y)))

instance bishopCauchyModulusExtractionBHistCarrier :
    BHistCarrier BishopCauchyModulusExtractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopCauchyModulusExtractionToEventFlow
  fromEventFlow := bishopCauchyModulusExtractionFromEventFlow

instance bishopCauchyModulusExtractionChapterTasteGate :
    ChapterTasteGate BishopCauchyModulusExtractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopCauchyModulusExtractionFromEventFlow
        (bishopCauchyModulusExtractionToEventFlow x) = some x
    exact BishopCauchyModulusExtractionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BishopCauchyModulusExtractionTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate BishopCauchyModulusExtractionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopCauchyModulusExtractionChapterTasteGate

theorem BishopCauchyModulusExtractionTasteGate_single_carrier_alignment :
    (∀ h : BHist, bishopCauchyModulusExtractionDecodeBHist
      (bishopCauchyModulusExtractionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier BishopCauchyModulusExtractionUp) ∧
        Nonempty (ChapterTasteGate BishopCauchyModulusExtractionUp) ∧
          bishopCauchyModulusExtractionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  exact
    ⟨BishopCauchyModulusExtractionTasteGate_single_carrier_alignment_decode,
      ⟨bishopCauchyModulusExtractionBHistCarrier⟩,
      ⟨bishopCauchyModulusExtractionChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.BishopCauchyModulusExtractionUp
