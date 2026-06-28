import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopCompletionComparisonSquareUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopCompletionComparisonSquareUp : Type where
  | mk (Q0 Q1 I0 I1 D S R E L H C P N : BHist) :
      BishopCompletionComparisonSquareUp
  deriving DecidableEq

def bishopCompletionComparisonSquareEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopCompletionComparisonSquareEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopCompletionComparisonSquareEncodeBHist h

def bishopCompletionComparisonSquareDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopCompletionComparisonSquareDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopCompletionComparisonSquareDecodeBHist tail)

private theorem BishopCompletionComparisonSquareTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      bishopCompletionComparisonSquareDecodeBHist
        (bishopCompletionComparisonSquareEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopCompletionComparisonSquareToEventFlow :
    BishopCompletionComparisonSquareUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BishopCompletionComparisonSquareUp.mk Q0 Q1 I0 I1 D S R E L H C P N =>
      [bishopCompletionComparisonSquareEncodeBHist Q0,
        bishopCompletionComparisonSquareEncodeBHist Q1,
        bishopCompletionComparisonSquareEncodeBHist I0,
        bishopCompletionComparisonSquareEncodeBHist I1,
        bishopCompletionComparisonSquareEncodeBHist D,
        bishopCompletionComparisonSquareEncodeBHist S,
        bishopCompletionComparisonSquareEncodeBHist R,
        bishopCompletionComparisonSquareEncodeBHist E,
        bishopCompletionComparisonSquareEncodeBHist L,
        bishopCompletionComparisonSquareEncodeBHist H,
        bishopCompletionComparisonSquareEncodeBHist C,
        bishopCompletionComparisonSquareEncodeBHist P,
        bishopCompletionComparisonSquareEncodeBHist N]

def bishopCompletionComparisonSquareFromEventFlow :
    EventFlow -> Option BishopCompletionComparisonSquareUp
  -- BEDC touchpoint anchor: BHist BMark
  | Q0 :: Q1 :: I0 :: I1 :: D :: S :: R :: E :: L :: H :: C :: P :: N :: [] =>
      some
        (BishopCompletionComparisonSquareUp.mk
          (bishopCompletionComparisonSquareDecodeBHist Q0)
          (bishopCompletionComparisonSquareDecodeBHist Q1)
          (bishopCompletionComparisonSquareDecodeBHist I0)
          (bishopCompletionComparisonSquareDecodeBHist I1)
          (bishopCompletionComparisonSquareDecodeBHist D)
          (bishopCompletionComparisonSquareDecodeBHist S)
          (bishopCompletionComparisonSquareDecodeBHist R)
          (bishopCompletionComparisonSquareDecodeBHist E)
          (bishopCompletionComparisonSquareDecodeBHist L)
          (bishopCompletionComparisonSquareDecodeBHist H)
          (bishopCompletionComparisonSquareDecodeBHist C)
          (bishopCompletionComparisonSquareDecodeBHist P)
          (bishopCompletionComparisonSquareDecodeBHist N))
  | _ => none

private theorem BishopCompletionComparisonSquareTasteGate_single_carrier_alignment_round_trip :
    forall x : BishopCompletionComparisonSquareUp,
      bishopCompletionComparisonSquareFromEventFlow
        (bishopCompletionComparisonSquareToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q0 Q1 I0 I1 D S R E L H C P N =>
      change
        some
          (BishopCompletionComparisonSquareUp.mk
            (bishopCompletionComparisonSquareDecodeBHist
              (bishopCompletionComparisonSquareEncodeBHist Q0))
            (bishopCompletionComparisonSquareDecodeBHist
              (bishopCompletionComparisonSquareEncodeBHist Q1))
            (bishopCompletionComparisonSquareDecodeBHist
              (bishopCompletionComparisonSquareEncodeBHist I0))
            (bishopCompletionComparisonSquareDecodeBHist
              (bishopCompletionComparisonSquareEncodeBHist I1))
            (bishopCompletionComparisonSquareDecodeBHist
              (bishopCompletionComparisonSquareEncodeBHist D))
            (bishopCompletionComparisonSquareDecodeBHist
              (bishopCompletionComparisonSquareEncodeBHist S))
            (bishopCompletionComparisonSquareDecodeBHist
              (bishopCompletionComparisonSquareEncodeBHist R))
            (bishopCompletionComparisonSquareDecodeBHist
              (bishopCompletionComparisonSquareEncodeBHist E))
            (bishopCompletionComparisonSquareDecodeBHist
              (bishopCompletionComparisonSquareEncodeBHist L))
            (bishopCompletionComparisonSquareDecodeBHist
              (bishopCompletionComparisonSquareEncodeBHist H))
            (bishopCompletionComparisonSquareDecodeBHist
              (bishopCompletionComparisonSquareEncodeBHist C))
            (bishopCompletionComparisonSquareDecodeBHist
              (bishopCompletionComparisonSquareEncodeBHist P))
            (bishopCompletionComparisonSquareDecodeBHist
              (bishopCompletionComparisonSquareEncodeBHist N))) =
          some (BishopCompletionComparisonSquareUp.mk Q0 Q1 I0 I1 D S R E L H C P N)
      rw [BishopCompletionComparisonSquareTasteGate_single_carrier_alignment_decode Q0,
        BishopCompletionComparisonSquareTasteGate_single_carrier_alignment_decode Q1,
        BishopCompletionComparisonSquareTasteGate_single_carrier_alignment_decode I0,
        BishopCompletionComparisonSquareTasteGate_single_carrier_alignment_decode I1,
        BishopCompletionComparisonSquareTasteGate_single_carrier_alignment_decode D,
        BishopCompletionComparisonSquareTasteGate_single_carrier_alignment_decode S,
        BishopCompletionComparisonSquareTasteGate_single_carrier_alignment_decode R,
        BishopCompletionComparisonSquareTasteGate_single_carrier_alignment_decode E,
        BishopCompletionComparisonSquareTasteGate_single_carrier_alignment_decode L,
        BishopCompletionComparisonSquareTasteGate_single_carrier_alignment_decode H,
        BishopCompletionComparisonSquareTasteGate_single_carrier_alignment_decode C,
        BishopCompletionComparisonSquareTasteGate_single_carrier_alignment_decode P,
        BishopCompletionComparisonSquareTasteGate_single_carrier_alignment_decode N]

private theorem BishopCompletionComparisonSquareTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopCompletionComparisonSquareUp} :
    bishopCompletionComparisonSquareToEventFlow x =
        bishopCompletionComparisonSquareToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopCompletionComparisonSquareFromEventFlow
          (bishopCompletionComparisonSquareToEventFlow x) =
        bishopCompletionComparisonSquareFromEventFlow
          (bishopCompletionComparisonSquareToEventFlow y) :=
    congrArg bishopCompletionComparisonSquareFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopCompletionComparisonSquareTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopCompletionComparisonSquareTasteGate_single_carrier_alignment_round_trip y)))

instance bishopCompletionComparisonSquareBHistCarrier :
    BHistCarrier BishopCompletionComparisonSquareUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopCompletionComparisonSquareToEventFlow
  fromEventFlow := bishopCompletionComparisonSquareFromEventFlow

instance bishopCompletionComparisonSquareChapterTasteGate :
    ChapterTasteGate BishopCompletionComparisonSquareUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopCompletionComparisonSquareFromEventFlow
        (bishopCompletionComparisonSquareToEventFlow x) = some x
    exact BishopCompletionComparisonSquareTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BishopCompletionComparisonSquareTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem BishopCompletionComparisonSquareTasteGate_single_carrier_alignment :
    (forall h : BHist,
      bishopCompletionComparisonSquareDecodeBHist
        (bishopCompletionComparisonSquareEncodeBHist h) = h) /\
      bishopCompletionComparisonSquareEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨BishopCompletionComparisonSquareTasteGate_single_carrier_alignment_decode,
      rfl⟩

end BEDC.Derived.BishopCompletionComparisonSquareUp
