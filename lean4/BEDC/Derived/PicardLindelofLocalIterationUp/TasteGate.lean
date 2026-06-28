import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PicardLindelofLocalIterationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PicardLindelofLocalIterationUp : Type where
  | mk (O F I M S R E H C P0 N : BHist) : PicardLindelofLocalIterationUp

def PicardLindelofLocalIterationTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 :: PicardLindelofLocalIterationTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h =>
      BMark.b1 :: PicardLindelofLocalIterationTasteGate_single_carrier_alignment_encodeBHist h

def PicardLindelofLocalIterationTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0
        (PicardLindelofLocalIterationTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1
        (PicardLindelofLocalIterationTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem PicardLindelofLocalIterationTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      PicardLindelofLocalIterationTasteGate_single_carrier_alignment_decodeBHist
        (PicardLindelofLocalIterationTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def PicardLindelofLocalIterationTasteGate_single_carrier_alignment_fields :
    PicardLindelofLocalIterationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PicardLindelofLocalIterationUp.mk O F I M S R E H C P0 N =>
      [O, F, I, M, S, R, E, H, C, P0, N]

def PicardLindelofLocalIterationTasteGate_single_carrier_alignment_toEventFlow :
    PicardLindelofLocalIterationUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (PicardLindelofLocalIterationTasteGate_single_carrier_alignment_fields x).map
      PicardLindelofLocalIterationTasteGate_single_carrier_alignment_encodeBHist

def PicardLindelofLocalIterationTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option PicardLindelofLocalIterationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [O, F, I, M, S, R, E, H, C, P0, N] =>
      some
        (PicardLindelofLocalIterationUp.mk
          (PicardLindelofLocalIterationTasteGate_single_carrier_alignment_decodeBHist O)
          (PicardLindelofLocalIterationTasteGate_single_carrier_alignment_decodeBHist F)
          (PicardLindelofLocalIterationTasteGate_single_carrier_alignment_decodeBHist I)
          (PicardLindelofLocalIterationTasteGate_single_carrier_alignment_decodeBHist M)
          (PicardLindelofLocalIterationTasteGate_single_carrier_alignment_decodeBHist S)
          (PicardLindelofLocalIterationTasteGate_single_carrier_alignment_decodeBHist R)
          (PicardLindelofLocalIterationTasteGate_single_carrier_alignment_decodeBHist E)
          (PicardLindelofLocalIterationTasteGate_single_carrier_alignment_decodeBHist H)
          (PicardLindelofLocalIterationTasteGate_single_carrier_alignment_decodeBHist C)
          (PicardLindelofLocalIterationTasteGate_single_carrier_alignment_decodeBHist P0)
          (PicardLindelofLocalIterationTasteGate_single_carrier_alignment_decodeBHist N))
  | _ => none

private theorem PicardLindelofLocalIterationTasteGate_single_carrier_alignment_round_trip
    (x : PicardLindelofLocalIterationUp) :
    PicardLindelofLocalIterationTasteGate_single_carrier_alignment_fromEventFlow
      (PicardLindelofLocalIterationTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk O F I M S R E H C P0 N =>
      change
        some
          (PicardLindelofLocalIterationUp.mk
            (PicardLindelofLocalIterationTasteGate_single_carrier_alignment_decodeBHist
              (PicardLindelofLocalIterationTasteGate_single_carrier_alignment_encodeBHist O))
            (PicardLindelofLocalIterationTasteGate_single_carrier_alignment_decodeBHist
              (PicardLindelofLocalIterationTasteGate_single_carrier_alignment_encodeBHist F))
            (PicardLindelofLocalIterationTasteGate_single_carrier_alignment_decodeBHist
              (PicardLindelofLocalIterationTasteGate_single_carrier_alignment_encodeBHist I))
            (PicardLindelofLocalIterationTasteGate_single_carrier_alignment_decodeBHist
              (PicardLindelofLocalIterationTasteGate_single_carrier_alignment_encodeBHist M))
            (PicardLindelofLocalIterationTasteGate_single_carrier_alignment_decodeBHist
              (PicardLindelofLocalIterationTasteGate_single_carrier_alignment_encodeBHist S))
            (PicardLindelofLocalIterationTasteGate_single_carrier_alignment_decodeBHist
              (PicardLindelofLocalIterationTasteGate_single_carrier_alignment_encodeBHist R))
            (PicardLindelofLocalIterationTasteGate_single_carrier_alignment_decodeBHist
              (PicardLindelofLocalIterationTasteGate_single_carrier_alignment_encodeBHist E))
            (PicardLindelofLocalIterationTasteGate_single_carrier_alignment_decodeBHist
              (PicardLindelofLocalIterationTasteGate_single_carrier_alignment_encodeBHist H))
            (PicardLindelofLocalIterationTasteGate_single_carrier_alignment_decodeBHist
              (PicardLindelofLocalIterationTasteGate_single_carrier_alignment_encodeBHist C))
            (PicardLindelofLocalIterationTasteGate_single_carrier_alignment_decodeBHist
              (PicardLindelofLocalIterationTasteGate_single_carrier_alignment_encodeBHist P0))
            (PicardLindelofLocalIterationTasteGate_single_carrier_alignment_decodeBHist
              (PicardLindelofLocalIterationTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (PicardLindelofLocalIterationUp.mk O F I M S R E H C P0 N)
      rw [PicardLindelofLocalIterationTasteGate_single_carrier_alignment_decode_encode O,
        PicardLindelofLocalIterationTasteGate_single_carrier_alignment_decode_encode F,
        PicardLindelofLocalIterationTasteGate_single_carrier_alignment_decode_encode I,
        PicardLindelofLocalIterationTasteGate_single_carrier_alignment_decode_encode M,
        PicardLindelofLocalIterationTasteGate_single_carrier_alignment_decode_encode S,
        PicardLindelofLocalIterationTasteGate_single_carrier_alignment_decode_encode R,
        PicardLindelofLocalIterationTasteGate_single_carrier_alignment_decode_encode E,
        PicardLindelofLocalIterationTasteGate_single_carrier_alignment_decode_encode H,
        PicardLindelofLocalIterationTasteGate_single_carrier_alignment_decode_encode C,
        PicardLindelofLocalIterationTasteGate_single_carrier_alignment_decode_encode P0,
        PicardLindelofLocalIterationTasteGate_single_carrier_alignment_decode_encode N]

private theorem PicardLindelofLocalIterationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : PicardLindelofLocalIterationUp} :
    PicardLindelofLocalIterationTasteGate_single_carrier_alignment_toEventFlow x =
        PicardLindelofLocalIterationTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      PicardLindelofLocalIterationTasteGate_single_carrier_alignment_fromEventFlow
          (PicardLindelofLocalIterationTasteGate_single_carrier_alignment_toEventFlow x) =
        PicardLindelofLocalIterationTasteGate_single_carrier_alignment_fromEventFlow
          (PicardLindelofLocalIterationTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg PicardLindelofLocalIterationTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (PicardLindelofLocalIterationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (PicardLindelofLocalIterationTasteGate_single_carrier_alignment_round_trip y)))

instance picardLindelofLocalIterationBHistCarrier :
    BHistCarrier PicardLindelofLocalIterationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := PicardLindelofLocalIterationTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := PicardLindelofLocalIterationTasteGate_single_carrier_alignment_fromEventFlow

instance picardLindelofLocalIterationChapterTasteGate :
    ChapterTasteGate PicardLindelofLocalIterationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      PicardLindelofLocalIterationTasteGate_single_carrier_alignment_fromEventFlow
        (PicardLindelofLocalIterationTasteGate_single_carrier_alignment_toEventFlow x) =
          some x
    exact PicardLindelofLocalIterationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (PicardLindelofLocalIterationTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate PicardLindelofLocalIterationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  picardLindelofLocalIterationChapterTasteGate

theorem PicardLindelofLocalIterationTasteGate_single_carrier_alignment :
    ChapterTasteGate PicardLindelofLocalIterationUp := by
  -- BEDC touchpoint anchor: BHist BMark
  exact taste_gate

end BEDC.Derived.PicardLindelofLocalIterationUp
