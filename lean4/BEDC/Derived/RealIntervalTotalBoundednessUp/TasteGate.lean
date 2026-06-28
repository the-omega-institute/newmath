import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealIntervalTotalBoundednessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealIntervalTotalBoundednessUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk (I L epsilon M E F H C P N : BHist) : RealIntervalTotalBoundednessUp
  deriving DecidableEq

def realIntervalTotalBoundednessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realIntervalTotalBoundednessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realIntervalTotalBoundednessEncodeBHist h

def realIntervalTotalBoundednessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realIntervalTotalBoundednessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realIntervalTotalBoundednessDecodeBHist tail)

private theorem RealIntervalTotalBoundednessTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      realIntervalTotalBoundednessDecodeBHist
          (realIntervalTotalBoundednessEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realIntervalTotalBoundednessFields : RealIntervalTotalBoundednessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealIntervalTotalBoundednessUp.mk I L epsilon M E F H C P N =>
      [I, L, epsilon, M, E, F, H, C, P, N]

def realIntervalTotalBoundednessToEventFlow :
    RealIntervalTotalBoundednessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realIntervalTotalBoundednessFields x).map realIntervalTotalBoundednessEncodeBHist

def realIntervalTotalBoundednessFromEventFlow :
    EventFlow → Option RealIntervalTotalBoundednessUp
  -- BEDC touchpoint anchor: BHist BMark
  | I :: L :: epsilon :: M :: E :: F :: H :: C :: P :: N :: [] =>
      some
        (RealIntervalTotalBoundednessUp.mk
          (realIntervalTotalBoundednessDecodeBHist I)
          (realIntervalTotalBoundednessDecodeBHist L)
          (realIntervalTotalBoundednessDecodeBHist epsilon)
          (realIntervalTotalBoundednessDecodeBHist M)
          (realIntervalTotalBoundednessDecodeBHist E)
          (realIntervalTotalBoundednessDecodeBHist F)
          (realIntervalTotalBoundednessDecodeBHist H)
          (realIntervalTotalBoundednessDecodeBHist C)
          (realIntervalTotalBoundednessDecodeBHist P)
          (realIntervalTotalBoundednessDecodeBHist N))
  | _ => none

private theorem RealIntervalTotalBoundednessTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RealIntervalTotalBoundednessUp,
      realIntervalTotalBoundednessFromEventFlow
          (realIntervalTotalBoundednessToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I L epsilon M E F H C P N =>
      change
        some
          (RealIntervalTotalBoundednessUp.mk
            (realIntervalTotalBoundednessDecodeBHist
              (realIntervalTotalBoundednessEncodeBHist I))
            (realIntervalTotalBoundednessDecodeBHist
              (realIntervalTotalBoundednessEncodeBHist L))
            (realIntervalTotalBoundednessDecodeBHist
              (realIntervalTotalBoundednessEncodeBHist epsilon))
            (realIntervalTotalBoundednessDecodeBHist
              (realIntervalTotalBoundednessEncodeBHist M))
            (realIntervalTotalBoundednessDecodeBHist
              (realIntervalTotalBoundednessEncodeBHist E))
            (realIntervalTotalBoundednessDecodeBHist
              (realIntervalTotalBoundednessEncodeBHist F))
            (realIntervalTotalBoundednessDecodeBHist
              (realIntervalTotalBoundednessEncodeBHist H))
            (realIntervalTotalBoundednessDecodeBHist
              (realIntervalTotalBoundednessEncodeBHist C))
            (realIntervalTotalBoundednessDecodeBHist
              (realIntervalTotalBoundednessEncodeBHist P))
            (realIntervalTotalBoundednessDecodeBHist
              (realIntervalTotalBoundednessEncodeBHist N))) =
          some (RealIntervalTotalBoundednessUp.mk I L epsilon M E F H C P N)
      simp only [RealIntervalTotalBoundednessTasteGate_single_carrier_alignment_decode]

private theorem RealIntervalTotalBoundednessTasteGate_single_carrier_alignment_injective
    {x y : RealIntervalTotalBoundednessUp} :
    realIntervalTotalBoundednessToEventFlow x =
        realIntervalTotalBoundednessToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realIntervalTotalBoundednessFromEventFlow
          (realIntervalTotalBoundednessToEventFlow x) =
        realIntervalTotalBoundednessFromEventFlow
          (realIntervalTotalBoundednessToEventFlow y) :=
    congrArg realIntervalTotalBoundednessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RealIntervalTotalBoundednessTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RealIntervalTotalBoundednessTasteGate_single_carrier_alignment_round_trip y)))

instance realIntervalTotalBoundednessBHistCarrier :
    BHistCarrier RealIntervalTotalBoundednessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realIntervalTotalBoundednessToEventFlow
  fromEventFlow := realIntervalTotalBoundednessFromEventFlow

instance realIntervalTotalBoundednessChapterTasteGate :
    ChapterTasteGate RealIntervalTotalBoundednessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realIntervalTotalBoundednessFromEventFlow
          (realIntervalTotalBoundednessToEventFlow x) =
        some x
    exact RealIntervalTotalBoundednessTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealIntervalTotalBoundednessTasteGate_single_carrier_alignment_injective heq)

theorem RealIntervalTotalBoundednessTasteGate_single_carrier_alignment :
    ∀ h : BHist,
      realIntervalTotalBoundednessDecodeBHist
          (realIntervalTotalBoundednessEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  exact RealIntervalTotalBoundednessTasteGate_single_carrier_alignment_decode

end BEDC.Derived.RealIntervalTotalBoundednessUp
