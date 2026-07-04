import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Foundations.TriAxisCoverage
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactMetricContinuousImageCompactUp

open BEDC.Foundations.TriangleGenerationSystem
open BEDC.Foundations.TriAxisCoverage
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactMetricContinuousImageCompactUp : Type where
  | mk (K F U I T E H C P N : BHist) : CompactMetricContinuousImageCompactUp
  deriving DecidableEq

def compactMetricContinuousImageCompactAxisObjCode : TriAxisObjCode :=
  -- BEDC touchpoint anchor: BHist
  TriAxisObjCode.pairGen
    (TriAxisObjCode.distinctionGen TriAxisObjCode.base)
    (TriAxisObjCode.pairGen
      (TriAxisObjCode.timeGen TriAxisObjCode.base)
      (TriAxisObjCode.symmetryGen TriAxisObjCode.base))

theorem compactMetricContinuousImageCompactAxisObjCode_covers_distinction :
    CoversDistinction compactMetricContinuousImageCompactAxisObjCode := by
  -- BEDC touchpoint anchor: BHist
  unfold compactMetricContinuousImageCompactAxisObjCode
  exact CoversDistinction.pairLeft
    (CoversDistinction.here TriAxisObjCode.base)

theorem compactMetricContinuousImageCompactAxisObjCode_covers_time :
    CoversTime compactMetricContinuousImageCompactAxisObjCode := by
  -- BEDC touchpoint anchor: BHist
  unfold compactMetricContinuousImageCompactAxisObjCode
  exact CoversTime.pairRight
    (CoversTime.pairLeft
      (CoversTime.here TriAxisObjCode.base))

theorem compactMetricContinuousImageCompactAxisObjCode_covers_symmetry :
    CoversSymmetry compactMetricContinuousImageCompactAxisObjCode := by
  -- BEDC touchpoint anchor: BHist
  unfold compactMetricContinuousImageCompactAxisObjCode
  exact CoversSymmetry.pairRight
    (CoversSymmetry.pairRight
      (CoversSymmetry.here TriAxisObjCode.base))

def compactMetricContinuousImageCompactAxisObjCode_covers_all :
    AxisDemand.Covers AxisDemand.allThree compactMetricContinuousImageCompactAxisObjCode :=
  -- BEDC touchpoint anchor: BHist
  ⟨compactMetricContinuousImageCompactAxisObjCode_covers_distinction,
    compactMetricContinuousImageCompactAxisObjCode_covers_time,
    compactMetricContinuousImageCompactAxisObjCode_covers_symmetry⟩

instance compactMetricContinuousImageCompactTriAxisProjected :
    TriAxisProjected CompactMetricContinuousImageCompactUp where
  -- BEDC touchpoint anchor: BHist
  code := compactMetricContinuousImageCompactAxisObjCode
  projection_forced :=
    triAxisProjection_forced_unique compactMetricContinuousImageCompactAxisObjCode
  demanded_axes := AxisDemand.allThree
  covers_some := compactMetricContinuousImageCompactAxisObjCode_covers_all

def compactMetricContinuousImageCompactEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactMetricContinuousImageCompactEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactMetricContinuousImageCompactEncodeBHist h

def compactMetricContinuousImageCompactDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactMetricContinuousImageCompactDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactMetricContinuousImageCompactDecodeBHist tail)

private theorem CompactMetricContinuousImageCompactTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      compactMetricContinuousImageCompactDecodeBHist
          (compactMetricContinuousImageCompactEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactMetricContinuousImageCompactToEventFlow :
    CompactMetricContinuousImageCompactUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CompactMetricContinuousImageCompactUp.mk K F U I T E H C P N =>
      [compactMetricContinuousImageCompactEncodeBHist K,
        compactMetricContinuousImageCompactEncodeBHist F,
        compactMetricContinuousImageCompactEncodeBHist U,
        compactMetricContinuousImageCompactEncodeBHist I,
        compactMetricContinuousImageCompactEncodeBHist T,
        compactMetricContinuousImageCompactEncodeBHist E,
        compactMetricContinuousImageCompactEncodeBHist H,
        compactMetricContinuousImageCompactEncodeBHist C,
        compactMetricContinuousImageCompactEncodeBHist P,
        compactMetricContinuousImageCompactEncodeBHist N]

def compactMetricContinuousImageCompactFromEventFlow :
    EventFlow → Option CompactMetricContinuousImageCompactUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | K :: restF =>
      match restF with
      | [] => none
      | F :: restU =>
          match restU with
          | [] => none
          | U :: restI =>
              match restI with
              | [] => none
              | I :: restT =>
                  match restT with
                  | [] => none
                  | T :: restE =>
                      match restE with
                      | [] => none
                      | E :: restH =>
                          match restH with
                          | [] => none
                          | H :: restC =>
                              match restC with
                              | [] => none
                              | C :: restP =>
                                  match restP with
                                  | [] => none
                                  | P :: restN =>
                                      match restN with
                                      | [] => none
                                      | N :: rest =>
                                          match rest with
                                          | [] =>
                                              some
                                                (CompactMetricContinuousImageCompactUp.mk
                                                  (compactMetricContinuousImageCompactDecodeBHist K)
                                                  (compactMetricContinuousImageCompactDecodeBHist F)
                                                  (compactMetricContinuousImageCompactDecodeBHist U)
                                                  (compactMetricContinuousImageCompactDecodeBHist I)
                                                  (compactMetricContinuousImageCompactDecodeBHist T)
                                                  (compactMetricContinuousImageCompactDecodeBHist E)
                                                  (compactMetricContinuousImageCompactDecodeBHist H)
                                                  (compactMetricContinuousImageCompactDecodeBHist C)
                                                  (compactMetricContinuousImageCompactDecodeBHist P)
                                                  (compactMetricContinuousImageCompactDecodeBHist N))
                                          | _ :: _ => none

private theorem CompactMetricContinuousImageCompactTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CompactMetricContinuousImageCompactUp,
      compactMetricContinuousImageCompactFromEventFlow
          (compactMetricContinuousImageCompactToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K F U I T E H C P N =>
      change
        some
          (CompactMetricContinuousImageCompactUp.mk
            (compactMetricContinuousImageCompactDecodeBHist
              (compactMetricContinuousImageCompactEncodeBHist K))
            (compactMetricContinuousImageCompactDecodeBHist
              (compactMetricContinuousImageCompactEncodeBHist F))
            (compactMetricContinuousImageCompactDecodeBHist
              (compactMetricContinuousImageCompactEncodeBHist U))
            (compactMetricContinuousImageCompactDecodeBHist
              (compactMetricContinuousImageCompactEncodeBHist I))
            (compactMetricContinuousImageCompactDecodeBHist
              (compactMetricContinuousImageCompactEncodeBHist T))
            (compactMetricContinuousImageCompactDecodeBHist
              (compactMetricContinuousImageCompactEncodeBHist E))
            (compactMetricContinuousImageCompactDecodeBHist
              (compactMetricContinuousImageCompactEncodeBHist H))
            (compactMetricContinuousImageCompactDecodeBHist
              (compactMetricContinuousImageCompactEncodeBHist C))
            (compactMetricContinuousImageCompactDecodeBHist
              (compactMetricContinuousImageCompactEncodeBHist P))
            (compactMetricContinuousImageCompactDecodeBHist
              (compactMetricContinuousImageCompactEncodeBHist N))) =
          some (CompactMetricContinuousImageCompactUp.mk K F U I T E H C P N)
      rw [CompactMetricContinuousImageCompactTasteGate_single_carrier_alignment_decode K,
        CompactMetricContinuousImageCompactTasteGate_single_carrier_alignment_decode F,
        CompactMetricContinuousImageCompactTasteGate_single_carrier_alignment_decode U,
        CompactMetricContinuousImageCompactTasteGate_single_carrier_alignment_decode I,
        CompactMetricContinuousImageCompactTasteGate_single_carrier_alignment_decode T,
        CompactMetricContinuousImageCompactTasteGate_single_carrier_alignment_decode E,
        CompactMetricContinuousImageCompactTasteGate_single_carrier_alignment_decode H,
        CompactMetricContinuousImageCompactTasteGate_single_carrier_alignment_decode C,
        CompactMetricContinuousImageCompactTasteGate_single_carrier_alignment_decode P,
        CompactMetricContinuousImageCompactTasteGate_single_carrier_alignment_decode N]

private theorem CompactMetricContinuousImageCompactToEventFlow_injective
    {x y : CompactMetricContinuousImageCompactUp} :
    compactMetricContinuousImageCompactToEventFlow x =
        compactMetricContinuousImageCompactToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactMetricContinuousImageCompactFromEventFlow
          (compactMetricContinuousImageCompactToEventFlow x) =
        compactMetricContinuousImageCompactFromEventFlow
          (compactMetricContinuousImageCompactToEventFlow y) :=
    congrArg compactMetricContinuousImageCompactFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CompactMetricContinuousImageCompactTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompactMetricContinuousImageCompactTasteGate_single_carrier_alignment_round_trip y)))

instance compactMetricContinuousImageCompactBHistCarrier :
    BHistCarrier CompactMetricContinuousImageCompactUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactMetricContinuousImageCompactToEventFlow
  fromEventFlow := compactMetricContinuousImageCompactFromEventFlow

instance compactMetricContinuousImageCompactChapterTasteGate :
    ChapterTasteGate CompactMetricContinuousImageCompactUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactMetricContinuousImageCompactFromEventFlow
          (compactMetricContinuousImageCompactToEventFlow x) = some x
    exact CompactMetricContinuousImageCompactTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CompactMetricContinuousImageCompactToEventFlow_injective heq)

theorem CompactMetricContinuousImageCompactTasteGate_single_carrier_alignment
    (x : CompactMetricContinuousImageCompactUp) :
    compactMetricContinuousImageCompactFromEventFlow
        (compactMetricContinuousImageCompactToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk K F U I T E H C P N =>
      change
        some
          (CompactMetricContinuousImageCompactUp.mk
            (compactMetricContinuousImageCompactDecodeBHist
              (compactMetricContinuousImageCompactEncodeBHist K))
            (compactMetricContinuousImageCompactDecodeBHist
              (compactMetricContinuousImageCompactEncodeBHist F))
            (compactMetricContinuousImageCompactDecodeBHist
              (compactMetricContinuousImageCompactEncodeBHist U))
            (compactMetricContinuousImageCompactDecodeBHist
              (compactMetricContinuousImageCompactEncodeBHist I))
            (compactMetricContinuousImageCompactDecodeBHist
              (compactMetricContinuousImageCompactEncodeBHist T))
            (compactMetricContinuousImageCompactDecodeBHist
              (compactMetricContinuousImageCompactEncodeBHist E))
            (compactMetricContinuousImageCompactDecodeBHist
              (compactMetricContinuousImageCompactEncodeBHist H))
            (compactMetricContinuousImageCompactDecodeBHist
              (compactMetricContinuousImageCompactEncodeBHist C))
            (compactMetricContinuousImageCompactDecodeBHist
              (compactMetricContinuousImageCompactEncodeBHist P))
            (compactMetricContinuousImageCompactDecodeBHist
              (compactMetricContinuousImageCompactEncodeBHist N))) =
          some (CompactMetricContinuousImageCompactUp.mk K F U I T E H C P N)
      rw [CompactMetricContinuousImageCompactTasteGate_single_carrier_alignment_decode K,
        CompactMetricContinuousImageCompactTasteGate_single_carrier_alignment_decode F,
        CompactMetricContinuousImageCompactTasteGate_single_carrier_alignment_decode U,
        CompactMetricContinuousImageCompactTasteGate_single_carrier_alignment_decode I,
        CompactMetricContinuousImageCompactTasteGate_single_carrier_alignment_decode T,
        CompactMetricContinuousImageCompactTasteGate_single_carrier_alignment_decode E,
        CompactMetricContinuousImageCompactTasteGate_single_carrier_alignment_decode H,
        CompactMetricContinuousImageCompactTasteGate_single_carrier_alignment_decode C,
        CompactMetricContinuousImageCompactTasteGate_single_carrier_alignment_decode P,
        CompactMetricContinuousImageCompactTasteGate_single_carrier_alignment_decode N]

end BEDC.Derived.CompactMetricContinuousImageCompactUp
