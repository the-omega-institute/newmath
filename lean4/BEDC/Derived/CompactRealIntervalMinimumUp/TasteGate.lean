import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactRealIntervalMinimumUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactRealIntervalMinimumUp : Type where
  | mk (I K F L W R E H C P N : BHist) : CompactRealIntervalMinimumUp
  deriving DecidableEq

def compactRealIntervalMinimumEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactRealIntervalMinimumEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactRealIntervalMinimumEncodeBHist h

def compactRealIntervalMinimumDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactRealIntervalMinimumDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactRealIntervalMinimumDecodeBHist tail)

private theorem CompactRealIntervalMinimumTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      compactRealIntervalMinimumDecodeBHist (compactRealIntervalMinimumEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def compactRealIntervalMinimumToEventFlow :
    CompactRealIntervalMinimumUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CompactRealIntervalMinimumUp.mk I K F L W R E H C P N =>
      [compactRealIntervalMinimumEncodeBHist I,
        compactRealIntervalMinimumEncodeBHist K,
        compactRealIntervalMinimumEncodeBHist F,
        compactRealIntervalMinimumEncodeBHist L,
        compactRealIntervalMinimumEncodeBHist W,
        compactRealIntervalMinimumEncodeBHist R,
        compactRealIntervalMinimumEncodeBHist E,
        compactRealIntervalMinimumEncodeBHist H,
        compactRealIntervalMinimumEncodeBHist C,
        compactRealIntervalMinimumEncodeBHist P,
        compactRealIntervalMinimumEncodeBHist N]

def compactRealIntervalMinimumFromEventFlow :
    EventFlow → Option CompactRealIntervalMinimumUp
  -- BEDC touchpoint anchor: BHist BMark
  | I :: K :: F :: L :: W :: R :: E :: H :: C :: P :: N :: [] =>
      some
        (CompactRealIntervalMinimumUp.mk
          (compactRealIntervalMinimumDecodeBHist I)
          (compactRealIntervalMinimumDecodeBHist K)
          (compactRealIntervalMinimumDecodeBHist F)
          (compactRealIntervalMinimumDecodeBHist L)
          (compactRealIntervalMinimumDecodeBHist W)
          (compactRealIntervalMinimumDecodeBHist R)
          (compactRealIntervalMinimumDecodeBHist E)
          (compactRealIntervalMinimumDecodeBHist H)
          (compactRealIntervalMinimumDecodeBHist C)
          (compactRealIntervalMinimumDecodeBHist P)
          (compactRealIntervalMinimumDecodeBHist N))
  | _ => none

private theorem CompactRealIntervalMinimumTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CompactRealIntervalMinimumUp,
      compactRealIntervalMinimumFromEventFlow
          (compactRealIntervalMinimumToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I K F L W R E H C P N =>
      change
        some
          (CompactRealIntervalMinimumUp.mk
            (compactRealIntervalMinimumDecodeBHist
              (compactRealIntervalMinimumEncodeBHist I))
            (compactRealIntervalMinimumDecodeBHist
              (compactRealIntervalMinimumEncodeBHist K))
            (compactRealIntervalMinimumDecodeBHist
              (compactRealIntervalMinimumEncodeBHist F))
            (compactRealIntervalMinimumDecodeBHist
              (compactRealIntervalMinimumEncodeBHist L))
            (compactRealIntervalMinimumDecodeBHist
              (compactRealIntervalMinimumEncodeBHist W))
            (compactRealIntervalMinimumDecodeBHist
              (compactRealIntervalMinimumEncodeBHist R))
            (compactRealIntervalMinimumDecodeBHist
              (compactRealIntervalMinimumEncodeBHist E))
            (compactRealIntervalMinimumDecodeBHist
              (compactRealIntervalMinimumEncodeBHist H))
            (compactRealIntervalMinimumDecodeBHist
              (compactRealIntervalMinimumEncodeBHist C))
            (compactRealIntervalMinimumDecodeBHist
              (compactRealIntervalMinimumEncodeBHist P))
            (compactRealIntervalMinimumDecodeBHist
              (compactRealIntervalMinimumEncodeBHist N))) =
          some (CompactRealIntervalMinimumUp.mk I K F L W R E H C P N)
      rw [CompactRealIntervalMinimumTasteGate_single_carrier_alignment_decode I,
        CompactRealIntervalMinimumTasteGate_single_carrier_alignment_decode K,
        CompactRealIntervalMinimumTasteGate_single_carrier_alignment_decode F,
        CompactRealIntervalMinimumTasteGate_single_carrier_alignment_decode L,
        CompactRealIntervalMinimumTasteGate_single_carrier_alignment_decode W,
        CompactRealIntervalMinimumTasteGate_single_carrier_alignment_decode R,
        CompactRealIntervalMinimumTasteGate_single_carrier_alignment_decode E,
        CompactRealIntervalMinimumTasteGate_single_carrier_alignment_decode H,
        CompactRealIntervalMinimumTasteGate_single_carrier_alignment_decode C,
        CompactRealIntervalMinimumTasteGate_single_carrier_alignment_decode P,
        CompactRealIntervalMinimumTasteGate_single_carrier_alignment_decode N]

private theorem CompactRealIntervalMinimumTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompactRealIntervalMinimumUp} :
    compactRealIntervalMinimumToEventFlow x =
        compactRealIntervalMinimumToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactRealIntervalMinimumFromEventFlow
          (compactRealIntervalMinimumToEventFlow x) =
        compactRealIntervalMinimumFromEventFlow
          (compactRealIntervalMinimumToEventFlow y) :=
    congrArg compactRealIntervalMinimumFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CompactRealIntervalMinimumTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompactRealIntervalMinimumTasteGate_single_carrier_alignment_round_trip y)))

instance compactRealIntervalMinimumBHistCarrier :
    BHistCarrier CompactRealIntervalMinimumUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactRealIntervalMinimumToEventFlow
  fromEventFlow := compactRealIntervalMinimumFromEventFlow

instance compactRealIntervalMinimumChapterTasteGate :
    ChapterTasteGate CompactRealIntervalMinimumUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactRealIntervalMinimumFromEventFlow
          (compactRealIntervalMinimumToEventFlow x) =
        some x
    exact CompactRealIntervalMinimumTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CompactRealIntervalMinimumTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

theorem CompactRealIntervalMinimumTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        compactRealIntervalMinimumDecodeBHist
            (compactRealIntervalMinimumEncodeBHist h) =
          h) ∧
      Nonempty (BHistCarrier CompactRealIntervalMinimumUp) ∧
        Nonempty (ChapterTasteGate CompactRealIntervalMinimumUp) ∧
          compactRealIntervalMinimumEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CompactRealIntervalMinimumTasteGate_single_carrier_alignment_decode,
      ⟨compactRealIntervalMinimumBHistCarrier⟩,
      ⟨compactRealIntervalMinimumChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.CompactRealIntervalMinimumUp
