import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactUniformNetSelectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactUniformNetSelectionUp : Type where
  | mk (K F M Q R D L U H C P N : BHist) : CompactUniformNetSelectionUp
  deriving DecidableEq

def compactUniformNetSelectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactUniformNetSelectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactUniformNetSelectionEncodeBHist h

def compactUniformNetSelectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactUniformNetSelectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactUniformNetSelectionDecodeBHist tail)

private theorem CompactUniformNetSelectionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      compactUniformNetSelectionDecodeBHist (compactUniformNetSelectionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactUniformNetSelectionToEventFlow : CompactUniformNetSelectionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CompactUniformNetSelectionUp.mk K F M Q R D L U H C P N =>
      [compactUniformNetSelectionEncodeBHist K,
        compactUniformNetSelectionEncodeBHist F,
        compactUniformNetSelectionEncodeBHist M,
        compactUniformNetSelectionEncodeBHist Q,
        compactUniformNetSelectionEncodeBHist R,
        compactUniformNetSelectionEncodeBHist D,
        compactUniformNetSelectionEncodeBHist L,
        compactUniformNetSelectionEncodeBHist U,
        compactUniformNetSelectionEncodeBHist H,
        compactUniformNetSelectionEncodeBHist C,
        compactUniformNetSelectionEncodeBHist P,
        compactUniformNetSelectionEncodeBHist N]

def compactUniformNetSelectionFromEventFlow :
    EventFlow → Option CompactUniformNetSelectionUp
  -- BEDC touchpoint anchor: BHist BMark
  | K :: F :: M :: Q :: R :: D :: L :: U :: H :: C :: P :: N :: [] =>
      some
        (CompactUniformNetSelectionUp.mk
          (compactUniformNetSelectionDecodeBHist K)
          (compactUniformNetSelectionDecodeBHist F)
          (compactUniformNetSelectionDecodeBHist M)
          (compactUniformNetSelectionDecodeBHist Q)
          (compactUniformNetSelectionDecodeBHist R)
          (compactUniformNetSelectionDecodeBHist D)
          (compactUniformNetSelectionDecodeBHist L)
          (compactUniformNetSelectionDecodeBHist U)
          (compactUniformNetSelectionDecodeBHist H)
          (compactUniformNetSelectionDecodeBHist C)
          (compactUniformNetSelectionDecodeBHist P)
          (compactUniformNetSelectionDecodeBHist N))
  | _ => none

private theorem CompactUniformNetSelectionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CompactUniformNetSelectionUp,
      compactUniformNetSelectionFromEventFlow (compactUniformNetSelectionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk K F M Q R D L U H C P N =>
      change
        some
          (CompactUniformNetSelectionUp.mk
            (compactUniformNetSelectionDecodeBHist (compactUniformNetSelectionEncodeBHist K))
            (compactUniformNetSelectionDecodeBHist (compactUniformNetSelectionEncodeBHist F))
            (compactUniformNetSelectionDecodeBHist (compactUniformNetSelectionEncodeBHist M))
            (compactUniformNetSelectionDecodeBHist (compactUniformNetSelectionEncodeBHist Q))
            (compactUniformNetSelectionDecodeBHist (compactUniformNetSelectionEncodeBHist R))
            (compactUniformNetSelectionDecodeBHist (compactUniformNetSelectionEncodeBHist D))
            (compactUniformNetSelectionDecodeBHist (compactUniformNetSelectionEncodeBHist L))
            (compactUniformNetSelectionDecodeBHist (compactUniformNetSelectionEncodeBHist U))
            (compactUniformNetSelectionDecodeBHist (compactUniformNetSelectionEncodeBHist H))
            (compactUniformNetSelectionDecodeBHist (compactUniformNetSelectionEncodeBHist C))
            (compactUniformNetSelectionDecodeBHist (compactUniformNetSelectionEncodeBHist P))
            (compactUniformNetSelectionDecodeBHist (compactUniformNetSelectionEncodeBHist N))) =
          some (CompactUniformNetSelectionUp.mk K F M Q R D L U H C P N)
      rw [CompactUniformNetSelectionTasteGate_single_carrier_alignment_decode K,
        CompactUniformNetSelectionTasteGate_single_carrier_alignment_decode F,
        CompactUniformNetSelectionTasteGate_single_carrier_alignment_decode M,
        CompactUniformNetSelectionTasteGate_single_carrier_alignment_decode Q,
        CompactUniformNetSelectionTasteGate_single_carrier_alignment_decode R,
        CompactUniformNetSelectionTasteGate_single_carrier_alignment_decode D,
        CompactUniformNetSelectionTasteGate_single_carrier_alignment_decode L,
        CompactUniformNetSelectionTasteGate_single_carrier_alignment_decode U,
        CompactUniformNetSelectionTasteGate_single_carrier_alignment_decode H,
        CompactUniformNetSelectionTasteGate_single_carrier_alignment_decode C,
        CompactUniformNetSelectionTasteGate_single_carrier_alignment_decode P,
        CompactUniformNetSelectionTasteGate_single_carrier_alignment_decode N]

private theorem CompactUniformNetSelectionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompactUniformNetSelectionUp} :
    compactUniformNetSelectionToEventFlow x = compactUniformNetSelectionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactUniformNetSelectionFromEventFlow (compactUniformNetSelectionToEventFlow x) =
        compactUniformNetSelectionFromEventFlow (compactUniformNetSelectionToEventFlow y) :=
    congrArg compactUniformNetSelectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CompactUniformNetSelectionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompactUniformNetSelectionTasteGate_single_carrier_alignment_round_trip y)))

instance compactUniformNetSelectionBHistCarrier :
    BHistCarrier CompactUniformNetSelectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactUniformNetSelectionToEventFlow
  fromEventFlow := compactUniformNetSelectionFromEventFlow

instance compactUniformNetSelectionChapterTasteGate :
    ChapterTasteGate CompactUniformNetSelectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactUniformNetSelectionFromEventFlow (compactUniformNetSelectionToEventFlow x) =
        some x
    exact CompactUniformNetSelectionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CompactUniformNetSelectionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate CompactUniformNetSelectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactUniformNetSelectionChapterTasteGate

theorem CompactUniformNetSelectionTasteGate_single_carrier_alignment :
    (∀ h : BHist, compactUniformNetSelectionDecodeBHist
        (compactUniformNetSelectionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CompactUniformNetSelectionUp) ∧
        Nonempty (ChapterTasteGate CompactUniformNetSelectionUp) ∧
          compactUniformNetSelectionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CompactUniformNetSelectionTasteGate_single_carrier_alignment_decode,
      ⟨compactUniformNetSelectionBHistCarrier⟩,
      ⟨compactUniformNetSelectionChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.CompactUniformNetSelectionUp
