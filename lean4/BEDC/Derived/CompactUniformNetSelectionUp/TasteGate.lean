import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow

namespace BEDC.Derived.CompactUniformNetSelectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow

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

end BEDC.Derived.CompactUniformNetSelectionUp
