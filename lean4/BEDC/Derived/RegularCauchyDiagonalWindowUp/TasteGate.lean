import BEDC.Derived.RegularCauchyDiagonalWindowUp
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyDiagonalWindowUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def regularCauchyDiagonalWindowEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyDiagonalWindowEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyDiagonalWindowEncodeBHist h

def regularCauchyDiagonalWindowDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyDiagonalWindowDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyDiagonalWindowDecodeBHist tail)

private theorem RegularCauchyDiagonalWindowTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      regularCauchyDiagonalWindowDecodeBHist
          (regularCauchyDiagonalWindowEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyDiagonalWindowToEventFlow : RegularCauchyDiagonalWindowUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyDiagonalWindowUp.packet => [[BMark.b0]]

def regularCauchyDiagonalWindowFromEventFlow : EventFlow -> Option RegularCauchyDiagonalWindowUp
  -- BEDC touchpoint anchor: BHist BMark
  | _ => some RegularCauchyDiagonalWindowUp.packet

private theorem RegularCauchyDiagonalWindowTasteGate_single_carrier_alignment_round_trip :
    forall x : RegularCauchyDiagonalWindowUp,
      regularCauchyDiagonalWindowFromEventFlow
          (regularCauchyDiagonalWindowToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x
  rfl

private theorem RegularCauchyDiagonalWindowTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyDiagonalWindowUp} :
    regularCauchyDiagonalWindowToEventFlow x =
        regularCauchyDiagonalWindowToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro _heq
  cases x
  cases y
  rfl

private theorem RegularCauchyDiagonalWindowTasteGate_single_carrier_alignment_empty_encode :
    regularCauchyDiagonalWindowEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  rfl

instance regularCauchyDiagonalWindowBHistCarrier :
    BHistCarrier RegularCauchyDiagonalWindowUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyDiagonalWindowToEventFlow
  fromEventFlow := regularCauchyDiagonalWindowFromEventFlow

instance regularCauchyDiagonalWindowChapterTasteGate :
    ChapterTasteGate RegularCauchyDiagonalWindowUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyDiagonalWindowFromEventFlow
          (regularCauchyDiagonalWindowToEventFlow x) = some x
    exact RegularCauchyDiagonalWindowTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact
      hxy
        (RegularCauchyDiagonalWindowTasteGate_single_carrier_alignment_toEventFlow_injective
          heq)

theorem RegularCauchyDiagonalWindowTasteGate_single_carrier_alignment :
    (forall h : BHist,
      regularCauchyDiagonalWindowDecodeBHist
          (regularCauchyDiagonalWindowEncodeBHist h) = h) ∧
      regularCauchyDiagonalWindowEncodeBHist BHist.Empty = ([] : List BMark) ∧
        (forall x : RegularCauchyDiagonalWindowUp,
          regularCauchyDiagonalWindowFromEventFlow
              (regularCauchyDiagonalWindowToEventFlow x) = some x) ∧
          (forall x y : RegularCauchyDiagonalWindowUp,
            regularCauchyDiagonalWindowToEventFlow x =
                regularCauchyDiagonalWindowToEventFlow y -> x = y) ∧
            Nonempty (ChapterTasteGate RegularCauchyDiagonalWindowUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RegularCauchyDiagonalWindowTasteGate_single_carrier_alignment_decode,
      RegularCauchyDiagonalWindowTasteGate_single_carrier_alignment_empty_encode,
      RegularCauchyDiagonalWindowTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RegularCauchyDiagonalWindowTasteGate_single_carrier_alignment_toEventFlow_injective
          heq),
      ⟨regularCauchyDiagonalWindowChapterTasteGate⟩⟩

end BEDC.Derived.RegularCauchyDiagonalWindowUp
