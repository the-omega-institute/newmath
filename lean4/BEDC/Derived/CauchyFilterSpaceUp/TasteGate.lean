import BEDC.Derived.CauchyFilterSpaceUp
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyFilterSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def cauchyFilterSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyFilterSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyFilterSpaceEncodeBHist h

def cauchyFilterSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyFilterSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyFilterSpaceDecodeBHist tail)

private theorem CauchyFilterSpaceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyFilterSpaceDecodeBHist (cauchyFilterSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyFilterSpaceToEventFlow :
    BEDC.Derived.CauchyFilterSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BEDC.Derived.CauchyFilterSpaceUp.carrier => [cauchyFilterSpaceEncodeBHist BHist.Empty]

def cauchyFilterSpaceFromEventFlow :
    EventFlow → Option BEDC.Derived.CauchyFilterSpaceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _row :: [] => some BEDC.Derived.CauchyFilterSpaceUp.carrier
  | _head :: _next :: _tail => none

private theorem CauchyFilterSpaceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BEDC.Derived.CauchyFilterSpaceUp,
      cauchyFilterSpaceFromEventFlow (cauchyFilterSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x
  rfl

private theorem CauchyFilterSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BEDC.Derived.CauchyFilterSpaceUp} :
    cauchyFilterSpaceToEventFlow x = cauchyFilterSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro _heq
  cases x
  cases y
  rfl

instance cauchyFilterSpaceBHistCarrier :
    BHistCarrier BEDC.Derived.CauchyFilterSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyFilterSpaceToEventFlow
  fromEventFlow := cauchyFilterSpaceFromEventFlow

instance cauchyFilterSpaceChapterTasteGate :
    ChapterTasteGate BEDC.Derived.CauchyFilterSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyFilterSpaceFromEventFlow (cauchyFilterSpaceToEventFlow x) = some x
    exact CauchyFilterSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyFilterSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate BEDC.Derived.CauchyFilterSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyFilterSpaceChapterTasteGate

theorem CauchyFilterSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyFilterSpaceDecodeBHist (cauchyFilterSpaceEncodeBHist h) = h) ∧
      (∀ x : BEDC.Derived.CauchyFilterSpaceUp,
        cauchyFilterSpaceFromEventFlow (cauchyFilterSpaceToEventFlow x) = some x) ∧
        (∀ x y : BEDC.Derived.CauchyFilterSpaceUp,
          cauchyFilterSpaceToEventFlow x = cauchyFilterSpaceToEventFlow y → x = y) ∧
          cauchyFilterSpaceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CauchyFilterSpaceTasteGate_single_carrier_alignment_decode_encode,
      CauchyFilterSpaceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => CauchyFilterSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyFilterSpaceUp
