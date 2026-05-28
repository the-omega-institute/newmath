import BEDC.Derived.CompactOpenFunctionSpaceUp
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactOpenFunctionSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def compactOpenFunctionSpaceEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactOpenFunctionSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactOpenFunctionSpaceEncodeBHist h

def compactOpenFunctionSpaceDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactOpenFunctionSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactOpenFunctionSpaceDecodeBHist tail)

private theorem CompactOpenFunctionSpaceTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist, compactOpenFunctionSpaceDecodeBHist
      (compactOpenFunctionSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactOpenFunctionSpaceRows : CompactOpenFunctionSpaceUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactOpenFunctionSpaceUp.compactOpenFunctionSpace =>
      [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
        BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty]

def compactOpenFunctionSpaceToEventFlow : CompactOpenFunctionSpaceUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (compactOpenFunctionSpaceRows x).map compactOpenFunctionSpaceEncodeBHist

def compactOpenFunctionSpaceFromEventFlow : EventFlow -> Option CompactOpenFunctionSpaceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _X :: [] => none
  | _X :: _F :: [] => none
  | _X :: _F :: _S :: [] => none
  | _X :: _F :: _S :: _U :: [] => none
  | _X :: _F :: _S :: _U :: _W :: [] => none
  | _X :: _F :: _S :: _U :: _W :: _R :: [] => none
  | _X :: _F :: _S :: _U :: _W :: _R :: _E :: [] => none
  | _X :: _F :: _S :: _U :: _W :: _R :: _E :: _H :: [] => none
  | _X :: _F :: _S :: _U :: _W :: _R :: _E :: _H :: _C :: [] => none
  | _X :: _F :: _S :: _U :: _W :: _R :: _E :: _H :: _C :: _P :: [] => none
  | _X :: _F :: _S :: _U :: _W :: _R :: _E :: _H :: _C :: _P :: _N :: [] =>
      some CompactOpenFunctionSpaceUp.compactOpenFunctionSpace
  | _X :: _F :: _S :: _U :: _W :: _R :: _E :: _H :: _C :: _P :: _N :: _extra :: _rest =>
      none

private theorem CompactOpenFunctionSpaceTasteGate_single_carrier_alignment_round_trip :
    forall x : CompactOpenFunctionSpaceUp,
      compactOpenFunctionSpaceFromEventFlow (compactOpenFunctionSpaceToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x
  rfl

private theorem CompactOpenFunctionSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompactOpenFunctionSpaceUp} :
    compactOpenFunctionSpaceToEventFlow x = compactOpenFunctionSpaceToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro _heq
  cases x
  cases y
  rfl

instance compactOpenFunctionSpaceBHistCarrier : BHistCarrier CompactOpenFunctionSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactOpenFunctionSpaceToEventFlow
  fromEventFlow := compactOpenFunctionSpaceFromEventFlow

instance compactOpenFunctionSpaceChapterTasteGate :
    ChapterTasteGate CompactOpenFunctionSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactOpenFunctionSpaceFromEventFlow (compactOpenFunctionSpaceToEventFlow x) =
        some x
    exact CompactOpenFunctionSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CompactOpenFunctionSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate CompactOpenFunctionSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactOpenFunctionSpaceChapterTasteGate

theorem CompactOpenFunctionSpaceTasteGate_single_carrier_alignment :
    (forall h : BHist, compactOpenFunctionSpaceDecodeBHist
      (compactOpenFunctionSpaceEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CompactOpenFunctionSpaceUp) ∧
        Nonempty (ChapterTasteGate CompactOpenFunctionSpaceUp) ∧
          (forall x : CompactOpenFunctionSpaceUp,
            compactOpenFunctionSpaceFromEventFlow (compactOpenFunctionSpaceToEventFlow x) =
              some x) ∧
            (forall x y : CompactOpenFunctionSpaceUp,
              compactOpenFunctionSpaceToEventFlow x =
                compactOpenFunctionSpaceToEventFlow y -> x = y) ∧
              compactOpenFunctionSpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CompactOpenFunctionSpaceTasteGate_single_carrier_alignment_decode_encode,
      ⟨compactOpenFunctionSpaceBHistCarrier⟩,
      ⟨compactOpenFunctionSpaceChapterTasteGate⟩,
      CompactOpenFunctionSpaceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CompactOpenFunctionSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CompactOpenFunctionSpaceUp
