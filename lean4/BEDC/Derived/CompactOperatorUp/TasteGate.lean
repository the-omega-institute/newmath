import BEDC.Derived.CompactOperatorUp
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactOperatorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def compactOperatorEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactOperatorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactOperatorEncodeBHist h

def compactOperatorDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactOperatorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactOperatorDecodeBHist tail)

private theorem compactOperator_decode_encode_bhist :
    forall h : BHist, compactOperatorDecodeBHist (compactOperatorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactOperatorToEventFlow : CompactOperatorUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CompactOperatorUp.compactOperator => [[BMark.b0]]

def compactOperatorFromEventFlow (_ef : EventFlow) : Option CompactOperatorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some CompactOperatorUp.compactOperator

private theorem compactOperator_round_trip :
    forall x : CompactOperatorUp,
      compactOperatorFromEventFlow (compactOperatorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x
  rfl

private theorem compactOperatorToEventFlow_injective {x y : CompactOperatorUp} :
    compactOperatorToEventFlow x = compactOperatorToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro _heq
  cases x
  cases y
  rfl

instance compactOperatorBHistCarrier : BHistCarrier CompactOperatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactOperatorToEventFlow
  fromEventFlow := compactOperatorFromEventFlow

instance compactOperatorChapterTasteGate : ChapterTasteGate CompactOperatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change compactOperatorFromEventFlow (compactOperatorToEventFlow x) = some x
    exact compactOperator_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactOperatorToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CompactOperatorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactOperatorChapterTasteGate

theorem CompactOperatorTasteGate_single_carrier_alignment :
    (forall h : BHist, compactOperatorDecodeBHist (compactOperatorEncodeBHist h) = h) ∧
      (forall x : CompactOperatorUp,
        compactOperatorFromEventFlow (compactOperatorToEventFlow x) = some x) ∧
        (forall x y : CompactOperatorUp,
          compactOperatorToEventFlow x = compactOperatorToEventFlow y -> x = y) ∧
          compactOperatorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨compactOperator_decode_encode_bhist,
      compactOperator_round_trip,
      (fun _ _ heq => compactOperatorToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CompactOperatorUp
