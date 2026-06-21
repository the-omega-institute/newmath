import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactNetRadiusChainUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactNetRadiusChainUp : Type where
  | mk (K F A B D U H C P L : BHist) : CompactNetRadiusChainUp
  deriving DecidableEq

def compactNetRadiusChainEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 tail => BMark.b0 :: compactNetRadiusChainEncodeBHist tail
  | BHist.e1 tail => BMark.b1 :: compactNetRadiusChainEncodeBHist tail

def compactNetRadiusChainDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactNetRadiusChainDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactNetRadiusChainDecodeBHist tail)

private theorem CompactNetRadiusChainTasteGate_single_carrier_alignment_decode_encode :
    ∀ row : BHist,
      compactNetRadiusChainDecodeBHist (compactNetRadiusChainEncodeBHist row) = row := by
  -- BEDC touchpoint anchor: BHist BMark
  intro row
  induction row with
  | Empty => rfl
  | e0 row ih => exact congrArg BHist.e0 ih
  | e1 row ih => exact congrArg BHist.e1 ih

def compactNetRadiusChainToEventFlow : CompactNetRadiusChainUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CompactNetRadiusChainUp.mk K F A B D U H C P L =>
      [compactNetRadiusChainEncodeBHist K,
        compactNetRadiusChainEncodeBHist F,
        compactNetRadiusChainEncodeBHist A,
        compactNetRadiusChainEncodeBHist B,
        compactNetRadiusChainEncodeBHist D,
        compactNetRadiusChainEncodeBHist U,
        compactNetRadiusChainEncodeBHist H,
        compactNetRadiusChainEncodeBHist C,
        compactNetRadiusChainEncodeBHist P,
        compactNetRadiusChainEncodeBHist L]

private def compactNetRadiusChainEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => compactNetRadiusChainEventAtDefault index rest

def compactNetRadiusChainFromEventFlow (flow : EventFlow) : Option CompactNetRadiusChainUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompactNetRadiusChainUp.mk
      (compactNetRadiusChainDecodeBHist (compactNetRadiusChainEventAtDefault 0 flow))
      (compactNetRadiusChainDecodeBHist (compactNetRadiusChainEventAtDefault 1 flow))
      (compactNetRadiusChainDecodeBHist (compactNetRadiusChainEventAtDefault 2 flow))
      (compactNetRadiusChainDecodeBHist (compactNetRadiusChainEventAtDefault 3 flow))
      (compactNetRadiusChainDecodeBHist (compactNetRadiusChainEventAtDefault 4 flow))
      (compactNetRadiusChainDecodeBHist (compactNetRadiusChainEventAtDefault 5 flow))
      (compactNetRadiusChainDecodeBHist (compactNetRadiusChainEventAtDefault 6 flow))
      (compactNetRadiusChainDecodeBHist (compactNetRadiusChainEventAtDefault 7 flow))
      (compactNetRadiusChainDecodeBHist (compactNetRadiusChainEventAtDefault 8 flow))
      (compactNetRadiusChainDecodeBHist (compactNetRadiusChainEventAtDefault 9 flow)))

private theorem CompactNetRadiusChainTasteGate_single_carrier_alignment_round_trip
    (x : CompactNetRadiusChainUp) :
    compactNetRadiusChainFromEventFlow (compactNetRadiusChainToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk K F A B D U H C P L =>
      change
        some
          (CompactNetRadiusChainUp.mk
            (compactNetRadiusChainDecodeBHist (compactNetRadiusChainEncodeBHist K))
            (compactNetRadiusChainDecodeBHist (compactNetRadiusChainEncodeBHist F))
            (compactNetRadiusChainDecodeBHist (compactNetRadiusChainEncodeBHist A))
            (compactNetRadiusChainDecodeBHist (compactNetRadiusChainEncodeBHist B))
            (compactNetRadiusChainDecodeBHist (compactNetRadiusChainEncodeBHist D))
            (compactNetRadiusChainDecodeBHist (compactNetRadiusChainEncodeBHist U))
            (compactNetRadiusChainDecodeBHist (compactNetRadiusChainEncodeBHist H))
            (compactNetRadiusChainDecodeBHist (compactNetRadiusChainEncodeBHist C))
            (compactNetRadiusChainDecodeBHist (compactNetRadiusChainEncodeBHist P))
            (compactNetRadiusChainDecodeBHist (compactNetRadiusChainEncodeBHist L))) =
          some (CompactNetRadiusChainUp.mk K F A B D U H C P L)
      rw [CompactNetRadiusChainTasteGate_single_carrier_alignment_decode_encode K,
        CompactNetRadiusChainTasteGate_single_carrier_alignment_decode_encode F,
        CompactNetRadiusChainTasteGate_single_carrier_alignment_decode_encode A,
        CompactNetRadiusChainTasteGate_single_carrier_alignment_decode_encode B,
        CompactNetRadiusChainTasteGate_single_carrier_alignment_decode_encode D,
        CompactNetRadiusChainTasteGate_single_carrier_alignment_decode_encode U,
        CompactNetRadiusChainTasteGate_single_carrier_alignment_decode_encode H,
        CompactNetRadiusChainTasteGate_single_carrier_alignment_decode_encode C,
        CompactNetRadiusChainTasteGate_single_carrier_alignment_decode_encode P,
        CompactNetRadiusChainTasteGate_single_carrier_alignment_decode_encode L]

private theorem CompactNetRadiusChainTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompactNetRadiusChainUp} :
    compactNetRadiusChainToEventFlow x = compactNetRadiusChainToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactNetRadiusChainFromEventFlow (compactNetRadiusChainToEventFlow x) =
        compactNetRadiusChainFromEventFlow (compactNetRadiusChainToEventFlow y) :=
    congrArg compactNetRadiusChainFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CompactNetRadiusChainTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompactNetRadiusChainTasteGate_single_carrier_alignment_round_trip y)))

instance compactNetRadiusChainBHistCarrier : BHistCarrier CompactNetRadiusChainUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactNetRadiusChainToEventFlow
  fromEventFlow := compactNetRadiusChainFromEventFlow

instance compactNetRadiusChainChapterTasteGate :
    ChapterTasteGate CompactNetRadiusChainUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change compactNetRadiusChainFromEventFlow (compactNetRadiusChainToEventFlow x) = some x
    exact CompactNetRadiusChainTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CompactNetRadiusChainTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CompactNetRadiusChainTasteGate_single_carrier_alignment :
    ChapterTasteGate CompactNetRadiusChainUp := by
  -- BEDC touchpoint anchor: BHist BMark
  exact compactNetRadiusChainChapterTasteGate

end BEDC.Derived.CompactNetRadiusChainUp
