import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HigmanLemmaUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HigmanLemmaUp : Type where
  | mk (S W E B D H C P N : BHist) : HigmanLemmaUp
  deriving DecidableEq

def higmanLemmaEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: higmanLemmaEncodeBHist h
  | BHist.e1 h => BMark.b1 :: higmanLemmaEncodeBHist h

def higmanLemmaDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (higmanLemmaDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (higmanLemmaDecodeBHist tail)

private theorem HigmanLemmaTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, higmanLemmaDecodeBHist (higmanLemmaEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def higmanLemmaToEventFlow : HigmanLemmaUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | HigmanLemmaUp.mk S W E B D H C P N =>
      [higmanLemmaEncodeBHist S,
        higmanLemmaEncodeBHist W,
        higmanLemmaEncodeBHist E,
        higmanLemmaEncodeBHist B,
        higmanLemmaEncodeBHist D,
        higmanLemmaEncodeBHist H,
        higmanLemmaEncodeBHist C,
        higmanLemmaEncodeBHist P,
        higmanLemmaEncodeBHist N]

private def higmanLemmaEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => higmanLemmaEventAtDefault index rest

def higmanLemmaFromEventFlow : EventFlow → Option HigmanLemmaUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (HigmanLemmaUp.mk
        (higmanLemmaDecodeBHist (higmanLemmaEventAtDefault 0 ef))
        (higmanLemmaDecodeBHist (higmanLemmaEventAtDefault 1 ef))
        (higmanLemmaDecodeBHist (higmanLemmaEventAtDefault 2 ef))
        (higmanLemmaDecodeBHist (higmanLemmaEventAtDefault 3 ef))
        (higmanLemmaDecodeBHist (higmanLemmaEventAtDefault 4 ef))
        (higmanLemmaDecodeBHist (higmanLemmaEventAtDefault 5 ef))
        (higmanLemmaDecodeBHist (higmanLemmaEventAtDefault 6 ef))
        (higmanLemmaDecodeBHist (higmanLemmaEventAtDefault 7 ef))
        (higmanLemmaDecodeBHist (higmanLemmaEventAtDefault 8 ef)))

private theorem HigmanLemmaTasteGate_single_carrier_alignment_round_trip
    (x : HigmanLemmaUp) :
    higmanLemmaFromEventFlow (higmanLemmaToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S W E B D H C P N =>
      change
        some
          (HigmanLemmaUp.mk
            (higmanLemmaDecodeBHist (higmanLemmaEncodeBHist S))
            (higmanLemmaDecodeBHist (higmanLemmaEncodeBHist W))
            (higmanLemmaDecodeBHist (higmanLemmaEncodeBHist E))
            (higmanLemmaDecodeBHist (higmanLemmaEncodeBHist B))
            (higmanLemmaDecodeBHist (higmanLemmaEncodeBHist D))
            (higmanLemmaDecodeBHist (higmanLemmaEncodeBHist H))
            (higmanLemmaDecodeBHist (higmanLemmaEncodeBHist C))
            (higmanLemmaDecodeBHist (higmanLemmaEncodeBHist P))
            (higmanLemmaDecodeBHist (higmanLemmaEncodeBHist N))) =
          some (HigmanLemmaUp.mk S W E B D H C P N)
      rw [HigmanLemmaTasteGate_single_carrier_alignment_decode_encode S,
        HigmanLemmaTasteGate_single_carrier_alignment_decode_encode W,
        HigmanLemmaTasteGate_single_carrier_alignment_decode_encode E,
        HigmanLemmaTasteGate_single_carrier_alignment_decode_encode B,
        HigmanLemmaTasteGate_single_carrier_alignment_decode_encode D,
        HigmanLemmaTasteGate_single_carrier_alignment_decode_encode H,
        HigmanLemmaTasteGate_single_carrier_alignment_decode_encode C,
        HigmanLemmaTasteGate_single_carrier_alignment_decode_encode P,
        HigmanLemmaTasteGate_single_carrier_alignment_decode_encode N]

private theorem HigmanLemmaTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : HigmanLemmaUp} :
    higmanLemmaToEventFlow x = higmanLemmaToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      higmanLemmaFromEventFlow (higmanLemmaToEventFlow x) =
        higmanLemmaFromEventFlow (higmanLemmaToEventFlow y) :=
    congrArg higmanLemmaFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (HigmanLemmaTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (HigmanLemmaTasteGate_single_carrier_alignment_round_trip y)))

instance higmanLemmaBHistCarrier : BHistCarrier HigmanLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := higmanLemmaToEventFlow
  fromEventFlow := higmanLemmaFromEventFlow

instance higmanLemmaChapterTasteGate : ChapterTasteGate HigmanLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change higmanLemmaFromEventFlow (higmanLemmaToEventFlow x) = some x
    exact HigmanLemmaTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HigmanLemmaTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem HigmanLemmaTasteGate_single_carrier_alignment :
    (∀ h : BHist, higmanLemmaDecodeBHist (higmanLemmaEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier HigmanLemmaUp) ∧
        Nonempty (ChapterTasteGate HigmanLemmaUp) ∧
          higmanLemmaEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨HigmanLemmaTasteGate_single_carrier_alignment_decode_encode,
      ⟨higmanLemmaBHistCarrier⟩,
      ⟨higmanLemmaChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.HigmanLemmaUp.TasteGate
