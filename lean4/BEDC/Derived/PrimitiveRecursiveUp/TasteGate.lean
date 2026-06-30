import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PrimitiveRecursiveUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PrimitiveRecursiveUp : Type where
  | mk (Z S Pi K R H C Q N : BHist) : PrimitiveRecursiveUp
  deriving DecidableEq

def primitiveRecursiveEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: primitiveRecursiveEncodeBHist h
  | BHist.e1 h => BMark.b1 :: primitiveRecursiveEncodeBHist h

def primitiveRecursiveDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (primitiveRecursiveDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (primitiveRecursiveDecodeBHist tail)

private theorem PrimitiveRecursiveTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, primitiveRecursiveDecodeBHist (primitiveRecursiveEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def primitiveRecursiveFields : PrimitiveRecursiveUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PrimitiveRecursiveUp.mk Z S Pi K R H C Q N => [Z, S, Pi, K, R, H, C, Q, N]

def primitiveRecursiveToEventFlow : PrimitiveRecursiveUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (primitiveRecursiveFields x).map primitiveRecursiveEncodeBHist

private def PrimitiveRecursiveTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      PrimitiveRecursiveTasteGate_single_carrier_alignment_eventAt index rest

def primitiveRecursiveDecodeFields (ef : EventFlow) : PrimitiveRecursiveUp :=
  -- BEDC touchpoint anchor: BHist BMark
  PrimitiveRecursiveUp.mk
    (primitiveRecursiveDecodeBHist
      (PrimitiveRecursiveTasteGate_single_carrier_alignment_eventAt 0 ef))
    (primitiveRecursiveDecodeBHist
      (PrimitiveRecursiveTasteGate_single_carrier_alignment_eventAt 1 ef))
    (primitiveRecursiveDecodeBHist
      (PrimitiveRecursiveTasteGate_single_carrier_alignment_eventAt 2 ef))
    (primitiveRecursiveDecodeBHist
      (PrimitiveRecursiveTasteGate_single_carrier_alignment_eventAt 3 ef))
    (primitiveRecursiveDecodeBHist
      (PrimitiveRecursiveTasteGate_single_carrier_alignment_eventAt 4 ef))
    (primitiveRecursiveDecodeBHist
      (PrimitiveRecursiveTasteGate_single_carrier_alignment_eventAt 5 ef))
    (primitiveRecursiveDecodeBHist
      (PrimitiveRecursiveTasteGate_single_carrier_alignment_eventAt 6 ef))
    (primitiveRecursiveDecodeBHist
      (PrimitiveRecursiveTasteGate_single_carrier_alignment_eventAt 7 ef))
    (primitiveRecursiveDecodeBHist
      (PrimitiveRecursiveTasteGate_single_carrier_alignment_eventAt 8 ef))

def primitiveRecursiveFromEventFlow (ef : EventFlow) : Option PrimitiveRecursiveUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some (primitiveRecursiveDecodeFields ef)

private theorem PrimitiveRecursiveTasteGate_single_carrier_alignment_round_trip
    (x : PrimitiveRecursiveUp) :
    primitiveRecursiveFromEventFlow (primitiveRecursiveToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk Z S Pi K R H C Q N =>
      change
        some
          (PrimitiveRecursiveUp.mk
            (primitiveRecursiveDecodeBHist (primitiveRecursiveEncodeBHist Z))
            (primitiveRecursiveDecodeBHist (primitiveRecursiveEncodeBHist S))
            (primitiveRecursiveDecodeBHist (primitiveRecursiveEncodeBHist Pi))
            (primitiveRecursiveDecodeBHist (primitiveRecursiveEncodeBHist K))
            (primitiveRecursiveDecodeBHist (primitiveRecursiveEncodeBHist R))
            (primitiveRecursiveDecodeBHist (primitiveRecursiveEncodeBHist H))
            (primitiveRecursiveDecodeBHist (primitiveRecursiveEncodeBHist C))
            (primitiveRecursiveDecodeBHist (primitiveRecursiveEncodeBHist Q))
            (primitiveRecursiveDecodeBHist (primitiveRecursiveEncodeBHist N))) =
          some (PrimitiveRecursiveUp.mk Z S Pi K R H C Q N)
      rw [PrimitiveRecursiveTasteGate_single_carrier_alignment_decode_encode Z,
        PrimitiveRecursiveTasteGate_single_carrier_alignment_decode_encode S,
        PrimitiveRecursiveTasteGate_single_carrier_alignment_decode_encode Pi,
        PrimitiveRecursiveTasteGate_single_carrier_alignment_decode_encode K,
        PrimitiveRecursiveTasteGate_single_carrier_alignment_decode_encode R,
        PrimitiveRecursiveTasteGate_single_carrier_alignment_decode_encode H,
        PrimitiveRecursiveTasteGate_single_carrier_alignment_decode_encode C,
        PrimitiveRecursiveTasteGate_single_carrier_alignment_decode_encode Q,
        PrimitiveRecursiveTasteGate_single_carrier_alignment_decode_encode N]

private theorem PrimitiveRecursiveTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : PrimitiveRecursiveUp} :
    primitiveRecursiveToEventFlow x = primitiveRecursiveToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      primitiveRecursiveFromEventFlow (primitiveRecursiveToEventFlow x) =
        primitiveRecursiveFromEventFlow (primitiveRecursiveToEventFlow y) :=
    congrArg primitiveRecursiveFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (PrimitiveRecursiveTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (PrimitiveRecursiveTasteGate_single_carrier_alignment_round_trip y)))

instance primitiveRecursiveBHistCarrier : BHistCarrier PrimitiveRecursiveUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := primitiveRecursiveToEventFlow
  fromEventFlow := primitiveRecursiveFromEventFlow

instance primitiveRecursiveChapterTasteGate : ChapterTasteGate PrimitiveRecursiveUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change primitiveRecursiveFromEventFlow (primitiveRecursiveToEventFlow x) = some x
    exact PrimitiveRecursiveTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (PrimitiveRecursiveTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate PrimitiveRecursiveUp :=
  -- BEDC touchpoint anchor: BHist BMark
  primitiveRecursiveChapterTasteGate

theorem PrimitiveRecursiveTasteGate_single_carrier_alignment :
    (∀ h : BHist, primitiveRecursiveDecodeBHist (primitiveRecursiveEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier PrimitiveRecursiveUp) ∧
        Nonempty (ChapterTasteGate PrimitiveRecursiveUp) ∧
          primitiveRecursiveEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨PrimitiveRecursiveTasteGate_single_carrier_alignment_decode_encode,
      ⟨primitiveRecursiveBHistCarrier⟩,
      ⟨primitiveRecursiveChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.PrimitiveRecursiveUp.TasteGate
