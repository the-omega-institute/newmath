import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PriestleyDualityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PriestleyDualityUp : Type where
  | mk (L B T S U O H C G N : BHist) : PriestleyDualityUp
  deriving DecidableEq

def priestleyDualityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: priestleyDualityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: priestleyDualityEncodeBHist h

def priestleyDualityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (priestleyDualityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (priestleyDualityDecodeBHist tail)

private theorem PriestleyDualityTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, priestleyDualityDecodeBHist (priestleyDualityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def priestleyDualityFields : PriestleyDualityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PriestleyDualityUp.mk L B T S U O H C G N => [L, B, T, S, U, O, H, C, G, N]

def priestleyDualityToEventFlow : PriestleyDualityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (priestleyDualityFields x).map priestleyDualityEncodeBHist

private def priestleyDualityEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => priestleyDualityEventAtDefault index rest

def priestleyDualityFromEventFlow (ef : EventFlow) :
    Option PriestleyDualityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PriestleyDualityUp.mk
      (priestleyDualityDecodeBHist (priestleyDualityEventAtDefault 0 ef))
      (priestleyDualityDecodeBHist (priestleyDualityEventAtDefault 1 ef))
      (priestleyDualityDecodeBHist (priestleyDualityEventAtDefault 2 ef))
      (priestleyDualityDecodeBHist (priestleyDualityEventAtDefault 3 ef))
      (priestleyDualityDecodeBHist (priestleyDualityEventAtDefault 4 ef))
      (priestleyDualityDecodeBHist (priestleyDualityEventAtDefault 5 ef))
      (priestleyDualityDecodeBHist (priestleyDualityEventAtDefault 6 ef))
      (priestleyDualityDecodeBHist (priestleyDualityEventAtDefault 7 ef))
      (priestleyDualityDecodeBHist (priestleyDualityEventAtDefault 8 ef))
      (priestleyDualityDecodeBHist (priestleyDualityEventAtDefault 9 ef)))

private theorem PriestleyDualityTasteGate_single_carrier_alignment_round_trip
    (x : PriestleyDualityUp) :
    priestleyDualityFromEventFlow (priestleyDualityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk L B T S U O H C G N =>
      change
        some
          (PriestleyDualityUp.mk
            (priestleyDualityDecodeBHist (priestleyDualityEncodeBHist L))
            (priestleyDualityDecodeBHist (priestleyDualityEncodeBHist B))
            (priestleyDualityDecodeBHist (priestleyDualityEncodeBHist T))
            (priestleyDualityDecodeBHist (priestleyDualityEncodeBHist S))
            (priestleyDualityDecodeBHist (priestleyDualityEncodeBHist U))
            (priestleyDualityDecodeBHist (priestleyDualityEncodeBHist O))
            (priestleyDualityDecodeBHist (priestleyDualityEncodeBHist H))
            (priestleyDualityDecodeBHist (priestleyDualityEncodeBHist C))
            (priestleyDualityDecodeBHist (priestleyDualityEncodeBHist G))
            (priestleyDualityDecodeBHist (priestleyDualityEncodeBHist N))) =
          some (PriestleyDualityUp.mk L B T S U O H C G N)
      rw [PriestleyDualityTasteGate_single_carrier_alignment_decode_encode L,
        PriestleyDualityTasteGate_single_carrier_alignment_decode_encode B,
        PriestleyDualityTasteGate_single_carrier_alignment_decode_encode T,
        PriestleyDualityTasteGate_single_carrier_alignment_decode_encode S,
        PriestleyDualityTasteGate_single_carrier_alignment_decode_encode U,
        PriestleyDualityTasteGate_single_carrier_alignment_decode_encode O,
        PriestleyDualityTasteGate_single_carrier_alignment_decode_encode H,
        PriestleyDualityTasteGate_single_carrier_alignment_decode_encode C,
        PriestleyDualityTasteGate_single_carrier_alignment_decode_encode G,
        PriestleyDualityTasteGate_single_carrier_alignment_decode_encode N]

private theorem PriestleyDualityTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : PriestleyDualityUp} :
    priestleyDualityToEventFlow x = priestleyDualityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      priestleyDualityFromEventFlow (priestleyDualityToEventFlow x) =
        priestleyDualityFromEventFlow (priestleyDualityToEventFlow y) :=
    congrArg priestleyDualityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (PriestleyDualityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (PriestleyDualityTasteGate_single_carrier_alignment_round_trip y)))

instance priestleyDualityBHistCarrier : BHistCarrier PriestleyDualityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := priestleyDualityToEventFlow
  fromEventFlow := priestleyDualityFromEventFlow

instance priestleyDualityChapterTasteGate :
    ChapterTasteGate PriestleyDualityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change priestleyDualityFromEventFlow (priestleyDualityToEventFlow x) = some x
    exact PriestleyDualityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (PriestleyDualityTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem PriestleyDualityTasteGate_single_carrier_alignment :
    (∀ h : BHist, priestleyDualityDecodeBHist (priestleyDualityEncodeBHist h) = h) ∧
      (∀ x : PriestleyDualityUp,
        priestleyDualityFromEventFlow (priestleyDualityToEventFlow x) = some x) ∧
        (∀ x y : PriestleyDualityUp,
          priestleyDualityToEventFlow x = priestleyDualityToEventFlow y → x = y) ∧
          priestleyDualityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨PriestleyDualityTasteGate_single_carrier_alignment_decode_encode,
      PriestleyDualityTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        PriestleyDualityTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.PriestleyDualityUp
