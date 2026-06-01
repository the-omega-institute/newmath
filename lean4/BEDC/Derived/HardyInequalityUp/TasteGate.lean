import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HardyInequalityUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HardyInequalityUp : Type where
  | mk (A W S Q D U E T J K P N : BHist) : HardyInequalityUp
  deriving DecidableEq

def hardyInequalityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hardyInequalityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hardyInequalityEncodeBHist h

def hardyInequalityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hardyInequalityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hardyInequalityDecodeBHist tail)

private theorem HardyInequalityTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, hardyInequalityDecodeBHist (hardyInequalityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hardyInequalityFields : HardyInequalityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HardyInequalityUp.mk A W S Q D U E T J K P N => [A, W, S, Q, D, U, E, T, J, K, P, N]

def hardyInequalityToEventFlow : HardyInequalityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (hardyInequalityFields x).map hardyInequalityEncodeBHist

private def hardyInequalityEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => hardyInequalityEventAt index rest

def hardyInequalityFromEventFlow (ef : EventFlow) : Option HardyInequalityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HardyInequalityUp.mk
      (hardyInequalityDecodeBHist (hardyInequalityEventAt 0 ef))
      (hardyInequalityDecodeBHist (hardyInequalityEventAt 1 ef))
      (hardyInequalityDecodeBHist (hardyInequalityEventAt 2 ef))
      (hardyInequalityDecodeBHist (hardyInequalityEventAt 3 ef))
      (hardyInequalityDecodeBHist (hardyInequalityEventAt 4 ef))
      (hardyInequalityDecodeBHist (hardyInequalityEventAt 5 ef))
      (hardyInequalityDecodeBHist (hardyInequalityEventAt 6 ef))
      (hardyInequalityDecodeBHist (hardyInequalityEventAt 7 ef))
      (hardyInequalityDecodeBHist (hardyInequalityEventAt 8 ef))
      (hardyInequalityDecodeBHist (hardyInequalityEventAt 9 ef))
      (hardyInequalityDecodeBHist (hardyInequalityEventAt 10 ef))
      (hardyInequalityDecodeBHist (hardyInequalityEventAt 11 ef)))

private theorem HardyInequalityTasteGate_single_carrier_alignment_round_trip :
    ∀ x : HardyInequalityUp,
      hardyInequalityFromEventFlow (hardyInequalityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A W S Q D U E T J K P N =>
      change
        some
            (HardyInequalityUp.mk
              (hardyInequalityDecodeBHist (hardyInequalityEncodeBHist A))
              (hardyInequalityDecodeBHist (hardyInequalityEncodeBHist W))
              (hardyInequalityDecodeBHist (hardyInequalityEncodeBHist S))
              (hardyInequalityDecodeBHist (hardyInequalityEncodeBHist Q))
              (hardyInequalityDecodeBHist (hardyInequalityEncodeBHist D))
              (hardyInequalityDecodeBHist (hardyInequalityEncodeBHist U))
              (hardyInequalityDecodeBHist (hardyInequalityEncodeBHist E))
              (hardyInequalityDecodeBHist (hardyInequalityEncodeBHist T))
              (hardyInequalityDecodeBHist (hardyInequalityEncodeBHist J))
              (hardyInequalityDecodeBHist (hardyInequalityEncodeBHist K))
              (hardyInequalityDecodeBHist (hardyInequalityEncodeBHist P))
              (hardyInequalityDecodeBHist (hardyInequalityEncodeBHist N))) =
          some (HardyInequalityUp.mk A W S Q D U E T J K P N)
      rw [HardyInequalityTasteGate_single_carrier_alignment_decode_encode A,
        HardyInequalityTasteGate_single_carrier_alignment_decode_encode W,
        HardyInequalityTasteGate_single_carrier_alignment_decode_encode S,
        HardyInequalityTasteGate_single_carrier_alignment_decode_encode Q,
        HardyInequalityTasteGate_single_carrier_alignment_decode_encode D,
        HardyInequalityTasteGate_single_carrier_alignment_decode_encode U,
        HardyInequalityTasteGate_single_carrier_alignment_decode_encode E,
        HardyInequalityTasteGate_single_carrier_alignment_decode_encode T,
        HardyInequalityTasteGate_single_carrier_alignment_decode_encode J,
        HardyInequalityTasteGate_single_carrier_alignment_decode_encode K,
        HardyInequalityTasteGate_single_carrier_alignment_decode_encode P,
        HardyInequalityTasteGate_single_carrier_alignment_decode_encode N]

private theorem HardyInequalityToEventFlow_injective {x y : HardyInequalityUp} :
    hardyInequalityToEventFlow x = hardyInequalityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hardyInequalityFromEventFlow (hardyInequalityToEventFlow x) =
        hardyInequalityFromEventFlow (hardyInequalityToEventFlow y) :=
    congrArg hardyInequalityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (HardyInequalityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (HardyInequalityTasteGate_single_carrier_alignment_round_trip y)))

instance hardyInequalityBHistCarrier : BHistCarrier HardyInequalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hardyInequalityToEventFlow
  fromEventFlow := hardyInequalityFromEventFlow

instance hardyInequalityChapterTasteGate : ChapterTasteGate HardyInequalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hardyInequalityFromEventFlow (hardyInequalityToEventFlow x) = some x
    exact HardyInequalityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HardyInequalityToEventFlow_injective heq)

def taste_gate : ChapterTasteGate HardyInequalityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hardyInequalityChapterTasteGate

theorem HardyInequalityTasteGate_single_carrier_alignment :
    (forall A W S Q D U E T J K P N : BHist,
      hardyInequalityFields (HardyInequalityUp.mk A W S Q D U E T J K P N) =
        [A, W, S, Q, D, U, E, T, J, K, P, N]) ∧
      hardyInequalityEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · intro A W S Q D U E T J K P N
    rfl
  · rfl

end BEDC.Derived.HardyInequalityUp.TasteGate
