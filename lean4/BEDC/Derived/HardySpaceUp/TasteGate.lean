import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HardySpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HardySpaceUp : Type where
  | mk (C B A S R D E T J K P N : BHist) : HardySpaceUp
  deriving DecidableEq

def hardySpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hardySpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hardySpaceEncodeBHist h

def hardySpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hardySpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hardySpaceDecodeBHist tail)

private theorem HardySpaceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, hardySpaceDecodeBHist (hardySpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hardySpaceFields : HardySpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HardySpaceUp.mk C B A S R D E T J K P N => [C, B, A, S, R, D, E, T, J, K, P, N]

def hardySpaceToEventFlow : HardySpaceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (hardySpaceFields x).map hardySpaceEncodeBHist

private def hardySpaceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => hardySpaceEventAtDefault index rest

def hardySpaceFromEventFlow (ef : EventFlow) : Option HardySpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HardySpaceUp.mk
      (hardySpaceDecodeBHist (hardySpaceEventAtDefault 0 ef))
      (hardySpaceDecodeBHist (hardySpaceEventAtDefault 1 ef))
      (hardySpaceDecodeBHist (hardySpaceEventAtDefault 2 ef))
      (hardySpaceDecodeBHist (hardySpaceEventAtDefault 3 ef))
      (hardySpaceDecodeBHist (hardySpaceEventAtDefault 4 ef))
      (hardySpaceDecodeBHist (hardySpaceEventAtDefault 5 ef))
      (hardySpaceDecodeBHist (hardySpaceEventAtDefault 6 ef))
      (hardySpaceDecodeBHist (hardySpaceEventAtDefault 7 ef))
      (hardySpaceDecodeBHist (hardySpaceEventAtDefault 8 ef))
      (hardySpaceDecodeBHist (hardySpaceEventAtDefault 9 ef))
      (hardySpaceDecodeBHist (hardySpaceEventAtDefault 10 ef))
      (hardySpaceDecodeBHist (hardySpaceEventAtDefault 11 ef)))

private theorem HardySpaceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : HardySpaceUp, hardySpaceFromEventFlow (hardySpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk C B A S R D E T J K P N =>
      change
        some
          (HardySpaceUp.mk
            (hardySpaceDecodeBHist (hardySpaceEncodeBHist C))
            (hardySpaceDecodeBHist (hardySpaceEncodeBHist B))
            (hardySpaceDecodeBHist (hardySpaceEncodeBHist A))
            (hardySpaceDecodeBHist (hardySpaceEncodeBHist S))
            (hardySpaceDecodeBHist (hardySpaceEncodeBHist R))
            (hardySpaceDecodeBHist (hardySpaceEncodeBHist D))
            (hardySpaceDecodeBHist (hardySpaceEncodeBHist E))
            (hardySpaceDecodeBHist (hardySpaceEncodeBHist T))
            (hardySpaceDecodeBHist (hardySpaceEncodeBHist J))
            (hardySpaceDecodeBHist (hardySpaceEncodeBHist K))
            (hardySpaceDecodeBHist (hardySpaceEncodeBHist P))
            (hardySpaceDecodeBHist (hardySpaceEncodeBHist N))) =
          some (HardySpaceUp.mk C B A S R D E T J K P N)
      rw [HardySpaceTasteGate_single_carrier_alignment_decode C,
        HardySpaceTasteGate_single_carrier_alignment_decode B,
        HardySpaceTasteGate_single_carrier_alignment_decode A,
        HardySpaceTasteGate_single_carrier_alignment_decode S,
        HardySpaceTasteGate_single_carrier_alignment_decode R,
        HardySpaceTasteGate_single_carrier_alignment_decode D,
        HardySpaceTasteGate_single_carrier_alignment_decode E,
        HardySpaceTasteGate_single_carrier_alignment_decode T,
        HardySpaceTasteGate_single_carrier_alignment_decode J,
        HardySpaceTasteGate_single_carrier_alignment_decode K,
        HardySpaceTasteGate_single_carrier_alignment_decode P,
        HardySpaceTasteGate_single_carrier_alignment_decode N]

private theorem HardySpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : HardySpaceUp} :
    hardySpaceToEventFlow x = hardySpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hardySpaceFromEventFlow (hardySpaceToEventFlow x) =
        hardySpaceFromEventFlow (hardySpaceToEventFlow y) :=
    congrArg hardySpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (HardySpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (HardySpaceTasteGate_single_carrier_alignment_round_trip y)))

instance hardySpaceBHistCarrier : BHistCarrier HardySpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hardySpaceToEventFlow
  fromEventFlow := hardySpaceFromEventFlow

instance hardySpaceChapterTasteGate : ChapterTasteGate HardySpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hardySpaceFromEventFlow (hardySpaceToEventFlow x) = some x
    exact HardySpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HardySpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate HardySpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hardySpaceChapterTasteGate

theorem HardySpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, hardySpaceDecodeBHist (hardySpaceEncodeBHist h) = h) ∧
      (∀ x : HardySpaceUp, hardySpaceFromEventFlow (hardySpaceToEventFlow x) = some x) ∧
        (∀ x y : HardySpaceUp, hardySpaceToEventFlow x = hardySpaceToEventFlow y → x = y) ∧
          hardySpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨HardySpaceTasteGate_single_carrier_alignment_decode,
      HardySpaceTasteGate_single_carrier_alignment_round_trip,
      fun x y hxy => HardySpaceTasteGate_single_carrier_alignment_toEventFlow_injective hxy,
      rfl⟩

end BEDC.Derived.HardySpaceUp
