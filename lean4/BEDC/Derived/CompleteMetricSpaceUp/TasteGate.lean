import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompleteMetricSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompleteMetricSpaceUp : Type where
  | mk (M C E L U H T P N : BHist) : CompleteMetricSpaceUp
  deriving DecidableEq

def completeMetricSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: completeMetricSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: completeMetricSpaceEncodeBHist h

def completeMetricSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (completeMetricSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (completeMetricSpaceDecodeBHist tail)

private theorem completeMetricSpaceDecodeEncode :
    ∀ h : BHist, completeMetricSpaceDecodeBHist (completeMetricSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def completeMetricSpaceFields : CompleteMetricSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompleteMetricSpaceUp.mk M C E L U H T P N => [M, C, E, L, U, H, T, P, N]

def completeMetricSpaceToEventFlow : CompleteMetricSpaceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (completeMetricSpaceFields x).map completeMetricSpaceEncodeBHist

private def completeMetricSpaceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => completeMetricSpaceEventAtDefault index rest

def completeMetricSpaceFromEventFlow (ef : EventFlow) : Option CompleteMetricSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompleteMetricSpaceUp.mk
      (completeMetricSpaceDecodeBHist (completeMetricSpaceEventAtDefault 0 ef))
      (completeMetricSpaceDecodeBHist (completeMetricSpaceEventAtDefault 1 ef))
      (completeMetricSpaceDecodeBHist (completeMetricSpaceEventAtDefault 2 ef))
      (completeMetricSpaceDecodeBHist (completeMetricSpaceEventAtDefault 3 ef))
      (completeMetricSpaceDecodeBHist (completeMetricSpaceEventAtDefault 4 ef))
      (completeMetricSpaceDecodeBHist (completeMetricSpaceEventAtDefault 5 ef))
      (completeMetricSpaceDecodeBHist (completeMetricSpaceEventAtDefault 6 ef))
      (completeMetricSpaceDecodeBHist (completeMetricSpaceEventAtDefault 7 ef))
      (completeMetricSpaceDecodeBHist (completeMetricSpaceEventAtDefault 8 ef)))

private theorem completeMetricSpaceRoundTrip :
    ∀ x : CompleteMetricSpaceUp,
      completeMetricSpaceFromEventFlow (completeMetricSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M C E L U H T P N =>
      change
        some
          (CompleteMetricSpaceUp.mk
            (completeMetricSpaceDecodeBHist (completeMetricSpaceEncodeBHist M))
            (completeMetricSpaceDecodeBHist (completeMetricSpaceEncodeBHist C))
            (completeMetricSpaceDecodeBHist (completeMetricSpaceEncodeBHist E))
            (completeMetricSpaceDecodeBHist (completeMetricSpaceEncodeBHist L))
            (completeMetricSpaceDecodeBHist (completeMetricSpaceEncodeBHist U))
            (completeMetricSpaceDecodeBHist (completeMetricSpaceEncodeBHist H))
            (completeMetricSpaceDecodeBHist (completeMetricSpaceEncodeBHist T))
            (completeMetricSpaceDecodeBHist (completeMetricSpaceEncodeBHist P))
            (completeMetricSpaceDecodeBHist (completeMetricSpaceEncodeBHist N))) =
          some (CompleteMetricSpaceUp.mk M C E L U H T P N)
      rw [completeMetricSpaceDecodeEncode M, completeMetricSpaceDecodeEncode C,
        completeMetricSpaceDecodeEncode E, completeMetricSpaceDecodeEncode L,
        completeMetricSpaceDecodeEncode U, completeMetricSpaceDecodeEncode H,
        completeMetricSpaceDecodeEncode T, completeMetricSpaceDecodeEncode P,
        completeMetricSpaceDecodeEncode N]

private theorem completeMetricSpaceToEventFlow_injective {x y : CompleteMetricSpaceUp} :
    completeMetricSpaceToEventFlow x = completeMetricSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      completeMetricSpaceFromEventFlow (completeMetricSpaceToEventFlow x) =
        completeMetricSpaceFromEventFlow (completeMetricSpaceToEventFlow y) :=
    congrArg completeMetricSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (completeMetricSpaceRoundTrip x).symm
      (Eq.trans hread (completeMetricSpaceRoundTrip y)))

instance completeMetricSpaceBHistCarrier : BHistCarrier CompleteMetricSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := completeMetricSpaceToEventFlow
  fromEventFlow := completeMetricSpaceFromEventFlow

instance completeMetricSpaceChapterTasteGate : ChapterTasteGate CompleteMetricSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change completeMetricSpaceFromEventFlow (completeMetricSpaceToEventFlow x) = some x
    exact completeMetricSpaceRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (completeMetricSpaceToEventFlow_injective heq)

theorem CompleteMetricSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, completeMetricSpaceDecodeBHist (completeMetricSpaceEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CompleteMetricSpaceUp) ∧
        Nonempty (ChapterTasteGate CompleteMetricSpaceUp) ∧
          completeMetricSpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨completeMetricSpaceDecodeEncode,
      ⟨completeMetricSpaceBHistCarrier⟩,
      ⟨completeMetricSpaceChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.CompleteMetricSpaceUp
