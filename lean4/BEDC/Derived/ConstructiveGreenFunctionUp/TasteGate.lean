import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ConstructiveGreenFunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ConstructiveGreenFunctionUp : Type where
  | mk (D B R K S M H C P N : BHist) : ConstructiveGreenFunctionUp
  deriving DecidableEq

def constructiveGreenFunctionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: constructiveGreenFunctionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: constructiveGreenFunctionEncodeBHist h

def constructiveGreenFunctionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (constructiveGreenFunctionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (constructiveGreenFunctionDecodeBHist tail)

private theorem ConstructiveGreenFunctionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      constructiveGreenFunctionDecodeBHist (constructiveGreenFunctionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def constructiveGreenFunctionToEventFlow : ConstructiveGreenFunctionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ConstructiveGreenFunctionUp.mk D B R K S M H C P N =>
      [constructiveGreenFunctionEncodeBHist D,
        constructiveGreenFunctionEncodeBHist B,
        constructiveGreenFunctionEncodeBHist R,
        constructiveGreenFunctionEncodeBHist K,
        constructiveGreenFunctionEncodeBHist S,
        constructiveGreenFunctionEncodeBHist M,
        constructiveGreenFunctionEncodeBHist H,
        constructiveGreenFunctionEncodeBHist C,
        constructiveGreenFunctionEncodeBHist P,
        constructiveGreenFunctionEncodeBHist N]

private def constructiveGreenFunctionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => constructiveGreenFunctionEventAtDefault index rest

def constructiveGreenFunctionFromEventFlow
    (ef : EventFlow) : Option ConstructiveGreenFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ConstructiveGreenFunctionUp.mk
      (constructiveGreenFunctionDecodeBHist (constructiveGreenFunctionEventAtDefault 0 ef))
      (constructiveGreenFunctionDecodeBHist (constructiveGreenFunctionEventAtDefault 1 ef))
      (constructiveGreenFunctionDecodeBHist (constructiveGreenFunctionEventAtDefault 2 ef))
      (constructiveGreenFunctionDecodeBHist (constructiveGreenFunctionEventAtDefault 3 ef))
      (constructiveGreenFunctionDecodeBHist (constructiveGreenFunctionEventAtDefault 4 ef))
      (constructiveGreenFunctionDecodeBHist (constructiveGreenFunctionEventAtDefault 5 ef))
      (constructiveGreenFunctionDecodeBHist (constructiveGreenFunctionEventAtDefault 6 ef))
      (constructiveGreenFunctionDecodeBHist (constructiveGreenFunctionEventAtDefault 7 ef))
      (constructiveGreenFunctionDecodeBHist (constructiveGreenFunctionEventAtDefault 8 ef))
      (constructiveGreenFunctionDecodeBHist (constructiveGreenFunctionEventAtDefault 9 ef)))

private theorem ConstructiveGreenFunctionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ConstructiveGreenFunctionUp,
      constructiveGreenFunctionFromEventFlow (constructiveGreenFunctionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D B R K S M H C P N =>
      change
        some
          (ConstructiveGreenFunctionUp.mk
            (constructiveGreenFunctionDecodeBHist (constructiveGreenFunctionEncodeBHist D))
            (constructiveGreenFunctionDecodeBHist (constructiveGreenFunctionEncodeBHist B))
            (constructiveGreenFunctionDecodeBHist (constructiveGreenFunctionEncodeBHist R))
            (constructiveGreenFunctionDecodeBHist (constructiveGreenFunctionEncodeBHist K))
            (constructiveGreenFunctionDecodeBHist (constructiveGreenFunctionEncodeBHist S))
            (constructiveGreenFunctionDecodeBHist (constructiveGreenFunctionEncodeBHist M))
            (constructiveGreenFunctionDecodeBHist (constructiveGreenFunctionEncodeBHist H))
            (constructiveGreenFunctionDecodeBHist (constructiveGreenFunctionEncodeBHist C))
            (constructiveGreenFunctionDecodeBHist (constructiveGreenFunctionEncodeBHist P))
            (constructiveGreenFunctionDecodeBHist (constructiveGreenFunctionEncodeBHist N))) =
          some (ConstructiveGreenFunctionUp.mk D B R K S M H C P N)
      rw [ConstructiveGreenFunctionTasteGate_single_carrier_alignment_decode D,
        ConstructiveGreenFunctionTasteGate_single_carrier_alignment_decode B,
        ConstructiveGreenFunctionTasteGate_single_carrier_alignment_decode R,
        ConstructiveGreenFunctionTasteGate_single_carrier_alignment_decode K,
        ConstructiveGreenFunctionTasteGate_single_carrier_alignment_decode S,
        ConstructiveGreenFunctionTasteGate_single_carrier_alignment_decode M,
        ConstructiveGreenFunctionTasteGate_single_carrier_alignment_decode H,
        ConstructiveGreenFunctionTasteGate_single_carrier_alignment_decode C,
        ConstructiveGreenFunctionTasteGate_single_carrier_alignment_decode P,
        ConstructiveGreenFunctionTasteGate_single_carrier_alignment_decode N]

private theorem ConstructiveGreenFunctionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ConstructiveGreenFunctionUp} :
    constructiveGreenFunctionToEventFlow x = constructiveGreenFunctionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      constructiveGreenFunctionFromEventFlow (constructiveGreenFunctionToEventFlow x) =
        constructiveGreenFunctionFromEventFlow (constructiveGreenFunctionToEventFlow y) :=
    congrArg constructiveGreenFunctionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ConstructiveGreenFunctionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ConstructiveGreenFunctionTasteGate_single_carrier_alignment_round_trip y)))

instance constructiveGreenFunctionBHistCarrier :
    BHistCarrier ConstructiveGreenFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := constructiveGreenFunctionToEventFlow
  fromEventFlow := constructiveGreenFunctionFromEventFlow

instance constructiveGreenFunctionChapterTasteGate :
    ChapterTasteGate ConstructiveGreenFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      constructiveGreenFunctionFromEventFlow (constructiveGreenFunctionToEventFlow x) =
        some x
    exact ConstructiveGreenFunctionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact
      hxy (ConstructiveGreenFunctionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate ConstructiveGreenFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  constructiveGreenFunctionChapterTasteGate

theorem ConstructiveGreenFunctionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        constructiveGreenFunctionDecodeBHist (constructiveGreenFunctionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier ConstructiveGreenFunctionUp) ∧
        Nonempty (ChapterTasteGate ConstructiveGreenFunctionUp) ∧
          constructiveGreenFunctionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨ConstructiveGreenFunctionTasteGate_single_carrier_alignment_decode,
      ⟨constructiveGreenFunctionBHistCarrier⟩,
      ⟨constructiveGreenFunctionChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.ConstructiveGreenFunctionUp
