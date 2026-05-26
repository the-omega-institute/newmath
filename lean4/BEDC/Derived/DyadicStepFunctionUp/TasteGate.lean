import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicStepFunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicStepFunctionUp : Type where
  | mk (Pi I V R M E L C P N : BHist) : DyadicStepFunctionUp
  deriving DecidableEq

def dyadicStepFunctionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicStepFunctionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicStepFunctionEncodeBHist h

def dyadicStepFunctionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicStepFunctionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicStepFunctionDecodeBHist tail)

private theorem dyadicStepFunction_decode_encode :
    ∀ h : BHist, dyadicStepFunctionDecodeBHist (dyadicStepFunctionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicStepFunctionToEventFlow : DyadicStepFunctionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicStepFunctionUp.mk Pi I V R M E L C P N =>
      [[BMark.b1, BMark.b0],
        dyadicStepFunctionEncodeBHist Pi,
        dyadicStepFunctionEncodeBHist I,
        dyadicStepFunctionEncodeBHist V,
        dyadicStepFunctionEncodeBHist R,
        dyadicStepFunctionEncodeBHist M,
        dyadicStepFunctionEncodeBHist E,
        dyadicStepFunctionEncodeBHist L,
        dyadicStepFunctionEncodeBHist C,
        dyadicStepFunctionEncodeBHist P,
        dyadicStepFunctionEncodeBHist N]

private def dyadicStepFunctionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dyadicStepFunctionEventAtDefault index rest

def dyadicStepFunctionFromEventFlow (ef : EventFlow) : Option DyadicStepFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DyadicStepFunctionUp.mk
      (dyadicStepFunctionDecodeBHist (dyadicStepFunctionEventAtDefault 1 ef))
      (dyadicStepFunctionDecodeBHist (dyadicStepFunctionEventAtDefault 2 ef))
      (dyadicStepFunctionDecodeBHist (dyadicStepFunctionEventAtDefault 3 ef))
      (dyadicStepFunctionDecodeBHist (dyadicStepFunctionEventAtDefault 4 ef))
      (dyadicStepFunctionDecodeBHist (dyadicStepFunctionEventAtDefault 5 ef))
      (dyadicStepFunctionDecodeBHist (dyadicStepFunctionEventAtDefault 6 ef))
      (dyadicStepFunctionDecodeBHist (dyadicStepFunctionEventAtDefault 7 ef))
      (dyadicStepFunctionDecodeBHist (dyadicStepFunctionEventAtDefault 8 ef))
      (dyadicStepFunctionDecodeBHist (dyadicStepFunctionEventAtDefault 9 ef))
      (dyadicStepFunctionDecodeBHist (dyadicStepFunctionEventAtDefault 10 ef)))

private theorem dyadicStepFunction_round_trip :
    ∀ x : DyadicStepFunctionUp,
      dyadicStepFunctionFromEventFlow (dyadicStepFunctionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Pi I V R M E L C P N =>
      change
        some
          (DyadicStepFunctionUp.mk
            (dyadicStepFunctionDecodeBHist (dyadicStepFunctionEncodeBHist Pi))
            (dyadicStepFunctionDecodeBHist (dyadicStepFunctionEncodeBHist I))
            (dyadicStepFunctionDecodeBHist (dyadicStepFunctionEncodeBHist V))
            (dyadicStepFunctionDecodeBHist (dyadicStepFunctionEncodeBHist R))
            (dyadicStepFunctionDecodeBHist (dyadicStepFunctionEncodeBHist M))
            (dyadicStepFunctionDecodeBHist (dyadicStepFunctionEncodeBHist E))
            (dyadicStepFunctionDecodeBHist (dyadicStepFunctionEncodeBHist L))
            (dyadicStepFunctionDecodeBHist (dyadicStepFunctionEncodeBHist C))
            (dyadicStepFunctionDecodeBHist (dyadicStepFunctionEncodeBHist P))
            (dyadicStepFunctionDecodeBHist (dyadicStepFunctionEncodeBHist N))) =
          some (DyadicStepFunctionUp.mk Pi I V R M E L C P N)
      rw [dyadicStepFunction_decode_encode Pi, dyadicStepFunction_decode_encode I,
        dyadicStepFunction_decode_encode V, dyadicStepFunction_decode_encode R,
        dyadicStepFunction_decode_encode M, dyadicStepFunction_decode_encode E,
        dyadicStepFunction_decode_encode L, dyadicStepFunction_decode_encode C,
        dyadicStepFunction_decode_encode P, dyadicStepFunction_decode_encode N]

private theorem dyadicStepFunctionToEventFlow_injective {x y : DyadicStepFunctionUp} :
    dyadicStepFunctionToEventFlow x = dyadicStepFunctionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x = dyadicStepFunctionFromEventFlow (dyadicStepFunctionToEventFlow x) :=
        (dyadicStepFunction_round_trip x).symm
      _ = dyadicStepFunctionFromEventFlow (dyadicStepFunctionToEventFlow y) :=
        congrArg dyadicStepFunctionFromEventFlow hxy
      _ = some y := dyadicStepFunction_round_trip y
  exact Option.some.inj optionEq

instance dyadicStepFunctionBHistCarrier : BHistCarrier DyadicStepFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicStepFunctionToEventFlow
  fromEventFlow := dyadicStepFunctionFromEventFlow

instance dyadicStepFunctionChapterTasteGate : ChapterTasteGate DyadicStepFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicStepFunctionFromEventFlow (dyadicStepFunctionToEventFlow x) = some x
    exact dyadicStepFunction_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dyadicStepFunctionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate DyadicStepFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicStepFunctionChapterTasteGate

theorem DyadicStepFunctionTasteGate_single_carrier_alignment :
    (∀ h : BHist, dyadicStepFunctionDecodeBHist (dyadicStepFunctionEncodeBHist h) = h) ∧
      (∀ x : DyadicStepFunctionUp,
        dyadicStepFunctionFromEventFlow (dyadicStepFunctionToEventFlow x) = some x) ∧
        (∀ x y : DyadicStepFunctionUp,
          dyadicStepFunctionToEventFlow x = dyadicStepFunctionToEventFlow y → x = y) ∧
          dyadicStepFunctionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨dyadicStepFunction_decode_encode, dyadicStepFunction_round_trip,
      (fun _ _ heq => dyadicStepFunctionToEventFlow_injective heq), rfl⟩

end BEDC.Derived.DyadicStepFunctionUp
