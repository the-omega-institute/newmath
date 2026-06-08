import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompletionReflectorTriangleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompletionReflectorTriangleUp : Type where
  | mk (S U M Q I E R T H C P N : BHist) : CompletionReflectorTriangleUp
  deriving DecidableEq

def completionReflectorTriangleEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: completionReflectorTriangleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: completionReflectorTriangleEncodeBHist h

def completionReflectorTriangleDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (completionReflectorTriangleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (completionReflectorTriangleDecodeBHist tail)

private theorem completionReflectorTriangle_decode_encode_bhist :
    ∀ h : BHist,
      completionReflectorTriangleDecodeBHist
        (completionReflectorTriangleEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def completionReflectorTriangleToEventFlow :
    CompletionReflectorTriangleUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CompletionReflectorTriangleUp.mk S U M Q I E R T H C P N =>
      [completionReflectorTriangleEncodeBHist S,
        completionReflectorTriangleEncodeBHist U,
        completionReflectorTriangleEncodeBHist M,
        completionReflectorTriangleEncodeBHist Q,
        completionReflectorTriangleEncodeBHist I,
        completionReflectorTriangleEncodeBHist E,
        completionReflectorTriangleEncodeBHist R,
        completionReflectorTriangleEncodeBHist T,
        completionReflectorTriangleEncodeBHist H,
        completionReflectorTriangleEncodeBHist C,
        completionReflectorTriangleEncodeBHist P,
        completionReflectorTriangleEncodeBHist N]

private def completionReflectorTriangleEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => completionReflectorTriangleEventAtDefault index rest

def completionReflectorTriangleFromEventFlow
    (ef : EventFlow) : Option CompletionReflectorTriangleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompletionReflectorTriangleUp.mk
      (completionReflectorTriangleDecodeBHist
        (completionReflectorTriangleEventAtDefault 0 ef))
      (completionReflectorTriangleDecodeBHist
        (completionReflectorTriangleEventAtDefault 1 ef))
      (completionReflectorTriangleDecodeBHist
        (completionReflectorTriangleEventAtDefault 2 ef))
      (completionReflectorTriangleDecodeBHist
        (completionReflectorTriangleEventAtDefault 3 ef))
      (completionReflectorTriangleDecodeBHist
        (completionReflectorTriangleEventAtDefault 4 ef))
      (completionReflectorTriangleDecodeBHist
        (completionReflectorTriangleEventAtDefault 5 ef))
      (completionReflectorTriangleDecodeBHist
        (completionReflectorTriangleEventAtDefault 6 ef))
      (completionReflectorTriangleDecodeBHist
        (completionReflectorTriangleEventAtDefault 7 ef))
      (completionReflectorTriangleDecodeBHist
        (completionReflectorTriangleEventAtDefault 8 ef))
      (completionReflectorTriangleDecodeBHist
        (completionReflectorTriangleEventAtDefault 9 ef))
      (completionReflectorTriangleDecodeBHist
        (completionReflectorTriangleEventAtDefault 10 ef))
      (completionReflectorTriangleDecodeBHist
        (completionReflectorTriangleEventAtDefault 11 ef)))

private theorem completionReflectorTriangle_round_trip :
    ∀ x : CompletionReflectorTriangleUp,
      completionReflectorTriangleFromEventFlow
        (completionReflectorTriangleToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S U M Q I E R T H C P N =>
      change
        some
            (CompletionReflectorTriangleUp.mk
              (completionReflectorTriangleDecodeBHist
                (completionReflectorTriangleEncodeBHist S))
              (completionReflectorTriangleDecodeBHist
                (completionReflectorTriangleEncodeBHist U))
              (completionReflectorTriangleDecodeBHist
                (completionReflectorTriangleEncodeBHist M))
              (completionReflectorTriangleDecodeBHist
                (completionReflectorTriangleEncodeBHist Q))
              (completionReflectorTriangleDecodeBHist
                (completionReflectorTriangleEncodeBHist I))
              (completionReflectorTriangleDecodeBHist
                (completionReflectorTriangleEncodeBHist E))
              (completionReflectorTriangleDecodeBHist
                (completionReflectorTriangleEncodeBHist R))
              (completionReflectorTriangleDecodeBHist
                (completionReflectorTriangleEncodeBHist T))
              (completionReflectorTriangleDecodeBHist
                (completionReflectorTriangleEncodeBHist H))
              (completionReflectorTriangleDecodeBHist
                (completionReflectorTriangleEncodeBHist C))
              (completionReflectorTriangleDecodeBHist
                (completionReflectorTriangleEncodeBHist P))
              (completionReflectorTriangleDecodeBHist
                (completionReflectorTriangleEncodeBHist N))) =
          some (CompletionReflectorTriangleUp.mk S U M Q I E R T H C P N)
      rw [completionReflectorTriangle_decode_encode_bhist S,
        completionReflectorTriangle_decode_encode_bhist U,
        completionReflectorTriangle_decode_encode_bhist M,
        completionReflectorTriangle_decode_encode_bhist Q,
        completionReflectorTriangle_decode_encode_bhist I,
        completionReflectorTriangle_decode_encode_bhist E,
        completionReflectorTriangle_decode_encode_bhist R,
        completionReflectorTriangle_decode_encode_bhist T,
        completionReflectorTriangle_decode_encode_bhist H,
        completionReflectorTriangle_decode_encode_bhist C,
        completionReflectorTriangle_decode_encode_bhist P,
        completionReflectorTriangle_decode_encode_bhist N]

private theorem completionReflectorTriangleToEventFlow_injective
    {x y : CompletionReflectorTriangleUp} :
    completionReflectorTriangleToEventFlow x =
      completionReflectorTriangleToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      completionReflectorTriangleFromEventFlow
          (completionReflectorTriangleToEventFlow x) =
        completionReflectorTriangleFromEventFlow
          (completionReflectorTriangleToEventFlow y) :=
    congrArg completionReflectorTriangleFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (completionReflectorTriangle_round_trip x).symm
      (Eq.trans hread (completionReflectorTriangle_round_trip y)))

instance completionReflectorTriangleBHistCarrier :
    BHistCarrier CompletionReflectorTriangleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := completionReflectorTriangleToEventFlow
  fromEventFlow := completionReflectorTriangleFromEventFlow

instance completionReflectorTriangleChapterTasteGate :
    ChapterTasteGate CompletionReflectorTriangleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      completionReflectorTriangleFromEventFlow
        (completionReflectorTriangleToEventFlow x) = some x
    exact completionReflectorTriangle_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (completionReflectorTriangleToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CompletionReflectorTriangleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  completionReflectorTriangleChapterTasteGate

theorem CompletionReflectorTriangleTasteGate_single_carrier_alignment :
    completionReflectorTriangleEncodeBHist BHist.Empty = ([] : List BMark) ∧
      (∀ h : BHist,
        completionReflectorTriangleDecodeBHist
          (completionReflectorTriangleEncodeBHist h) = h) ∧
      (∀ x : CompletionReflectorTriangleUp,
        completionReflectorTriangleFromEventFlow
          (completionReflectorTriangleToEventFlow x) = some x) ∧
      (∀ x y : CompletionReflectorTriangleUp,
        completionReflectorTriangleToEventFlow x =
          completionReflectorTriangleToEventFlow y → x = y) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨rfl,
      completionReflectorTriangle_decode_encode_bhist,
      completionReflectorTriangle_round_trip,
      fun _ _ heq => completionReflectorTriangleToEventFlow_injective heq⟩

end BEDC.Derived.CompletionReflectorTriangleUp
