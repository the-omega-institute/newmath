import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ConstructiveDiniTheoremUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ConstructiveDiniTheoremUp : Type where
  | mk (K F M D U W R E H C P N : BHist) : ConstructiveDiniTheoremUp
  deriving DecidableEq

def constructiveDiniTheoremEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: constructiveDiniTheoremEncodeBHist h
  | BHist.e1 h => BMark.b1 :: constructiveDiniTheoremEncodeBHist h

def constructiveDiniTheoremDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (constructiveDiniTheoremDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (constructiveDiniTheoremDecodeBHist tail)

private theorem ConstructiveDiniTheoremTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      constructiveDiniTheoremDecodeBHist (constructiveDiniTheoremEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def constructiveDiniTheoremToEventFlow : ConstructiveDiniTheoremUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ConstructiveDiniTheoremUp.mk K F M D U W R E H C P N =>
      [constructiveDiniTheoremEncodeBHist K,
        constructiveDiniTheoremEncodeBHist F,
        constructiveDiniTheoremEncodeBHist M,
        constructiveDiniTheoremEncodeBHist D,
        constructiveDiniTheoremEncodeBHist U,
        constructiveDiniTheoremEncodeBHist W,
        constructiveDiniTheoremEncodeBHist R,
        constructiveDiniTheoremEncodeBHist E,
        constructiveDiniTheoremEncodeBHist H,
        constructiveDiniTheoremEncodeBHist C,
        constructiveDiniTheoremEncodeBHist P,
        constructiveDiniTheoremEncodeBHist N]

private def constructiveDiniTheoremEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => constructiveDiniTheoremEventAtDefault index rest

def constructiveDiniTheoremFromEventFlow
    (ef : EventFlow) : Option ConstructiveDiniTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ConstructiveDiniTheoremUp.mk
      (constructiveDiniTheoremDecodeBHist (constructiveDiniTheoremEventAtDefault 0 ef))
      (constructiveDiniTheoremDecodeBHist (constructiveDiniTheoremEventAtDefault 1 ef))
      (constructiveDiniTheoremDecodeBHist (constructiveDiniTheoremEventAtDefault 2 ef))
      (constructiveDiniTheoremDecodeBHist (constructiveDiniTheoremEventAtDefault 3 ef))
      (constructiveDiniTheoremDecodeBHist (constructiveDiniTheoremEventAtDefault 4 ef))
      (constructiveDiniTheoremDecodeBHist (constructiveDiniTheoremEventAtDefault 5 ef))
      (constructiveDiniTheoremDecodeBHist (constructiveDiniTheoremEventAtDefault 6 ef))
      (constructiveDiniTheoremDecodeBHist (constructiveDiniTheoremEventAtDefault 7 ef))
      (constructiveDiniTheoremDecodeBHist (constructiveDiniTheoremEventAtDefault 8 ef))
      (constructiveDiniTheoremDecodeBHist (constructiveDiniTheoremEventAtDefault 9 ef))
      (constructiveDiniTheoremDecodeBHist (constructiveDiniTheoremEventAtDefault 10 ef))
      (constructiveDiniTheoremDecodeBHist (constructiveDiniTheoremEventAtDefault 11 ef)))

private theorem ConstructiveDiniTheoremTasteGate_single_carrier_alignment_round_trip
    (x : ConstructiveDiniTheoremUp) :
    constructiveDiniTheoremFromEventFlow (constructiveDiniTheoremToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk K F M D U W R E H C P N =>
      change
        some
          (ConstructiveDiniTheoremUp.mk
            (constructiveDiniTheoremDecodeBHist (constructiveDiniTheoremEncodeBHist K))
            (constructiveDiniTheoremDecodeBHist (constructiveDiniTheoremEncodeBHist F))
            (constructiveDiniTheoremDecodeBHist (constructiveDiniTheoremEncodeBHist M))
            (constructiveDiniTheoremDecodeBHist (constructiveDiniTheoremEncodeBHist D))
            (constructiveDiniTheoremDecodeBHist (constructiveDiniTheoremEncodeBHist U))
            (constructiveDiniTheoremDecodeBHist (constructiveDiniTheoremEncodeBHist W))
            (constructiveDiniTheoremDecodeBHist (constructiveDiniTheoremEncodeBHist R))
            (constructiveDiniTheoremDecodeBHist (constructiveDiniTheoremEncodeBHist E))
            (constructiveDiniTheoremDecodeBHist (constructiveDiniTheoremEncodeBHist H))
            (constructiveDiniTheoremDecodeBHist (constructiveDiniTheoremEncodeBHist C))
            (constructiveDiniTheoremDecodeBHist (constructiveDiniTheoremEncodeBHist P))
            (constructiveDiniTheoremDecodeBHist (constructiveDiniTheoremEncodeBHist N))) =
          some (ConstructiveDiniTheoremUp.mk K F M D U W R E H C P N)
      rw [ConstructiveDiniTheoremTasteGate_single_carrier_alignment_decode_encode K,
        ConstructiveDiniTheoremTasteGate_single_carrier_alignment_decode_encode F,
        ConstructiveDiniTheoremTasteGate_single_carrier_alignment_decode_encode M,
        ConstructiveDiniTheoremTasteGate_single_carrier_alignment_decode_encode D,
        ConstructiveDiniTheoremTasteGate_single_carrier_alignment_decode_encode U,
        ConstructiveDiniTheoremTasteGate_single_carrier_alignment_decode_encode W,
        ConstructiveDiniTheoremTasteGate_single_carrier_alignment_decode_encode R,
        ConstructiveDiniTheoremTasteGate_single_carrier_alignment_decode_encode E,
        ConstructiveDiniTheoremTasteGate_single_carrier_alignment_decode_encode H,
        ConstructiveDiniTheoremTasteGate_single_carrier_alignment_decode_encode C,
        ConstructiveDiniTheoremTasteGate_single_carrier_alignment_decode_encode P,
        ConstructiveDiniTheoremTasteGate_single_carrier_alignment_decode_encode N]

private theorem ConstructiveDiniTheoremTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ConstructiveDiniTheoremUp} :
    constructiveDiniTheoremToEventFlow x = constructiveDiniTheoremToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      constructiveDiniTheoremFromEventFlow (constructiveDiniTheoremToEventFlow x) =
        constructiveDiniTheoremFromEventFlow (constructiveDiniTheoremToEventFlow y) :=
    congrArg constructiveDiniTheoremFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ConstructiveDiniTheoremTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ConstructiveDiniTheoremTasteGate_single_carrier_alignment_round_trip y)))

instance constructiveDiniTheoremBHistCarrier :
    BHistCarrier ConstructiveDiniTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := constructiveDiniTheoremToEventFlow
  fromEventFlow := constructiveDiniTheoremFromEventFlow

instance constructiveDiniTheoremChapterTasteGate :
    ChapterTasteGate ConstructiveDiniTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change constructiveDiniTheoremFromEventFlow (constructiveDiniTheoremToEventFlow x) =
      some x
    exact ConstructiveDiniTheoremTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (ConstructiveDiniTheoremTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem ConstructiveDiniTheoremTasteGate_single_carrier_alignment :
    (∀ h : BHist, constructiveDiniTheoremDecodeBHist
      (constructiveDiniTheoremEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier ConstructiveDiniTheoremUp) ∧
        Nonempty (ChapterTasteGate ConstructiveDiniTheoremUp) ∧
          constructiveDiniTheoremEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨ConstructiveDiniTheoremTasteGate_single_carrier_alignment_decode_encode,
      ⟨constructiveDiniTheoremBHistCarrier⟩,
      ⟨constructiveDiniTheoremChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.ConstructiveDiniTheoremUp.TasteGate
