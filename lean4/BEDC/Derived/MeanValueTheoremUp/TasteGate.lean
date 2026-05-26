import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MeanValueTheoremUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MeanValueTheoremUp : Type where
  | mk (A B S F D R Q T H C P N : BHist) : MeanValueTheoremUp
  deriving DecidableEq

def meanValueTheoremEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: meanValueTheoremEncodeBHist h
  | BHist.e1 h => BMark.b1 :: meanValueTheoremEncodeBHist h

def meanValueTheoremDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (meanValueTheoremDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (meanValueTheoremDecodeBHist tail)

private theorem MeanValueTheoremTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, meanValueTheoremDecodeBHist (meanValueTheoremEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def meanValueTheoremFields : MeanValueTheoremUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MeanValueTheoremUp.mk A B S F D R Q T H C P N => [A, B, S, F, D, R, Q, T, H, C, P, N]

def meanValueTheoremToEventFlow : MeanValueTheoremUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (meanValueTheoremFields x).map meanValueTheoremEncodeBHist

private def meanValueTheoremEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => meanValueTheoremEventAtDefault index rest

def meanValueTheoremFromEventFlow (ef : EventFlow) : Option MeanValueTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MeanValueTheoremUp.mk
      (meanValueTheoremDecodeBHist (meanValueTheoremEventAtDefault 0 ef))
      (meanValueTheoremDecodeBHist (meanValueTheoremEventAtDefault 1 ef))
      (meanValueTheoremDecodeBHist (meanValueTheoremEventAtDefault 2 ef))
      (meanValueTheoremDecodeBHist (meanValueTheoremEventAtDefault 3 ef))
      (meanValueTheoremDecodeBHist (meanValueTheoremEventAtDefault 4 ef))
      (meanValueTheoremDecodeBHist (meanValueTheoremEventAtDefault 5 ef))
      (meanValueTheoremDecodeBHist (meanValueTheoremEventAtDefault 6 ef))
      (meanValueTheoremDecodeBHist (meanValueTheoremEventAtDefault 7 ef))
      (meanValueTheoremDecodeBHist (meanValueTheoremEventAtDefault 8 ef))
      (meanValueTheoremDecodeBHist (meanValueTheoremEventAtDefault 9 ef))
      (meanValueTheoremDecodeBHist (meanValueTheoremEventAtDefault 10 ef))
      (meanValueTheoremDecodeBHist (meanValueTheoremEventAtDefault 11 ef)))

private theorem MeanValueTheoremTasteGate_single_carrier_alignment_round_trip :
    ∀ x : MeanValueTheoremUp,
      meanValueTheoremFromEventFlow (meanValueTheoremToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A B S F D R Q T H C P N =>
      change
        some
          (MeanValueTheoremUp.mk
            (meanValueTheoremDecodeBHist (meanValueTheoremEncodeBHist A))
            (meanValueTheoremDecodeBHist (meanValueTheoremEncodeBHist B))
            (meanValueTheoremDecodeBHist (meanValueTheoremEncodeBHist S))
            (meanValueTheoremDecodeBHist (meanValueTheoremEncodeBHist F))
            (meanValueTheoremDecodeBHist (meanValueTheoremEncodeBHist D))
            (meanValueTheoremDecodeBHist (meanValueTheoremEncodeBHist R))
            (meanValueTheoremDecodeBHist (meanValueTheoremEncodeBHist Q))
            (meanValueTheoremDecodeBHist (meanValueTheoremEncodeBHist T))
            (meanValueTheoremDecodeBHist (meanValueTheoremEncodeBHist H))
            (meanValueTheoremDecodeBHist (meanValueTheoremEncodeBHist C))
            (meanValueTheoremDecodeBHist (meanValueTheoremEncodeBHist P))
            (meanValueTheoremDecodeBHist (meanValueTheoremEncodeBHist N))) =
          some (MeanValueTheoremUp.mk A B S F D R Q T H C P N)
      rw [MeanValueTheoremTasteGate_single_carrier_alignment_decode A,
        MeanValueTheoremTasteGate_single_carrier_alignment_decode B,
        MeanValueTheoremTasteGate_single_carrier_alignment_decode S,
        MeanValueTheoremTasteGate_single_carrier_alignment_decode F,
        MeanValueTheoremTasteGate_single_carrier_alignment_decode D,
        MeanValueTheoremTasteGate_single_carrier_alignment_decode R,
        MeanValueTheoremTasteGate_single_carrier_alignment_decode Q,
        MeanValueTheoremTasteGate_single_carrier_alignment_decode T,
        MeanValueTheoremTasteGate_single_carrier_alignment_decode H,
        MeanValueTheoremTasteGate_single_carrier_alignment_decode C,
        MeanValueTheoremTasteGate_single_carrier_alignment_decode P,
        MeanValueTheoremTasteGate_single_carrier_alignment_decode N]

private theorem MeanValueTheoremTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MeanValueTheoremUp} :
    meanValueTheoremToEventFlow x = meanValueTheoremToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      meanValueTheoremFromEventFlow (meanValueTheoremToEventFlow x) =
        meanValueTheoremFromEventFlow (meanValueTheoremToEventFlow y) :=
    congrArg meanValueTheoremFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (MeanValueTheoremTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (MeanValueTheoremTasteGate_single_carrier_alignment_round_trip y)))

instance meanValueTheoremBHistCarrier : BHistCarrier MeanValueTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := meanValueTheoremToEventFlow
  fromEventFlow := meanValueTheoremFromEventFlow

instance meanValueTheoremChapterTasteGate : ChapterTasteGate MeanValueTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change meanValueTheoremFromEventFlow (meanValueTheoremToEventFlow x) = some x
    exact MeanValueTheoremTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MeanValueTheoremTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate MeanValueTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  meanValueTheoremChapterTasteGate

theorem MeanValueTheoremTasteGate_single_carrier_alignment :
    (∀ h : BHist, meanValueTheoremDecodeBHist (meanValueTheoremEncodeBHist h) = h) ∧
      (∀ x : MeanValueTheoremUp,
        meanValueTheoremFromEventFlow (meanValueTheoremToEventFlow x) = some x) ∧
        (∀ x y : MeanValueTheoremUp,
          meanValueTheoremToEventFlow x = meanValueTheoremToEventFlow y → x = y) ∧
          meanValueTheoremEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨MeanValueTheoremTasteGate_single_carrier_alignment_decode,
      MeanValueTheoremTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        MeanValueTheoremTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.MeanValueTheoremUp
