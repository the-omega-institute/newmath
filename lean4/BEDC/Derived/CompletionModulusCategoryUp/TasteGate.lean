import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompletionModulusCategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompletionModulusCategoryUp : Type where
  | mk (O A S R D E F H C P N : BHist) : CompletionModulusCategoryUp
  deriving DecidableEq

private def completionModulusCategoryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: completionModulusCategoryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: completionModulusCategoryEncodeBHist h

private def completionModulusCategoryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (completionModulusCategoryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (completionModulusCategoryDecodeBHist tail)

private theorem CompletionModulusCategoryTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      completionModulusCategoryDecodeBHist (completionModulusCategoryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def completionModulusCategoryFields :
    CompletionModulusCategoryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompletionModulusCategoryUp.mk O A S R D E F H C P N =>
      [O, A, S, R, D, E, F, H, C, P, N]

private def completionModulusCategoryToEventFlow :
    CompletionModulusCategoryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (completionModulusCategoryFields x).map completionModulusCategoryEncodeBHist

private def completionModulusCategoryEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => completionModulusCategoryEventAt index rest

private def completionModulusCategoryFromEventFlow
    (ef : EventFlow) : Option CompletionModulusCategoryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompletionModulusCategoryUp.mk
      (completionModulusCategoryDecodeBHist (completionModulusCategoryEventAt 0 ef))
      (completionModulusCategoryDecodeBHist (completionModulusCategoryEventAt 1 ef))
      (completionModulusCategoryDecodeBHist (completionModulusCategoryEventAt 2 ef))
      (completionModulusCategoryDecodeBHist (completionModulusCategoryEventAt 3 ef))
      (completionModulusCategoryDecodeBHist (completionModulusCategoryEventAt 4 ef))
      (completionModulusCategoryDecodeBHist (completionModulusCategoryEventAt 5 ef))
      (completionModulusCategoryDecodeBHist (completionModulusCategoryEventAt 6 ef))
      (completionModulusCategoryDecodeBHist (completionModulusCategoryEventAt 7 ef))
      (completionModulusCategoryDecodeBHist (completionModulusCategoryEventAt 8 ef))
      (completionModulusCategoryDecodeBHist (completionModulusCategoryEventAt 9 ef))
      (completionModulusCategoryDecodeBHist (completionModulusCategoryEventAt 10 ef)))

private theorem CompletionModulusCategoryTasteGate_single_carrier_alignment_round_trip
    (x : CompletionModulusCategoryUp) :
    completionModulusCategoryFromEventFlow (completionModulusCategoryToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk O A S R D E F H C P N =>
      change
        some
          (CompletionModulusCategoryUp.mk
            (completionModulusCategoryDecodeBHist (completionModulusCategoryEncodeBHist O))
            (completionModulusCategoryDecodeBHist (completionModulusCategoryEncodeBHist A))
            (completionModulusCategoryDecodeBHist (completionModulusCategoryEncodeBHist S))
            (completionModulusCategoryDecodeBHist (completionModulusCategoryEncodeBHist R))
            (completionModulusCategoryDecodeBHist (completionModulusCategoryEncodeBHist D))
            (completionModulusCategoryDecodeBHist (completionModulusCategoryEncodeBHist E))
            (completionModulusCategoryDecodeBHist (completionModulusCategoryEncodeBHist F))
            (completionModulusCategoryDecodeBHist (completionModulusCategoryEncodeBHist H))
            (completionModulusCategoryDecodeBHist (completionModulusCategoryEncodeBHist C))
            (completionModulusCategoryDecodeBHist (completionModulusCategoryEncodeBHist P))
            (completionModulusCategoryDecodeBHist (completionModulusCategoryEncodeBHist N))) =
          some (CompletionModulusCategoryUp.mk O A S R D E F H C P N)
      rw [CompletionModulusCategoryTasteGate_single_carrier_alignment_decode_encode O,
        CompletionModulusCategoryTasteGate_single_carrier_alignment_decode_encode A,
        CompletionModulusCategoryTasteGate_single_carrier_alignment_decode_encode S,
        CompletionModulusCategoryTasteGate_single_carrier_alignment_decode_encode R,
        CompletionModulusCategoryTasteGate_single_carrier_alignment_decode_encode D,
        CompletionModulusCategoryTasteGate_single_carrier_alignment_decode_encode E,
        CompletionModulusCategoryTasteGate_single_carrier_alignment_decode_encode F,
        CompletionModulusCategoryTasteGate_single_carrier_alignment_decode_encode H,
        CompletionModulusCategoryTasteGate_single_carrier_alignment_decode_encode C,
        CompletionModulusCategoryTasteGate_single_carrier_alignment_decode_encode P,
        CompletionModulusCategoryTasteGate_single_carrier_alignment_decode_encode N]

private theorem CompletionModulusCategoryTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompletionModulusCategoryUp} :
    completionModulusCategoryToEventFlow x = completionModulusCategoryToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      completionModulusCategoryFromEventFlow (completionModulusCategoryToEventFlow x) =
        completionModulusCategoryFromEventFlow (completionModulusCategoryToEventFlow y) :=
    congrArg completionModulusCategoryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CompletionModulusCategoryTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompletionModulusCategoryTasteGate_single_carrier_alignment_round_trip y)))

instance completionModulusCategoryBHistCarrier :
    BHistCarrier CompletionModulusCategoryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := completionModulusCategoryToEventFlow
  fromEventFlow := completionModulusCategoryFromEventFlow

instance completionModulusCategoryChapterTasteGate :
    ChapterTasteGate CompletionModulusCategoryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change completionModulusCategoryFromEventFlow
      (completionModulusCategoryToEventFlow x) = some x
    exact CompletionModulusCategoryTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CompletionModulusCategoryTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CompletionModulusCategoryTasteGate_single_carrier_alignment :
    ChapterTasteGate CompletionModulusCategoryUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact completionModulusCategoryChapterTasteGate

end BEDC.Derived.CompletionModulusCategoryUp
