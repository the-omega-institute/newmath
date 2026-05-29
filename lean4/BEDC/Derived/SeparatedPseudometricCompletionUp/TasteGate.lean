import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SeparatedPseudometricCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SeparatedPseudometricCompletionUp : Type where
  | mk (P Z Q M S R D E H C K N : BHist) : SeparatedPseudometricCompletionUp
  deriving DecidableEq

def separatedPseudometricCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: separatedPseudometricCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: separatedPseudometricCompletionEncodeBHist h

def separatedPseudometricCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (separatedPseudometricCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (separatedPseudometricCompletionDecodeBHist tail)

private theorem SeparatedPseudometricCompletionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      separatedPseudometricCompletionDecodeBHist
        (separatedPseudometricCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def separatedPseudometricCompletionToEventFlow :
    SeparatedPseudometricCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SeparatedPseudometricCompletionUp.mk P Z Q M S R D E H C K N =>
      [separatedPseudometricCompletionEncodeBHist P,
        separatedPseudometricCompletionEncodeBHist Z,
        separatedPseudometricCompletionEncodeBHist Q,
        separatedPseudometricCompletionEncodeBHist M,
        separatedPseudometricCompletionEncodeBHist S,
        separatedPseudometricCompletionEncodeBHist R,
        separatedPseudometricCompletionEncodeBHist D,
        separatedPseudometricCompletionEncodeBHist E,
        separatedPseudometricCompletionEncodeBHist H,
        separatedPseudometricCompletionEncodeBHist C,
        separatedPseudometricCompletionEncodeBHist K,
        separatedPseudometricCompletionEncodeBHist N]

private def separatedPseudometricCompletionEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      separatedPseudometricCompletionEventAtDefault index rest

def separatedPseudometricCompletionFromEventFlow
    (ef : EventFlow) : Option SeparatedPseudometricCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SeparatedPseudometricCompletionUp.mk
      (separatedPseudometricCompletionDecodeBHist
        (separatedPseudometricCompletionEventAtDefault 0 ef))
      (separatedPseudometricCompletionDecodeBHist
        (separatedPseudometricCompletionEventAtDefault 1 ef))
      (separatedPseudometricCompletionDecodeBHist
        (separatedPseudometricCompletionEventAtDefault 2 ef))
      (separatedPseudometricCompletionDecodeBHist
        (separatedPseudometricCompletionEventAtDefault 3 ef))
      (separatedPseudometricCompletionDecodeBHist
        (separatedPseudometricCompletionEventAtDefault 4 ef))
      (separatedPseudometricCompletionDecodeBHist
        (separatedPseudometricCompletionEventAtDefault 5 ef))
      (separatedPseudometricCompletionDecodeBHist
        (separatedPseudometricCompletionEventAtDefault 6 ef))
      (separatedPseudometricCompletionDecodeBHist
        (separatedPseudometricCompletionEventAtDefault 7 ef))
      (separatedPseudometricCompletionDecodeBHist
        (separatedPseudometricCompletionEventAtDefault 8 ef))
      (separatedPseudometricCompletionDecodeBHist
        (separatedPseudometricCompletionEventAtDefault 9 ef))
      (separatedPseudometricCompletionDecodeBHist
        (separatedPseudometricCompletionEventAtDefault 10 ef))
      (separatedPseudometricCompletionDecodeBHist
        (separatedPseudometricCompletionEventAtDefault 11 ef)))

private theorem SeparatedPseudometricCompletionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SeparatedPseudometricCompletionUp,
      separatedPseudometricCompletionFromEventFlow
        (separatedPseudometricCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk P Z Q M S R D E H C K N =>
      change
        some
          (SeparatedPseudometricCompletionUp.mk
            (separatedPseudometricCompletionDecodeBHist
              (separatedPseudometricCompletionEncodeBHist P))
            (separatedPseudometricCompletionDecodeBHist
              (separatedPseudometricCompletionEncodeBHist Z))
            (separatedPseudometricCompletionDecodeBHist
              (separatedPseudometricCompletionEncodeBHist Q))
            (separatedPseudometricCompletionDecodeBHist
              (separatedPseudometricCompletionEncodeBHist M))
            (separatedPseudometricCompletionDecodeBHist
              (separatedPseudometricCompletionEncodeBHist S))
            (separatedPseudometricCompletionDecodeBHist
              (separatedPseudometricCompletionEncodeBHist R))
            (separatedPseudometricCompletionDecodeBHist
              (separatedPseudometricCompletionEncodeBHist D))
            (separatedPseudometricCompletionDecodeBHist
              (separatedPseudometricCompletionEncodeBHist E))
            (separatedPseudometricCompletionDecodeBHist
              (separatedPseudometricCompletionEncodeBHist H))
            (separatedPseudometricCompletionDecodeBHist
              (separatedPseudometricCompletionEncodeBHist C))
            (separatedPseudometricCompletionDecodeBHist
              (separatedPseudometricCompletionEncodeBHist K))
            (separatedPseudometricCompletionDecodeBHist
              (separatedPseudometricCompletionEncodeBHist N))) =
          some (SeparatedPseudometricCompletionUp.mk P Z Q M S R D E H C K N)
      rw [SeparatedPseudometricCompletionTasteGate_single_carrier_alignment_decode P,
        SeparatedPseudometricCompletionTasteGate_single_carrier_alignment_decode Z,
        SeparatedPseudometricCompletionTasteGate_single_carrier_alignment_decode Q,
        SeparatedPseudometricCompletionTasteGate_single_carrier_alignment_decode M,
        SeparatedPseudometricCompletionTasteGate_single_carrier_alignment_decode S,
        SeparatedPseudometricCompletionTasteGate_single_carrier_alignment_decode R,
        SeparatedPseudometricCompletionTasteGate_single_carrier_alignment_decode D,
        SeparatedPseudometricCompletionTasteGate_single_carrier_alignment_decode E,
        SeparatedPseudometricCompletionTasteGate_single_carrier_alignment_decode H,
        SeparatedPseudometricCompletionTasteGate_single_carrier_alignment_decode C,
        SeparatedPseudometricCompletionTasteGate_single_carrier_alignment_decode K,
        SeparatedPseudometricCompletionTasteGate_single_carrier_alignment_decode N]

private theorem SeparatedPseudometricCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SeparatedPseudometricCompletionUp} :
    separatedPseudometricCompletionToEventFlow x =
        separatedPseudometricCompletionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      separatedPseudometricCompletionFromEventFlow
          (separatedPseudometricCompletionToEventFlow x) =
        separatedPseudometricCompletionFromEventFlow
          (separatedPseudometricCompletionToEventFlow y) :=
    congrArg separatedPseudometricCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (SeparatedPseudometricCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SeparatedPseudometricCompletionTasteGate_single_carrier_alignment_round_trip y)))

instance separatedPseudometricCompletionBHistCarrier :
    BHistCarrier SeparatedPseudometricCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := separatedPseudometricCompletionToEventFlow
  fromEventFlow := separatedPseudometricCompletionFromEventFlow

instance separatedPseudometricCompletionChapterTasteGate :
    ChapterTasteGate SeparatedPseudometricCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      separatedPseudometricCompletionFromEventFlow
        (separatedPseudometricCompletionToEventFlow x) = some x
    exact SeparatedPseudometricCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (SeparatedPseudometricCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate SeparatedPseudometricCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  separatedPseudometricCompletionChapterTasteGate

theorem SeparatedPseudometricCompletionTasteGate_single_carrier_alignment :
    ChapterTasteGate SeparatedPseudometricCompletionUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact separatedPseudometricCompletionChapterTasteGate

end BEDC.Derived.SeparatedPseudometricCompletionUp
