import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ConstructiveCauchyIntervalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ConstructiveCauchyIntervalUp : Type where
  | mk (L U O D S R E H C P N : BHist) : ConstructiveCauchyIntervalUp
  deriving DecidableEq

def constructiveCauchyIntervalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: constructiveCauchyIntervalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: constructiveCauchyIntervalEncodeBHist h

def constructiveCauchyIntervalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (constructiveCauchyIntervalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (constructiveCauchyIntervalDecodeBHist tail)

private theorem ConstructiveCauchyIntervalTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      constructiveCauchyIntervalDecodeBHist
          (constructiveCauchyIntervalEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def constructiveCauchyIntervalFields :
    ConstructiveCauchyIntervalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ConstructiveCauchyIntervalUp.mk L U O D S R E H C P N =>
      [L, U, O, D, S, R, E, H, C, P, N]

def constructiveCauchyIntervalToEventFlow :
    ConstructiveCauchyIntervalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (constructiveCauchyIntervalFields x).map constructiveCauchyIntervalEncodeBHist

private def constructiveCauchyIntervalEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => constructiveCauchyIntervalEventAtDefault index rest

def constructiveCauchyIntervalFromEventFlow
    (ef : EventFlow) : Option ConstructiveCauchyIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ConstructiveCauchyIntervalUp.mk
      (constructiveCauchyIntervalDecodeBHist
        (constructiveCauchyIntervalEventAtDefault 0 ef))
      (constructiveCauchyIntervalDecodeBHist
        (constructiveCauchyIntervalEventAtDefault 1 ef))
      (constructiveCauchyIntervalDecodeBHist
        (constructiveCauchyIntervalEventAtDefault 2 ef))
      (constructiveCauchyIntervalDecodeBHist
        (constructiveCauchyIntervalEventAtDefault 3 ef))
      (constructiveCauchyIntervalDecodeBHist
        (constructiveCauchyIntervalEventAtDefault 4 ef))
      (constructiveCauchyIntervalDecodeBHist
        (constructiveCauchyIntervalEventAtDefault 5 ef))
      (constructiveCauchyIntervalDecodeBHist
        (constructiveCauchyIntervalEventAtDefault 6 ef))
      (constructiveCauchyIntervalDecodeBHist
        (constructiveCauchyIntervalEventAtDefault 7 ef))
      (constructiveCauchyIntervalDecodeBHist
        (constructiveCauchyIntervalEventAtDefault 8 ef))
      (constructiveCauchyIntervalDecodeBHist
        (constructiveCauchyIntervalEventAtDefault 9 ef))
      (constructiveCauchyIntervalDecodeBHist
        (constructiveCauchyIntervalEventAtDefault 10 ef)))

private theorem ConstructiveCauchyIntervalTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ConstructiveCauchyIntervalUp,
      constructiveCauchyIntervalFromEventFlow
          (constructiveCauchyIntervalToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L U O D S R E H C P N =>
      change
        some
          (ConstructiveCauchyIntervalUp.mk
            (constructiveCauchyIntervalDecodeBHist (constructiveCauchyIntervalEncodeBHist L))
            (constructiveCauchyIntervalDecodeBHist (constructiveCauchyIntervalEncodeBHist U))
            (constructiveCauchyIntervalDecodeBHist (constructiveCauchyIntervalEncodeBHist O))
            (constructiveCauchyIntervalDecodeBHist (constructiveCauchyIntervalEncodeBHist D))
            (constructiveCauchyIntervalDecodeBHist (constructiveCauchyIntervalEncodeBHist S))
            (constructiveCauchyIntervalDecodeBHist (constructiveCauchyIntervalEncodeBHist R))
            (constructiveCauchyIntervalDecodeBHist (constructiveCauchyIntervalEncodeBHist E))
            (constructiveCauchyIntervalDecodeBHist (constructiveCauchyIntervalEncodeBHist H))
            (constructiveCauchyIntervalDecodeBHist (constructiveCauchyIntervalEncodeBHist C))
            (constructiveCauchyIntervalDecodeBHist (constructiveCauchyIntervalEncodeBHist P))
            (constructiveCauchyIntervalDecodeBHist
              (constructiveCauchyIntervalEncodeBHist N))) =
          some (ConstructiveCauchyIntervalUp.mk L U O D S R E H C P N)
      rw [ConstructiveCauchyIntervalTasteGate_single_carrier_alignment_decode L,
        ConstructiveCauchyIntervalTasteGate_single_carrier_alignment_decode U,
        ConstructiveCauchyIntervalTasteGate_single_carrier_alignment_decode O,
        ConstructiveCauchyIntervalTasteGate_single_carrier_alignment_decode D,
        ConstructiveCauchyIntervalTasteGate_single_carrier_alignment_decode S,
        ConstructiveCauchyIntervalTasteGate_single_carrier_alignment_decode R,
        ConstructiveCauchyIntervalTasteGate_single_carrier_alignment_decode E,
        ConstructiveCauchyIntervalTasteGate_single_carrier_alignment_decode H,
        ConstructiveCauchyIntervalTasteGate_single_carrier_alignment_decode C,
        ConstructiveCauchyIntervalTasteGate_single_carrier_alignment_decode P,
        ConstructiveCauchyIntervalTasteGate_single_carrier_alignment_decode N]

private theorem ConstructiveCauchyIntervalTasteGate_single_carrier_alignment_injective
    {x y : ConstructiveCauchyIntervalUp} :
    constructiveCauchyIntervalToEventFlow x =
        constructiveCauchyIntervalToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      constructiveCauchyIntervalFromEventFlow
          (constructiveCauchyIntervalToEventFlow x) =
        constructiveCauchyIntervalFromEventFlow
          (constructiveCauchyIntervalToEventFlow y) :=
    congrArg constructiveCauchyIntervalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ConstructiveCauchyIntervalTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ConstructiveCauchyIntervalTasteGate_single_carrier_alignment_round_trip y)))

instance constructiveCauchyIntervalBHistCarrier :
    BHistCarrier ConstructiveCauchyIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := constructiveCauchyIntervalToEventFlow
  fromEventFlow := constructiveCauchyIntervalFromEventFlow

instance constructiveCauchyIntervalChapterTasteGate :
    ChapterTasteGate ConstructiveCauchyIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      constructiveCauchyIntervalFromEventFlow
          (constructiveCauchyIntervalToEventFlow x) =
        some x
    exact ConstructiveCauchyIntervalTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ConstructiveCauchyIntervalTasteGate_single_carrier_alignment_injective heq)

theorem ConstructiveCauchyIntervalTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      constructiveCauchyIntervalDecodeBHist
          (constructiveCauchyIntervalEncodeBHist h) =
        h) ∧
      (∀ x : ConstructiveCauchyIntervalUp,
        constructiveCauchyIntervalFromEventFlow
            (constructiveCauchyIntervalToEventFlow x) =
          some x) ∧
        (∀ x y : ConstructiveCauchyIntervalUp,
          constructiveCauchyIntervalToEventFlow x =
              constructiveCauchyIntervalToEventFlow y →
            x = y) ∧
          constructiveCauchyIntervalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  exact
    ⟨ConstructiveCauchyIntervalTasteGate_single_carrier_alignment_decode,
      ConstructiveCauchyIntervalTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        ConstructiveCauchyIntervalTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.ConstructiveCauchyIntervalUp
