import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicCompletionFunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicCompletionFunctorUp : Type where
  | mk (D S R E U M H C P N : BHist) : DyadicCompletionFunctorUp
  deriving DecidableEq

def dyadicCompletionFunctorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicCompletionFunctorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicCompletionFunctorEncodeBHist h

def dyadicCompletionFunctorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicCompletionFunctorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicCompletionFunctorDecodeBHist tail)

private theorem DyadicCompletionFunctorTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      dyadicCompletionFunctorDecodeBHist (dyadicCompletionFunctorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicCompletionFunctorFields : DyadicCompletionFunctorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicCompletionFunctorUp.mk D S R E U M H C P N => [D, S, R, E, U, M, H, C, P, N]

def dyadicCompletionFunctorToEventFlow : DyadicCompletionFunctorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dyadicCompletionFunctorFields x).map dyadicCompletionFunctorEncodeBHist

private def dyadicCompletionFunctorEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dyadicCompletionFunctorEventAtDefault index rest

def dyadicCompletionFunctorFromEventFlow (ef : EventFlow) :
    Option DyadicCompletionFunctorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DyadicCompletionFunctorUp.mk
      (dyadicCompletionFunctorDecodeBHist (dyadicCompletionFunctorEventAtDefault 0 ef))
      (dyadicCompletionFunctorDecodeBHist (dyadicCompletionFunctorEventAtDefault 1 ef))
      (dyadicCompletionFunctorDecodeBHist (dyadicCompletionFunctorEventAtDefault 2 ef))
      (dyadicCompletionFunctorDecodeBHist (dyadicCompletionFunctorEventAtDefault 3 ef))
      (dyadicCompletionFunctorDecodeBHist (dyadicCompletionFunctorEventAtDefault 4 ef))
      (dyadicCompletionFunctorDecodeBHist (dyadicCompletionFunctorEventAtDefault 5 ef))
      (dyadicCompletionFunctorDecodeBHist (dyadicCompletionFunctorEventAtDefault 6 ef))
      (dyadicCompletionFunctorDecodeBHist (dyadicCompletionFunctorEventAtDefault 7 ef))
      (dyadicCompletionFunctorDecodeBHist (dyadicCompletionFunctorEventAtDefault 8 ef))
      (dyadicCompletionFunctorDecodeBHist (dyadicCompletionFunctorEventAtDefault 9 ef)))

private theorem DyadicCompletionFunctorTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DyadicCompletionFunctorUp,
      dyadicCompletionFunctorFromEventFlow (dyadicCompletionFunctorToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D S R E U M H C P N =>
      change
        some
            (DyadicCompletionFunctorUp.mk
              (dyadicCompletionFunctorDecodeBHist (dyadicCompletionFunctorEncodeBHist D))
              (dyadicCompletionFunctorDecodeBHist (dyadicCompletionFunctorEncodeBHist S))
              (dyadicCompletionFunctorDecodeBHist (dyadicCompletionFunctorEncodeBHist R))
              (dyadicCompletionFunctorDecodeBHist (dyadicCompletionFunctorEncodeBHist E))
              (dyadicCompletionFunctorDecodeBHist (dyadicCompletionFunctorEncodeBHist U))
              (dyadicCompletionFunctorDecodeBHist (dyadicCompletionFunctorEncodeBHist M))
              (dyadicCompletionFunctorDecodeBHist (dyadicCompletionFunctorEncodeBHist H))
              (dyadicCompletionFunctorDecodeBHist (dyadicCompletionFunctorEncodeBHist C))
              (dyadicCompletionFunctorDecodeBHist (dyadicCompletionFunctorEncodeBHist P))
              (dyadicCompletionFunctorDecodeBHist (dyadicCompletionFunctorEncodeBHist N))) =
          some (DyadicCompletionFunctorUp.mk D S R E U M H C P N)
      rw [DyadicCompletionFunctorTasteGate_single_carrier_alignment_decode D,
        DyadicCompletionFunctorTasteGate_single_carrier_alignment_decode S,
        DyadicCompletionFunctorTasteGate_single_carrier_alignment_decode R,
        DyadicCompletionFunctorTasteGate_single_carrier_alignment_decode E,
        DyadicCompletionFunctorTasteGate_single_carrier_alignment_decode U,
        DyadicCompletionFunctorTasteGate_single_carrier_alignment_decode M,
        DyadicCompletionFunctorTasteGate_single_carrier_alignment_decode H,
        DyadicCompletionFunctorTasteGate_single_carrier_alignment_decode C,
        DyadicCompletionFunctorTasteGate_single_carrier_alignment_decode P,
        DyadicCompletionFunctorTasteGate_single_carrier_alignment_decode N]

private theorem DyadicCompletionFunctorTasteGate_single_carrier_alignment_injective
    {x y : DyadicCompletionFunctorUp} :
    dyadicCompletionFunctorToEventFlow x = dyadicCompletionFunctorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicCompletionFunctorFromEventFlow (dyadicCompletionFunctorToEventFlow x) =
        dyadicCompletionFunctorFromEventFlow (dyadicCompletionFunctorToEventFlow y) :=
    congrArg dyadicCompletionFunctorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DyadicCompletionFunctorTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DyadicCompletionFunctorTasteGate_single_carrier_alignment_round_trip y)))

instance dyadicCompletionFunctorBHistCarrier :
    BHistCarrier DyadicCompletionFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicCompletionFunctorToEventFlow
  fromEventFlow := dyadicCompletionFunctorFromEventFlow

instance dyadicCompletionFunctorChapterTasteGate :
    ChapterTasteGate DyadicCompletionFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      dyadicCompletionFunctorFromEventFlow (dyadicCompletionFunctorToEventFlow x) =
        some x
    exact DyadicCompletionFunctorTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DyadicCompletionFunctorTasteGate_single_carrier_alignment_injective heq)

theorem DyadicCompletionFunctorTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      dyadicCompletionFunctorDecodeBHist (dyadicCompletionFunctorEncodeBHist h) = h) ∧
      (∀ x : DyadicCompletionFunctorUp,
        dyadicCompletionFunctorFromEventFlow (dyadicCompletionFunctorToEventFlow x) =
          some x) ∧
        (∀ x y : DyadicCompletionFunctorUp,
          dyadicCompletionFunctorToEventFlow x = dyadicCompletionFunctorToEventFlow y →
            x = y) ∧
          dyadicCompletionFunctorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨DyadicCompletionFunctorTasteGate_single_carrier_alignment_decode,
      ⟨DyadicCompletionFunctorTasteGate_single_carrier_alignment_round_trip,
        ⟨fun _ _ heq =>
          DyadicCompletionFunctorTasteGate_single_carrier_alignment_injective heq,
          rfl⟩⟩⟩

end BEDC.Derived.DyadicCompletionFunctorUp
