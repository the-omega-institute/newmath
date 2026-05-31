import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BlaschkeSelectionCompactHyperspaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BlaschkeSelectionCompactHyperspaceUp : Type where
  | mk (X S D W E R H C P N : BHist) : BlaschkeSelectionCompactHyperspaceUp
  deriving DecidableEq

def blaschkeSelectionCompactHyperspaceEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: blaschkeSelectionCompactHyperspaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: blaschkeSelectionCompactHyperspaceEncodeBHist h

def blaschkeSelectionCompactHyperspaceDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (blaschkeSelectionCompactHyperspaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (blaschkeSelectionCompactHyperspaceDecodeBHist tail)

def blaschkeSelectionCompactHyperspaceFields :
    BlaschkeSelectionCompactHyperspaceUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BlaschkeSelectionCompactHyperspaceUp.mk X S D W E R H C P N =>
      [X, S, D, W, E, R, H, C, P, N]

def blaschkeSelectionCompactHyperspaceToEventFlow :
    BlaschkeSelectionCompactHyperspaceUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (blaschkeSelectionCompactHyperspaceFields x).map
        blaschkeSelectionCompactHyperspaceEncodeBHist

private def blaschkeSelectionCompactHyperspaceEventAtDefault :
    Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      blaschkeSelectionCompactHyperspaceEventAtDefault index rest

def blaschkeSelectionCompactHyperspaceFromEventFlow
    (ef : EventFlow) : Option BlaschkeSelectionCompactHyperspaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BlaschkeSelectionCompactHyperspaceUp.mk
      (blaschkeSelectionCompactHyperspaceDecodeBHist
        (blaschkeSelectionCompactHyperspaceEventAtDefault 0 ef))
      (blaschkeSelectionCompactHyperspaceDecodeBHist
        (blaschkeSelectionCompactHyperspaceEventAtDefault 1 ef))
      (blaschkeSelectionCompactHyperspaceDecodeBHist
        (blaschkeSelectionCompactHyperspaceEventAtDefault 2 ef))
      (blaschkeSelectionCompactHyperspaceDecodeBHist
        (blaschkeSelectionCompactHyperspaceEventAtDefault 3 ef))
      (blaschkeSelectionCompactHyperspaceDecodeBHist
        (blaschkeSelectionCompactHyperspaceEventAtDefault 4 ef))
      (blaschkeSelectionCompactHyperspaceDecodeBHist
        (blaschkeSelectionCompactHyperspaceEventAtDefault 5 ef))
      (blaschkeSelectionCompactHyperspaceDecodeBHist
        (blaschkeSelectionCompactHyperspaceEventAtDefault 6 ef))
      (blaschkeSelectionCompactHyperspaceDecodeBHist
        (blaschkeSelectionCompactHyperspaceEventAtDefault 7 ef))
      (blaschkeSelectionCompactHyperspaceDecodeBHist
        (blaschkeSelectionCompactHyperspaceEventAtDefault 8 ef))
      (blaschkeSelectionCompactHyperspaceDecodeBHist
        (blaschkeSelectionCompactHyperspaceEventAtDefault 9 ef)))

theorem BlaschkeSelectionCompactHyperspaceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      blaschkeSelectionCompactHyperspaceDecodeBHist
        (blaschkeSelectionCompactHyperspaceEncodeBHist h) = h) ∧
      (∀ x : BlaschkeSelectionCompactHyperspaceUp,
        blaschkeSelectionCompactHyperspaceFromEventFlow
          (blaschkeSelectionCompactHyperspaceToEventFlow x) = some x) ∧
      (∀ x y : BlaschkeSelectionCompactHyperspaceUp,
        blaschkeSelectionCompactHyperspaceToEventFlow x =
            blaschkeSelectionCompactHyperspaceToEventFlow y →
          x = y) ∧
      blaschkeSelectionCompactHyperspaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  have hdecode :
      ∀ h : BHist,
        blaschkeSelectionCompactHyperspaceDecodeBHist
          (blaschkeSelectionCompactHyperspaceEncodeBHist h) = h := by
    intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  have hround :
      ∀ x : BlaschkeSelectionCompactHyperspaceUp,
        blaschkeSelectionCompactHyperspaceFromEventFlow
          (blaschkeSelectionCompactHyperspaceToEventFlow x) = some x := by
    intro x
    cases x with
    | mk X S D W E R H C P N =>
        change
          some
            (BlaschkeSelectionCompactHyperspaceUp.mk
              (blaschkeSelectionCompactHyperspaceDecodeBHist
                (blaschkeSelectionCompactHyperspaceEncodeBHist X))
              (blaschkeSelectionCompactHyperspaceDecodeBHist
                (blaschkeSelectionCompactHyperspaceEncodeBHist S))
              (blaschkeSelectionCompactHyperspaceDecodeBHist
                (blaschkeSelectionCompactHyperspaceEncodeBHist D))
              (blaschkeSelectionCompactHyperspaceDecodeBHist
                (blaschkeSelectionCompactHyperspaceEncodeBHist W))
              (blaschkeSelectionCompactHyperspaceDecodeBHist
                (blaschkeSelectionCompactHyperspaceEncodeBHist E))
              (blaschkeSelectionCompactHyperspaceDecodeBHist
                (blaschkeSelectionCompactHyperspaceEncodeBHist R))
              (blaschkeSelectionCompactHyperspaceDecodeBHist
                (blaschkeSelectionCompactHyperspaceEncodeBHist H))
              (blaschkeSelectionCompactHyperspaceDecodeBHist
                (blaschkeSelectionCompactHyperspaceEncodeBHist C))
              (blaschkeSelectionCompactHyperspaceDecodeBHist
                (blaschkeSelectionCompactHyperspaceEncodeBHist P))
              (blaschkeSelectionCompactHyperspaceDecodeBHist
                (blaschkeSelectionCompactHyperspaceEncodeBHist N))) =
            some (BlaschkeSelectionCompactHyperspaceUp.mk X S D W E R H C P N)
        rw [hdecode X, hdecode S, hdecode D, hdecode W, hdecode E, hdecode R,
          hdecode H, hdecode C, hdecode P, hdecode N]
  have hinjective :
      ∀ x y : BlaschkeSelectionCompactHyperspaceUp,
        blaschkeSelectionCompactHyperspaceToEventFlow x =
            blaschkeSelectionCompactHyperspaceToEventFlow y →
          x = y := by
    intro x y heq
    have hread :
        blaschkeSelectionCompactHyperspaceFromEventFlow
            (blaschkeSelectionCompactHyperspaceToEventFlow x) =
          blaschkeSelectionCompactHyperspaceFromEventFlow
            (blaschkeSelectionCompactHyperspaceToEventFlow y) :=
      congrArg blaschkeSelectionCompactHyperspaceFromEventFlow heq
    exact Option.some.inj
      (Eq.trans (hround x).symm (Eq.trans hread (hround y)))
  exact ⟨hdecode, hround, hinjective, rfl⟩

end BEDC.Derived.BlaschkeSelectionCompactHyperspaceUp
