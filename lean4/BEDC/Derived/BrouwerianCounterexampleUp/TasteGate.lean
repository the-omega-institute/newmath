import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BrouwerianCounterexampleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BrouwerianCounterexampleUp : Type where
  | mk (Q A S R E L H C P N : BHist) : BrouwerianCounterexampleUp
  deriving DecidableEq

def brouwerianCounterexampleEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: brouwerianCounterexampleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: brouwerianCounterexampleEncodeBHist h

def brouwerianCounterexampleDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (brouwerianCounterexampleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (brouwerianCounterexampleDecodeBHist tail)

private theorem BrouwerianCounterexampleTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      brouwerianCounterexampleDecodeBHist (brouwerianCounterexampleEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def brouwerianCounterexampleFields : BrouwerianCounterexampleUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BrouwerianCounterexampleUp.mk Q A S R E L H C P N => [Q, A, S, R, E, L, H, C, P, N]

def brouwerianCounterexampleToEventFlow : BrouwerianCounterexampleUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (brouwerianCounterexampleFields x).map brouwerianCounterexampleEncodeBHist

private def brouwerianCounterexampleEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => brouwerianCounterexampleEventAtDefault index rest

def brouwerianCounterexampleFromEventFlow (ef : EventFlow) :
    Option BrouwerianCounterexampleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BrouwerianCounterexampleUp.mk
      (brouwerianCounterexampleDecodeBHist (brouwerianCounterexampleEventAtDefault 0 ef))
      (brouwerianCounterexampleDecodeBHist (brouwerianCounterexampleEventAtDefault 1 ef))
      (brouwerianCounterexampleDecodeBHist (brouwerianCounterexampleEventAtDefault 2 ef))
      (brouwerianCounterexampleDecodeBHist (brouwerianCounterexampleEventAtDefault 3 ef))
      (brouwerianCounterexampleDecodeBHist (brouwerianCounterexampleEventAtDefault 4 ef))
      (brouwerianCounterexampleDecodeBHist (brouwerianCounterexampleEventAtDefault 5 ef))
      (brouwerianCounterexampleDecodeBHist (brouwerianCounterexampleEventAtDefault 6 ef))
      (brouwerianCounterexampleDecodeBHist (brouwerianCounterexampleEventAtDefault 7 ef))
      (brouwerianCounterexampleDecodeBHist (brouwerianCounterexampleEventAtDefault 8 ef))
      (brouwerianCounterexampleDecodeBHist (brouwerianCounterexampleEventAtDefault 9 ef)))

private theorem brouwerianCounterexample_round_trip :
    ∀ x : BrouwerianCounterexampleUp,
      brouwerianCounterexampleFromEventFlow (brouwerianCounterexampleToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q A S R E L H C P N =>
      change
        some
            (BrouwerianCounterexampleUp.mk
              (brouwerianCounterexampleDecodeBHist (brouwerianCounterexampleEncodeBHist Q))
              (brouwerianCounterexampleDecodeBHist (brouwerianCounterexampleEncodeBHist A))
              (brouwerianCounterexampleDecodeBHist (brouwerianCounterexampleEncodeBHist S))
              (brouwerianCounterexampleDecodeBHist (brouwerianCounterexampleEncodeBHist R))
              (brouwerianCounterexampleDecodeBHist (brouwerianCounterexampleEncodeBHist E))
              (brouwerianCounterexampleDecodeBHist (brouwerianCounterexampleEncodeBHist L))
              (brouwerianCounterexampleDecodeBHist (brouwerianCounterexampleEncodeBHist H))
              (brouwerianCounterexampleDecodeBHist (brouwerianCounterexampleEncodeBHist C))
              (brouwerianCounterexampleDecodeBHist (brouwerianCounterexampleEncodeBHist P))
              (brouwerianCounterexampleDecodeBHist (brouwerianCounterexampleEncodeBHist N))) =
          some (BrouwerianCounterexampleUp.mk Q A S R E L H C P N)
      rw [BrouwerianCounterexampleTasteGate_single_carrier_alignment_decode Q,
        BrouwerianCounterexampleTasteGate_single_carrier_alignment_decode A,
        BrouwerianCounterexampleTasteGate_single_carrier_alignment_decode S,
        BrouwerianCounterexampleTasteGate_single_carrier_alignment_decode R,
        BrouwerianCounterexampleTasteGate_single_carrier_alignment_decode E,
        BrouwerianCounterexampleTasteGate_single_carrier_alignment_decode L,
        BrouwerianCounterexampleTasteGate_single_carrier_alignment_decode H,
        BrouwerianCounterexampleTasteGate_single_carrier_alignment_decode C,
        BrouwerianCounterexampleTasteGate_single_carrier_alignment_decode P,
        BrouwerianCounterexampleTasteGate_single_carrier_alignment_decode N]

private theorem brouwerianCounterexampleToEventFlow_injective
    {x y : BrouwerianCounterexampleUp} :
    brouwerianCounterexampleToEventFlow x = brouwerianCounterexampleToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      brouwerianCounterexampleFromEventFlow (brouwerianCounterexampleToEventFlow x) =
        brouwerianCounterexampleFromEventFlow (brouwerianCounterexampleToEventFlow y) :=
    congrArg brouwerianCounterexampleFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (brouwerianCounterexample_round_trip x).symm
      (Eq.trans hread (brouwerianCounterexample_round_trip y)))

instance brouwerianCounterexampleBHistCarrier : BHistCarrier BrouwerianCounterexampleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := brouwerianCounterexampleToEventFlow
  fromEventFlow := brouwerianCounterexampleFromEventFlow

instance brouwerianCounterexampleChapterTasteGate :
    ChapterTasteGate BrouwerianCounterexampleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change brouwerianCounterexampleFromEventFlow (brouwerianCounterexampleToEventFlow x) =
      some x
    exact brouwerianCounterexample_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (brouwerianCounterexampleToEventFlow_injective heq)

def taste_gate : ChapterTasteGate BrouwerianCounterexampleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  brouwerianCounterexampleChapterTasteGate

theorem BrouwerianCounterexampleTasteGate_single_carrier_alignment :
    (∀ h : BHist, brouwerianCounterexampleDecodeBHist (brouwerianCounterexampleEncodeBHist h) = h) ∧
      (∀ x : BrouwerianCounterexampleUp,
        brouwerianCounterexampleFromEventFlow (brouwerianCounterexampleToEventFlow x) =
          some x) ∧
        (∀ x y : BrouwerianCounterexampleUp,
          brouwerianCounterexampleToEventFlow x =
            brouwerianCounterexampleToEventFlow y → x = y) ∧
          brouwerianCounterexampleEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨BrouwerianCounterexampleTasteGate_single_carrier_alignment_decode,
      brouwerianCounterexample_round_trip,
      (fun _ _ heq => brouwerianCounterexampleToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.BrouwerianCounterexampleUp
