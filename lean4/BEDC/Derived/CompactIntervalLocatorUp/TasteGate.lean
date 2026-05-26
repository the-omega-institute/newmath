import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactIntervalLocatorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactIntervalLocatorUp : Type where
  | mk (I Lambda M D S R Q H C P N : BHist) : CompactIntervalLocatorUp
  deriving DecidableEq

def compactIntervalLocatorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactIntervalLocatorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactIntervalLocatorEncodeBHist h

def compactIntervalLocatorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactIntervalLocatorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactIntervalLocatorDecodeBHist tail)

private theorem CompactIntervalLocatorTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      compactIntervalLocatorDecodeBHist (compactIntervalLocatorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactIntervalLocatorFields : CompactIntervalLocatorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactIntervalLocatorUp.mk I Lambda M D S R Q H C P N =>
      [I, Lambda, M, D, S, R, Q, H, C, P, N]

def compactIntervalLocatorToEventFlow : CompactIntervalLocatorUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (compactIntervalLocatorFields x).map compactIntervalLocatorEncodeBHist

private def compactIntervalLocatorEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => compactIntervalLocatorEventAtDefault index rest

def compactIntervalLocatorFromEventFlow : EventFlow → Option CompactIntervalLocatorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (CompactIntervalLocatorUp.mk
        (compactIntervalLocatorDecodeBHist (compactIntervalLocatorEventAtDefault 0 ef))
        (compactIntervalLocatorDecodeBHist (compactIntervalLocatorEventAtDefault 1 ef))
        (compactIntervalLocatorDecodeBHist (compactIntervalLocatorEventAtDefault 2 ef))
        (compactIntervalLocatorDecodeBHist (compactIntervalLocatorEventAtDefault 3 ef))
        (compactIntervalLocatorDecodeBHist (compactIntervalLocatorEventAtDefault 4 ef))
        (compactIntervalLocatorDecodeBHist (compactIntervalLocatorEventAtDefault 5 ef))
        (compactIntervalLocatorDecodeBHist (compactIntervalLocatorEventAtDefault 6 ef))
        (compactIntervalLocatorDecodeBHist (compactIntervalLocatorEventAtDefault 7 ef))
        (compactIntervalLocatorDecodeBHist (compactIntervalLocatorEventAtDefault 8 ef))
        (compactIntervalLocatorDecodeBHist (compactIntervalLocatorEventAtDefault 9 ef))
        (compactIntervalLocatorDecodeBHist (compactIntervalLocatorEventAtDefault 10 ef)))

private theorem CompactIntervalLocatorTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CompactIntervalLocatorUp,
      compactIntervalLocatorFromEventFlow (compactIntervalLocatorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I Lambda M D S R Q H C P N =>
      change
        some
          (CompactIntervalLocatorUp.mk
            (compactIntervalLocatorDecodeBHist (compactIntervalLocatorEncodeBHist I))
            (compactIntervalLocatorDecodeBHist (compactIntervalLocatorEncodeBHist Lambda))
            (compactIntervalLocatorDecodeBHist (compactIntervalLocatorEncodeBHist M))
            (compactIntervalLocatorDecodeBHist (compactIntervalLocatorEncodeBHist D))
            (compactIntervalLocatorDecodeBHist (compactIntervalLocatorEncodeBHist S))
            (compactIntervalLocatorDecodeBHist (compactIntervalLocatorEncodeBHist R))
            (compactIntervalLocatorDecodeBHist (compactIntervalLocatorEncodeBHist Q))
            (compactIntervalLocatorDecodeBHist (compactIntervalLocatorEncodeBHist H))
            (compactIntervalLocatorDecodeBHist (compactIntervalLocatorEncodeBHist C))
            (compactIntervalLocatorDecodeBHist (compactIntervalLocatorEncodeBHist P))
            (compactIntervalLocatorDecodeBHist (compactIntervalLocatorEncodeBHist N))) =
          some (CompactIntervalLocatorUp.mk I Lambda M D S R Q H C P N)
      rw [CompactIntervalLocatorTasteGate_single_carrier_alignment_decode I,
        CompactIntervalLocatorTasteGate_single_carrier_alignment_decode Lambda,
        CompactIntervalLocatorTasteGate_single_carrier_alignment_decode M,
        CompactIntervalLocatorTasteGate_single_carrier_alignment_decode D,
        CompactIntervalLocatorTasteGate_single_carrier_alignment_decode S,
        CompactIntervalLocatorTasteGate_single_carrier_alignment_decode R,
        CompactIntervalLocatorTasteGate_single_carrier_alignment_decode Q,
        CompactIntervalLocatorTasteGate_single_carrier_alignment_decode H,
        CompactIntervalLocatorTasteGate_single_carrier_alignment_decode C,
        CompactIntervalLocatorTasteGate_single_carrier_alignment_decode P,
        CompactIntervalLocatorTasteGate_single_carrier_alignment_decode N]

private theorem CompactIntervalLocatorTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompactIntervalLocatorUp} :
    compactIntervalLocatorToEventFlow x = compactIntervalLocatorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactIntervalLocatorFromEventFlow (compactIntervalLocatorToEventFlow x) =
        compactIntervalLocatorFromEventFlow (compactIntervalLocatorToEventFlow y) :=
    congrArg compactIntervalLocatorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CompactIntervalLocatorTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CompactIntervalLocatorTasteGate_single_carrier_alignment_round_trip y)))

instance compactIntervalLocatorBHistCarrier : BHistCarrier CompactIntervalLocatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactIntervalLocatorToEventFlow
  fromEventFlow := compactIntervalLocatorFromEventFlow

instance compactIntervalLocatorChapterTasteGate : ChapterTasteGate CompactIntervalLocatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change compactIntervalLocatorFromEventFlow (compactIntervalLocatorToEventFlow x) = some x
    exact CompactIntervalLocatorTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CompactIntervalLocatorTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate CompactIntervalLocatorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactIntervalLocatorChapterTasteGate

theorem CompactIntervalLocatorTasteGate_single_carrier_alignment :
    (∀ h : BHist, compactIntervalLocatorDecodeBHist (compactIntervalLocatorEncodeBHist h) = h) ∧
      (∀ x : CompactIntervalLocatorUp,
        compactIntervalLocatorFromEventFlow (compactIntervalLocatorToEventFlow x) = some x) ∧
        (∀ x y : CompactIntervalLocatorUp,
          compactIntervalLocatorToEventFlow x = compactIntervalLocatorToEventFlow y → x = y) ∧
          compactIntervalLocatorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CompactIntervalLocatorTasteGate_single_carrier_alignment_decode,
      CompactIntervalLocatorTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CompactIntervalLocatorTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CompactIntervalLocatorUp
