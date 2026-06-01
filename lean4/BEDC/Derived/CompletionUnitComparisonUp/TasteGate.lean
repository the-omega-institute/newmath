import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompletionUnitComparisonUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompletionUnitComparisonUp : Type where
  | mk (Q N T S R H C P L : BHist) : CompletionUnitComparisonUp
  deriving DecidableEq

def completionUnitComparisonEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: completionUnitComparisonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: completionUnitComparisonEncodeBHist h

def completionUnitComparisonDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (completionUnitComparisonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (completionUnitComparisonDecodeBHist tail)

private theorem CompletionUnitComparisonTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      completionUnitComparisonDecodeBHist (completionUnitComparisonEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def completionUnitComparisonToEventFlow : CompletionUnitComparisonUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CompletionUnitComparisonUp.mk Q N T S R H C P L =>
      [completionUnitComparisonEncodeBHist Q,
        completionUnitComparisonEncodeBHist N,
        completionUnitComparisonEncodeBHist T,
        completionUnitComparisonEncodeBHist S,
        completionUnitComparisonEncodeBHist R,
        completionUnitComparisonEncodeBHist H,
        completionUnitComparisonEncodeBHist C,
        completionUnitComparisonEncodeBHist P,
        completionUnitComparisonEncodeBHist L]

private def completionUnitComparisonEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => completionUnitComparisonEventAtDefault index rest

def completionUnitComparisonFromEventFlow
    (ef : EventFlow) : Option CompletionUnitComparisonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompletionUnitComparisonUp.mk
      (completionUnitComparisonDecodeBHist (completionUnitComparisonEventAtDefault 0 ef))
      (completionUnitComparisonDecodeBHist (completionUnitComparisonEventAtDefault 1 ef))
      (completionUnitComparisonDecodeBHist (completionUnitComparisonEventAtDefault 2 ef))
      (completionUnitComparisonDecodeBHist (completionUnitComparisonEventAtDefault 3 ef))
      (completionUnitComparisonDecodeBHist (completionUnitComparisonEventAtDefault 4 ef))
      (completionUnitComparisonDecodeBHist (completionUnitComparisonEventAtDefault 5 ef))
      (completionUnitComparisonDecodeBHist (completionUnitComparisonEventAtDefault 6 ef))
      (completionUnitComparisonDecodeBHist (completionUnitComparisonEventAtDefault 7 ef))
      (completionUnitComparisonDecodeBHist (completionUnitComparisonEventAtDefault 8 ef)))

private theorem CompletionUnitComparisonTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CompletionUnitComparisonUp,
      completionUnitComparisonFromEventFlow (completionUnitComparisonToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q N T S R H C P L =>
      change
        some
          (CompletionUnitComparisonUp.mk
            (completionUnitComparisonDecodeBHist (completionUnitComparisonEncodeBHist Q))
            (completionUnitComparisonDecodeBHist (completionUnitComparisonEncodeBHist N))
            (completionUnitComparisonDecodeBHist (completionUnitComparisonEncodeBHist T))
            (completionUnitComparisonDecodeBHist (completionUnitComparisonEncodeBHist S))
            (completionUnitComparisonDecodeBHist (completionUnitComparisonEncodeBHist R))
            (completionUnitComparisonDecodeBHist (completionUnitComparisonEncodeBHist H))
            (completionUnitComparisonDecodeBHist (completionUnitComparisonEncodeBHist C))
            (completionUnitComparisonDecodeBHist (completionUnitComparisonEncodeBHist P))
            (completionUnitComparisonDecodeBHist (completionUnitComparisonEncodeBHist L))) =
          some (CompletionUnitComparisonUp.mk Q N T S R H C P L)
      rw [CompletionUnitComparisonTasteGate_single_carrier_alignment_decode Q,
        CompletionUnitComparisonTasteGate_single_carrier_alignment_decode N,
        CompletionUnitComparisonTasteGate_single_carrier_alignment_decode T,
        CompletionUnitComparisonTasteGate_single_carrier_alignment_decode S,
        CompletionUnitComparisonTasteGate_single_carrier_alignment_decode R,
        CompletionUnitComparisonTasteGate_single_carrier_alignment_decode H,
        CompletionUnitComparisonTasteGate_single_carrier_alignment_decode C,
        CompletionUnitComparisonTasteGate_single_carrier_alignment_decode P,
        CompletionUnitComparisonTasteGate_single_carrier_alignment_decode L]

private theorem CompletionUnitComparisonTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompletionUnitComparisonUp} :
    completionUnitComparisonToEventFlow x = completionUnitComparisonToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      completionUnitComparisonFromEventFlow (completionUnitComparisonToEventFlow x) =
        completionUnitComparisonFromEventFlow (completionUnitComparisonToEventFlow y) :=
    congrArg completionUnitComparisonFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CompletionUnitComparisonTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompletionUnitComparisonTasteGate_single_carrier_alignment_round_trip y)))

instance completionUnitComparisonBHistCarrier : BHistCarrier CompletionUnitComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := completionUnitComparisonToEventFlow
  fromEventFlow := completionUnitComparisonFromEventFlow

instance completionUnitComparisonChapterTasteGate :
    ChapterTasteGate CompletionUnitComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change completionUnitComparisonFromEventFlow (completionUnitComparisonToEventFlow x) =
      some x
    exact CompletionUnitComparisonTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CompletionUnitComparisonTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate CompletionUnitComparisonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  completionUnitComparisonChapterTasteGate

theorem CompletionUnitComparisonTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        completionUnitComparisonDecodeBHist (completionUnitComparisonEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CompletionUnitComparisonUp) ∧
        Nonempty (ChapterTasteGate CompletionUnitComparisonUp) ∧
          completionUnitComparisonEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CompletionUnitComparisonTasteGate_single_carrier_alignment_decode,
      ⟨completionUnitComparisonBHistCarrier⟩,
      ⟨completionUnitComparisonChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.CompletionUnitComparisonUp
