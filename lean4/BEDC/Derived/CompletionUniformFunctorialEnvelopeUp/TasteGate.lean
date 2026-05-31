import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompletionUniformFunctorialEnvelopeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompletionUniformFunctorialEnvelopeUp : Type where
  | mk (U M F L S R A H C P N : BHist) : CompletionUniformFunctorialEnvelopeUp
  deriving DecidableEq

def completionUniformFunctorialEnvelopeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: completionUniformFunctorialEnvelopeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: completionUniformFunctorialEnvelopeEncodeBHist h

def completionUniformFunctorialEnvelopeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (completionUniformFunctorialEnvelopeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (completionUniformFunctorialEnvelopeDecodeBHist tail)

private theorem CompletionUniformFunctorialEnvelopeTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      completionUniformFunctorialEnvelopeDecodeBHist
        (completionUniformFunctorialEnvelopeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def completionUniformFunctorialEnvelopeFields :
    CompletionUniformFunctorialEnvelopeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompletionUniformFunctorialEnvelopeUp.mk U M F L S R A H C P N =>
      [U, M, F, L, S, R, A, H, C, P, N]

def completionUniformFunctorialEnvelopeToEventFlow :
    CompletionUniformFunctorialEnvelopeUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (completionUniformFunctorialEnvelopeFields x).map
      completionUniformFunctorialEnvelopeEncodeBHist

private def completionUniformFunctorialEnvelopeEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      completionUniformFunctorialEnvelopeEventAtDefault index rest

def completionUniformFunctorialEnvelopeFromEventFlow
    (ef : EventFlow) : Option CompletionUniformFunctorialEnvelopeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompletionUniformFunctorialEnvelopeUp.mk
      (completionUniformFunctorialEnvelopeDecodeBHist
        (completionUniformFunctorialEnvelopeEventAtDefault 0 ef))
      (completionUniformFunctorialEnvelopeDecodeBHist
        (completionUniformFunctorialEnvelopeEventAtDefault 1 ef))
      (completionUniformFunctorialEnvelopeDecodeBHist
        (completionUniformFunctorialEnvelopeEventAtDefault 2 ef))
      (completionUniformFunctorialEnvelopeDecodeBHist
        (completionUniformFunctorialEnvelopeEventAtDefault 3 ef))
      (completionUniformFunctorialEnvelopeDecodeBHist
        (completionUniformFunctorialEnvelopeEventAtDefault 4 ef))
      (completionUniformFunctorialEnvelopeDecodeBHist
        (completionUniformFunctorialEnvelopeEventAtDefault 5 ef))
      (completionUniformFunctorialEnvelopeDecodeBHist
        (completionUniformFunctorialEnvelopeEventAtDefault 6 ef))
      (completionUniformFunctorialEnvelopeDecodeBHist
        (completionUniformFunctorialEnvelopeEventAtDefault 7 ef))
      (completionUniformFunctorialEnvelopeDecodeBHist
        (completionUniformFunctorialEnvelopeEventAtDefault 8 ef))
      (completionUniformFunctorialEnvelopeDecodeBHist
        (completionUniformFunctorialEnvelopeEventAtDefault 9 ef))
      (completionUniformFunctorialEnvelopeDecodeBHist
        (completionUniformFunctorialEnvelopeEventAtDefault 10 ef)))

private theorem CompletionUniformFunctorialEnvelopeTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CompletionUniformFunctorialEnvelopeUp,
      completionUniformFunctorialEnvelopeFromEventFlow
        (completionUniformFunctorialEnvelopeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk U M F L S R A H C P N =>
      change
        some
            (CompletionUniformFunctorialEnvelopeUp.mk
              (completionUniformFunctorialEnvelopeDecodeBHist
                (completionUniformFunctorialEnvelopeEncodeBHist U))
              (completionUniformFunctorialEnvelopeDecodeBHist
                (completionUniformFunctorialEnvelopeEncodeBHist M))
              (completionUniformFunctorialEnvelopeDecodeBHist
                (completionUniformFunctorialEnvelopeEncodeBHist F))
              (completionUniformFunctorialEnvelopeDecodeBHist
                (completionUniformFunctorialEnvelopeEncodeBHist L))
              (completionUniformFunctorialEnvelopeDecodeBHist
                (completionUniformFunctorialEnvelopeEncodeBHist S))
              (completionUniformFunctorialEnvelopeDecodeBHist
                (completionUniformFunctorialEnvelopeEncodeBHist R))
              (completionUniformFunctorialEnvelopeDecodeBHist
                (completionUniformFunctorialEnvelopeEncodeBHist A))
              (completionUniformFunctorialEnvelopeDecodeBHist
                (completionUniformFunctorialEnvelopeEncodeBHist H))
              (completionUniformFunctorialEnvelopeDecodeBHist
                (completionUniformFunctorialEnvelopeEncodeBHist C))
              (completionUniformFunctorialEnvelopeDecodeBHist
                (completionUniformFunctorialEnvelopeEncodeBHist P))
              (completionUniformFunctorialEnvelopeDecodeBHist
                (completionUniformFunctorialEnvelopeEncodeBHist N))) =
          some (CompletionUniformFunctorialEnvelopeUp.mk U M F L S R A H C P N)
      rw [CompletionUniformFunctorialEnvelopeTasteGate_single_carrier_alignment_decode U,
        CompletionUniformFunctorialEnvelopeTasteGate_single_carrier_alignment_decode M,
        CompletionUniformFunctorialEnvelopeTasteGate_single_carrier_alignment_decode F,
        CompletionUniformFunctorialEnvelopeTasteGate_single_carrier_alignment_decode L,
        CompletionUniformFunctorialEnvelopeTasteGate_single_carrier_alignment_decode S,
        CompletionUniformFunctorialEnvelopeTasteGate_single_carrier_alignment_decode R,
        CompletionUniformFunctorialEnvelopeTasteGate_single_carrier_alignment_decode A,
        CompletionUniformFunctorialEnvelopeTasteGate_single_carrier_alignment_decode H,
        CompletionUniformFunctorialEnvelopeTasteGate_single_carrier_alignment_decode C,
        CompletionUniformFunctorialEnvelopeTasteGate_single_carrier_alignment_decode P,
        CompletionUniformFunctorialEnvelopeTasteGate_single_carrier_alignment_decode N]

private theorem CompletionUniformFunctorialEnvelopeTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompletionUniformFunctorialEnvelopeUp} :
    completionUniformFunctorialEnvelopeToEventFlow x =
        completionUniformFunctorialEnvelopeToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      completionUniformFunctorialEnvelopeFromEventFlow
          (completionUniformFunctorialEnvelopeToEventFlow x) =
        completionUniformFunctorialEnvelopeFromEventFlow
          (completionUniformFunctorialEnvelopeToEventFlow y) :=
    congrArg completionUniformFunctorialEnvelopeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CompletionUniformFunctorialEnvelopeTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompletionUniformFunctorialEnvelopeTasteGate_single_carrier_alignment_round_trip y)))

instance completionUniformFunctorialEnvelopeBHistCarrier :
    BHistCarrier CompletionUniformFunctorialEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := completionUniformFunctorialEnvelopeToEventFlow
  fromEventFlow := completionUniformFunctorialEnvelopeFromEventFlow

instance completionUniformFunctorialEnvelopeChapterTasteGate :
    ChapterTasteGate CompletionUniformFunctorialEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      completionUniformFunctorialEnvelopeFromEventFlow
        (completionUniformFunctorialEnvelopeToEventFlow x) = some x
    exact CompletionUniformFunctorialEnvelopeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CompletionUniformFunctorialEnvelopeTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

theorem CompletionUniformFunctorialEnvelopeTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      completionUniformFunctorialEnvelopeDecodeBHist
        (completionUniformFunctorialEnvelopeEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CompletionUniformFunctorialEnvelopeUp) ∧
        Nonempty (ChapterTasteGate CompletionUniformFunctorialEnvelopeUp) ∧
          completionUniformFunctorialEnvelopeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CompletionUniformFunctorialEnvelopeTasteGate_single_carrier_alignment_decode,
      ⟨completionUniformFunctorialEnvelopeBHistCarrier⟩,
      ⟨completionUniformFunctorialEnvelopeChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.CompletionUniformFunctorialEnvelopeUp
