import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedCauchyIntervalCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedCauchyIntervalCompletionUp : Type where
  | mk (I W D Q S A H C P N : BHist) : LocatedCauchyIntervalCompletionUp
  deriving DecidableEq

def locatedCauchyIntervalCompletionEncodeBHist : BHist → List BMark
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedCauchyIntervalCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedCauchyIntervalCompletionEncodeBHist h

def locatedCauchyIntervalCompletionDecodeBHist : List BMark → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedCauchyIntervalCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedCauchyIntervalCompletionDecodeBHist tail)

private theorem LocatedCauchyIntervalCompletionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      locatedCauchyIntervalCompletionDecodeBHist
          (locatedCauchyIntervalCompletionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedCauchyIntervalCompletionFields :
    LocatedCauchyIntervalCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedCauchyIntervalCompletionUp.mk I W D Q S A H C P N =>
      [I, W, D, Q, S, A, H, C, P, N]

def locatedCauchyIntervalCompletionToEventFlow :
    LocatedCauchyIntervalCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedCauchyIntervalCompletionFields x).map
      locatedCauchyIntervalCompletionEncodeBHist

private def locatedCauchyIntervalCompletionEventAtDefault :
    Nat → EventFlow → List BMark
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      locatedCauchyIntervalCompletionEventAtDefault index rest

def locatedCauchyIntervalCompletionFromEventFlow
    (ef : EventFlow) : Option LocatedCauchyIntervalCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedCauchyIntervalCompletionUp.mk
      (locatedCauchyIntervalCompletionDecodeBHist
        (locatedCauchyIntervalCompletionEventAtDefault 0 ef))
      (locatedCauchyIntervalCompletionDecodeBHist
        (locatedCauchyIntervalCompletionEventAtDefault 1 ef))
      (locatedCauchyIntervalCompletionDecodeBHist
        (locatedCauchyIntervalCompletionEventAtDefault 2 ef))
      (locatedCauchyIntervalCompletionDecodeBHist
        (locatedCauchyIntervalCompletionEventAtDefault 3 ef))
      (locatedCauchyIntervalCompletionDecodeBHist
        (locatedCauchyIntervalCompletionEventAtDefault 4 ef))
      (locatedCauchyIntervalCompletionDecodeBHist
        (locatedCauchyIntervalCompletionEventAtDefault 5 ef))
      (locatedCauchyIntervalCompletionDecodeBHist
        (locatedCauchyIntervalCompletionEventAtDefault 6 ef))
      (locatedCauchyIntervalCompletionDecodeBHist
        (locatedCauchyIntervalCompletionEventAtDefault 7 ef))
      (locatedCauchyIntervalCompletionDecodeBHist
        (locatedCauchyIntervalCompletionEventAtDefault 8 ef))
      (locatedCauchyIntervalCompletionDecodeBHist
        (locatedCauchyIntervalCompletionEventAtDefault 9 ef)))

private theorem LocatedCauchyIntervalCompletionTasteGate_single_carrier_alignment_round :
    ∀ x : LocatedCauchyIntervalCompletionUp,
      locatedCauchyIntervalCompletionFromEventFlow
          (locatedCauchyIntervalCompletionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I W D Q S A H C P N =>
      change
        some
          (LocatedCauchyIntervalCompletionUp.mk
            (locatedCauchyIntervalCompletionDecodeBHist
              (locatedCauchyIntervalCompletionEncodeBHist I))
            (locatedCauchyIntervalCompletionDecodeBHist
              (locatedCauchyIntervalCompletionEncodeBHist W))
            (locatedCauchyIntervalCompletionDecodeBHist
              (locatedCauchyIntervalCompletionEncodeBHist D))
            (locatedCauchyIntervalCompletionDecodeBHist
              (locatedCauchyIntervalCompletionEncodeBHist Q))
            (locatedCauchyIntervalCompletionDecodeBHist
              (locatedCauchyIntervalCompletionEncodeBHist S))
            (locatedCauchyIntervalCompletionDecodeBHist
              (locatedCauchyIntervalCompletionEncodeBHist A))
            (locatedCauchyIntervalCompletionDecodeBHist
              (locatedCauchyIntervalCompletionEncodeBHist H))
            (locatedCauchyIntervalCompletionDecodeBHist
              (locatedCauchyIntervalCompletionEncodeBHist C))
            (locatedCauchyIntervalCompletionDecodeBHist
              (locatedCauchyIntervalCompletionEncodeBHist P))
            (locatedCauchyIntervalCompletionDecodeBHist
              (locatedCauchyIntervalCompletionEncodeBHist N))) =
          some (LocatedCauchyIntervalCompletionUp.mk I W D Q S A H C P N)
      rw [LocatedCauchyIntervalCompletionTasteGate_single_carrier_alignment_decode I,
        LocatedCauchyIntervalCompletionTasteGate_single_carrier_alignment_decode W,
        LocatedCauchyIntervalCompletionTasteGate_single_carrier_alignment_decode D,
        LocatedCauchyIntervalCompletionTasteGate_single_carrier_alignment_decode Q,
        LocatedCauchyIntervalCompletionTasteGate_single_carrier_alignment_decode S,
        LocatedCauchyIntervalCompletionTasteGate_single_carrier_alignment_decode A,
        LocatedCauchyIntervalCompletionTasteGate_single_carrier_alignment_decode H,
        LocatedCauchyIntervalCompletionTasteGate_single_carrier_alignment_decode C,
        LocatedCauchyIntervalCompletionTasteGate_single_carrier_alignment_decode P,
        LocatedCauchyIntervalCompletionTasteGate_single_carrier_alignment_decode N]

private theorem LocatedCauchyIntervalCompletionTasteGate_single_carrier_alignment_injective
    {x y : LocatedCauchyIntervalCompletionUp} :
    locatedCauchyIntervalCompletionToEventFlow x =
        locatedCauchyIntervalCompletionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedCauchyIntervalCompletionFromEventFlow
          (locatedCauchyIntervalCompletionToEventFlow x) =
        locatedCauchyIntervalCompletionFromEventFlow
          (locatedCauchyIntervalCompletionToEventFlow y) :=
    congrArg locatedCauchyIntervalCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LocatedCauchyIntervalCompletionTasteGate_single_carrier_alignment_round x).symm
      (Eq.trans hread
        (LocatedCauchyIntervalCompletionTasteGate_single_carrier_alignment_round y)))

instance locatedCauchyIntervalCompletionBHistCarrier :
    BHistCarrier LocatedCauchyIntervalCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedCauchyIntervalCompletionToEventFlow
  fromEventFlow := locatedCauchyIntervalCompletionFromEventFlow

instance locatedCauchyIntervalCompletionChapterTasteGate :
    ChapterTasteGate LocatedCauchyIntervalCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      locatedCauchyIntervalCompletionFromEventFlow
          (locatedCauchyIntervalCompletionToEventFlow x) =
        some x
    exact LocatedCauchyIntervalCompletionTasteGate_single_carrier_alignment_round x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (LocatedCauchyIntervalCompletionTasteGate_single_carrier_alignment_injective heq)

theorem LocatedCauchyIntervalCompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      locatedCauchyIntervalCompletionDecodeBHist
          (locatedCauchyIntervalCompletionEncodeBHist h) =
        h) ∧
      Nonempty (BHistCarrier LocatedCauchyIntervalCompletionUp) ∧
        Nonempty (ChapterTasteGate LocatedCauchyIntervalCompletionUp) ∧
          locatedCauchyIntervalCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨LocatedCauchyIntervalCompletionTasteGate_single_carrier_alignment_decode,
      ⟨locatedCauchyIntervalCompletionBHistCarrier⟩,
      ⟨locatedCauchyIntervalCompletionChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.LocatedCauchyIntervalCompletionUp
