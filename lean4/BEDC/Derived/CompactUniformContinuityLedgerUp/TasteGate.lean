import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactUniformContinuityLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactUniformContinuityLedgerUp : Type where
  | mk (K F M R T U H C P N : BHist) : CompactUniformContinuityLedgerUp
  deriving DecidableEq

def compactUniformContinuityLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactUniformContinuityLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactUniformContinuityLedgerEncodeBHist h

def compactUniformContinuityLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactUniformContinuityLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactUniformContinuityLedgerDecodeBHist tail)

private theorem CompactUniformContinuityLedgerTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      compactUniformContinuityLedgerDecodeBHist
        (compactUniformContinuityLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactUniformContinuityLedgerFields :
    CompactUniformContinuityLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactUniformContinuityLedgerUp.mk K F M R T U H C P N =>
      [K, F, M, R, T, U, H, C, P, N]

def compactUniformContinuityLedgerToEventFlow :
    CompactUniformContinuityLedgerUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (compactUniformContinuityLedgerFields x).map
      compactUniformContinuityLedgerEncodeBHist

private def compactUniformContinuityLedgerEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      compactUniformContinuityLedgerEventAtDefault index rest

def compactUniformContinuityLedgerFromEventFlow :
    EventFlow → Option CompactUniformContinuityLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (CompactUniformContinuityLedgerUp.mk
        (compactUniformContinuityLedgerDecodeBHist
          (compactUniformContinuityLedgerEventAtDefault 0 ef))
        (compactUniformContinuityLedgerDecodeBHist
          (compactUniformContinuityLedgerEventAtDefault 1 ef))
        (compactUniformContinuityLedgerDecodeBHist
          (compactUniformContinuityLedgerEventAtDefault 2 ef))
        (compactUniformContinuityLedgerDecodeBHist
          (compactUniformContinuityLedgerEventAtDefault 3 ef))
        (compactUniformContinuityLedgerDecodeBHist
          (compactUniformContinuityLedgerEventAtDefault 4 ef))
        (compactUniformContinuityLedgerDecodeBHist
          (compactUniformContinuityLedgerEventAtDefault 5 ef))
        (compactUniformContinuityLedgerDecodeBHist
          (compactUniformContinuityLedgerEventAtDefault 6 ef))
        (compactUniformContinuityLedgerDecodeBHist
          (compactUniformContinuityLedgerEventAtDefault 7 ef))
        (compactUniformContinuityLedgerDecodeBHist
          (compactUniformContinuityLedgerEventAtDefault 8 ef))
        (compactUniformContinuityLedgerDecodeBHist
          (compactUniformContinuityLedgerEventAtDefault 9 ef)))

private theorem CompactUniformContinuityLedgerTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CompactUniformContinuityLedgerUp,
      compactUniformContinuityLedgerFromEventFlow
        (compactUniformContinuityLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K F M R T U H C P N =>
      change
        some
          (CompactUniformContinuityLedgerUp.mk
            (compactUniformContinuityLedgerDecodeBHist
              (compactUniformContinuityLedgerEncodeBHist K))
            (compactUniformContinuityLedgerDecodeBHist
              (compactUniformContinuityLedgerEncodeBHist F))
            (compactUniformContinuityLedgerDecodeBHist
              (compactUniformContinuityLedgerEncodeBHist M))
            (compactUniformContinuityLedgerDecodeBHist
              (compactUniformContinuityLedgerEncodeBHist R))
            (compactUniformContinuityLedgerDecodeBHist
              (compactUniformContinuityLedgerEncodeBHist T))
            (compactUniformContinuityLedgerDecodeBHist
              (compactUniformContinuityLedgerEncodeBHist U))
            (compactUniformContinuityLedgerDecodeBHist
              (compactUniformContinuityLedgerEncodeBHist H))
            (compactUniformContinuityLedgerDecodeBHist
              (compactUniformContinuityLedgerEncodeBHist C))
            (compactUniformContinuityLedgerDecodeBHist
              (compactUniformContinuityLedgerEncodeBHist P))
            (compactUniformContinuityLedgerDecodeBHist
              (compactUniformContinuityLedgerEncodeBHist N))) =
          some (CompactUniformContinuityLedgerUp.mk K F M R T U H C P N)
      rw [CompactUniformContinuityLedgerTasteGate_single_carrier_alignment_decode K,
        CompactUniformContinuityLedgerTasteGate_single_carrier_alignment_decode F,
        CompactUniformContinuityLedgerTasteGate_single_carrier_alignment_decode M,
        CompactUniformContinuityLedgerTasteGate_single_carrier_alignment_decode R,
        CompactUniformContinuityLedgerTasteGate_single_carrier_alignment_decode T,
        CompactUniformContinuityLedgerTasteGate_single_carrier_alignment_decode U,
        CompactUniformContinuityLedgerTasteGate_single_carrier_alignment_decode H,
        CompactUniformContinuityLedgerTasteGate_single_carrier_alignment_decode C,
        CompactUniformContinuityLedgerTasteGate_single_carrier_alignment_decode P,
        CompactUniformContinuityLedgerTasteGate_single_carrier_alignment_decode N]

private theorem CompactUniformContinuityLedgerTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompactUniformContinuityLedgerUp} :
    compactUniformContinuityLedgerToEventFlow x =
        compactUniformContinuityLedgerToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactUniformContinuityLedgerFromEventFlow
          (compactUniformContinuityLedgerToEventFlow x) =
        compactUniformContinuityLedgerFromEventFlow
          (compactUniformContinuityLedgerToEventFlow y) :=
    congrArg compactUniformContinuityLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CompactUniformContinuityLedgerTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompactUniformContinuityLedgerTasteGate_single_carrier_alignment_round_trip y)))

instance compactUniformContinuityLedgerBHistCarrier :
    BHistCarrier CompactUniformContinuityLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactUniformContinuityLedgerToEventFlow
  fromEventFlow := compactUniformContinuityLedgerFromEventFlow

instance compactUniformContinuityLedgerChapterTasteGate :
    ChapterTasteGate CompactUniformContinuityLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactUniformContinuityLedgerFromEventFlow
        (compactUniformContinuityLedgerToEventFlow x) = some x
    exact CompactUniformContinuityLedgerTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CompactUniformContinuityLedgerTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

def taste_gate : ChapterTasteGate CompactUniformContinuityLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactUniformContinuityLedgerChapterTasteGate

theorem CompactUniformContinuityLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      compactUniformContinuityLedgerDecodeBHist
        (compactUniformContinuityLedgerEncodeBHist h) = h) ∧
      (∀ x : CompactUniformContinuityLedgerUp,
        compactUniformContinuityLedgerFromEventFlow
          (compactUniformContinuityLedgerToEventFlow x) = some x) ∧
        (∀ x y : CompactUniformContinuityLedgerUp,
          compactUniformContinuityLedgerToEventFlow x =
              compactUniformContinuityLedgerToEventFlow y →
            x = y) ∧
          compactUniformContinuityLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CompactUniformContinuityLedgerTasteGate_single_carrier_alignment_decode,
      CompactUniformContinuityLedgerTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CompactUniformContinuityLedgerTasteGate_single_carrier_alignment_toEventFlow_injective
          heq),
      rfl⟩

end BEDC.Derived.CompactUniformContinuityLedgerUp
