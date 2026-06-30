import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactRealIntervalSearchBasisUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactRealIntervalSearchBasisUp : Type where
  | mk (K L F D W R E H C P N : BHist) : CompactRealIntervalSearchBasisUp
  deriving DecidableEq

def compactRealIntervalSearchBasisEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactRealIntervalSearchBasisEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactRealIntervalSearchBasisEncodeBHist h

def compactRealIntervalSearchBasisDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactRealIntervalSearchBasisDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactRealIntervalSearchBasisDecodeBHist tail)

private theorem CompactRealIntervalSearchBasisTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      compactRealIntervalSearchBasisDecodeBHist
        (compactRealIntervalSearchBasisEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactRealIntervalSearchBasisFields :
    CompactRealIntervalSearchBasisUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactRealIntervalSearchBasisUp.mk K L F D W R E H C P N =>
      [K, L, F, D, W, R, E, H, C, P, N]

def compactRealIntervalSearchBasisToEventFlow :
    CompactRealIntervalSearchBasisUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (compactRealIntervalSearchBasisFields x).map
      compactRealIntervalSearchBasisEncodeBHist

private def compactRealIntervalSearchBasisEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      compactRealIntervalSearchBasisEventAtDefault index rest

def compactRealIntervalSearchBasisFromEventFlow
    (ef : EventFlow) : Option CompactRealIntervalSearchBasisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompactRealIntervalSearchBasisUp.mk
      (compactRealIntervalSearchBasisDecodeBHist
        (compactRealIntervalSearchBasisEventAtDefault 0 ef))
      (compactRealIntervalSearchBasisDecodeBHist
        (compactRealIntervalSearchBasisEventAtDefault 1 ef))
      (compactRealIntervalSearchBasisDecodeBHist
        (compactRealIntervalSearchBasisEventAtDefault 2 ef))
      (compactRealIntervalSearchBasisDecodeBHist
        (compactRealIntervalSearchBasisEventAtDefault 3 ef))
      (compactRealIntervalSearchBasisDecodeBHist
        (compactRealIntervalSearchBasisEventAtDefault 4 ef))
      (compactRealIntervalSearchBasisDecodeBHist
        (compactRealIntervalSearchBasisEventAtDefault 5 ef))
      (compactRealIntervalSearchBasisDecodeBHist
        (compactRealIntervalSearchBasisEventAtDefault 6 ef))
      (compactRealIntervalSearchBasisDecodeBHist
        (compactRealIntervalSearchBasisEventAtDefault 7 ef))
      (compactRealIntervalSearchBasisDecodeBHist
        (compactRealIntervalSearchBasisEventAtDefault 8 ef))
      (compactRealIntervalSearchBasisDecodeBHist
        (compactRealIntervalSearchBasisEventAtDefault 9 ef))
      (compactRealIntervalSearchBasisDecodeBHist
        (compactRealIntervalSearchBasisEventAtDefault 10 ef)))

private theorem CompactRealIntervalSearchBasisTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CompactRealIntervalSearchBasisUp,
      compactRealIntervalSearchBasisFromEventFlow
          (compactRealIntervalSearchBasisToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K L F D W R E H C P N =>
      change
        some
          (CompactRealIntervalSearchBasisUp.mk
            (compactRealIntervalSearchBasisDecodeBHist
              (compactRealIntervalSearchBasisEncodeBHist K))
            (compactRealIntervalSearchBasisDecodeBHist
              (compactRealIntervalSearchBasisEncodeBHist L))
            (compactRealIntervalSearchBasisDecodeBHist
              (compactRealIntervalSearchBasisEncodeBHist F))
            (compactRealIntervalSearchBasisDecodeBHist
              (compactRealIntervalSearchBasisEncodeBHist D))
            (compactRealIntervalSearchBasisDecodeBHist
              (compactRealIntervalSearchBasisEncodeBHist W))
            (compactRealIntervalSearchBasisDecodeBHist
              (compactRealIntervalSearchBasisEncodeBHist R))
            (compactRealIntervalSearchBasisDecodeBHist
              (compactRealIntervalSearchBasisEncodeBHist E))
            (compactRealIntervalSearchBasisDecodeBHist
              (compactRealIntervalSearchBasisEncodeBHist H))
            (compactRealIntervalSearchBasisDecodeBHist
              (compactRealIntervalSearchBasisEncodeBHist C))
            (compactRealIntervalSearchBasisDecodeBHist
              (compactRealIntervalSearchBasisEncodeBHist P))
            (compactRealIntervalSearchBasisDecodeBHist
              (compactRealIntervalSearchBasisEncodeBHist N))) =
          some (CompactRealIntervalSearchBasisUp.mk K L F D W R E H C P N)
      rw [CompactRealIntervalSearchBasisTasteGate_single_carrier_alignment_decode K,
        CompactRealIntervalSearchBasisTasteGate_single_carrier_alignment_decode L,
        CompactRealIntervalSearchBasisTasteGate_single_carrier_alignment_decode F,
        CompactRealIntervalSearchBasisTasteGate_single_carrier_alignment_decode D,
        CompactRealIntervalSearchBasisTasteGate_single_carrier_alignment_decode W,
        CompactRealIntervalSearchBasisTasteGate_single_carrier_alignment_decode R,
        CompactRealIntervalSearchBasisTasteGate_single_carrier_alignment_decode E,
        CompactRealIntervalSearchBasisTasteGate_single_carrier_alignment_decode H,
        CompactRealIntervalSearchBasisTasteGate_single_carrier_alignment_decode C,
        CompactRealIntervalSearchBasisTasteGate_single_carrier_alignment_decode P,
        CompactRealIntervalSearchBasisTasteGate_single_carrier_alignment_decode N]

private theorem
    CompactRealIntervalSearchBasisTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompactRealIntervalSearchBasisUp} :
    compactRealIntervalSearchBasisToEventFlow x =
      compactRealIntervalSearchBasisToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactRealIntervalSearchBasisFromEventFlow
          (compactRealIntervalSearchBasisToEventFlow x) =
        compactRealIntervalSearchBasisFromEventFlow
          (compactRealIntervalSearchBasisToEventFlow y) :=
    congrArg compactRealIntervalSearchBasisFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CompactRealIntervalSearchBasisTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompactRealIntervalSearchBasisTasteGate_single_carrier_alignment_round_trip y)))

instance compactRealIntervalSearchBasisBHistCarrier :
    BHistCarrier CompactRealIntervalSearchBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactRealIntervalSearchBasisToEventFlow
  fromEventFlow := compactRealIntervalSearchBasisFromEventFlow

instance compactRealIntervalSearchBasisChapterTasteGate :
    ChapterTasteGate CompactRealIntervalSearchBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactRealIntervalSearchBasisFromEventFlow
          (compactRealIntervalSearchBasisToEventFlow x) =
        some x
    exact CompactRealIntervalSearchBasisTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CompactRealIntervalSearchBasisTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CompactRealIntervalSearchBasisTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      compactRealIntervalSearchBasisDecodeBHist
        (compactRealIntervalSearchBasisEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CompactRealIntervalSearchBasisUp) ∧
        Nonempty (ChapterTasteGate CompactRealIntervalSearchBasisUp) ∧
          compactRealIntervalSearchBasisEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CompactRealIntervalSearchBasisTasteGate_single_carrier_alignment_decode,
      ⟨compactRealIntervalSearchBasisBHistCarrier⟩,
      ⟨compactRealIntervalSearchBasisChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.CompactRealIntervalSearchBasisUp
