import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactLipschitzUniformHandoffUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactLipschitzUniformHandoffUp : Type where
  | mk (K G T R U E H C P N : BHist) : CompactLipschitzUniformHandoffUp
  deriving DecidableEq

def compactLipschitzUniformHandoffEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactLipschitzUniformHandoffEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactLipschitzUniformHandoffEncodeBHist h

def compactLipschitzUniformHandoffDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactLipschitzUniformHandoffDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactLipschitzUniformHandoffDecodeBHist tail)

private theorem CompactLipschitzUniformHandoffTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      compactLipschitzUniformHandoffDecodeBHist
        (compactLipschitzUniformHandoffEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactLipschitzUniformHandoffFields :
    CompactLipschitzUniformHandoffUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactLipschitzUniformHandoffUp.mk K G T R U E H C P N =>
      [K, G, T, R, U, E, H, C, P, N]

def compactLipschitzUniformHandoffToEventFlow :
    CompactLipschitzUniformHandoffUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (compactLipschitzUniformHandoffFields x).map
      compactLipschitzUniformHandoffEncodeBHist

private def compactLipschitzUniformHandoffEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => compactLipschitzUniformHandoffEventAt index rest

def compactLipschitzUniformHandoffFromEventFlow
    (ef : EventFlow) : Option CompactLipschitzUniformHandoffUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompactLipschitzUniformHandoffUp.mk
      (compactLipschitzUniformHandoffDecodeBHist
        (compactLipschitzUniformHandoffEventAt 0 ef))
      (compactLipschitzUniformHandoffDecodeBHist
        (compactLipschitzUniformHandoffEventAt 1 ef))
      (compactLipschitzUniformHandoffDecodeBHist
        (compactLipschitzUniformHandoffEventAt 2 ef))
      (compactLipschitzUniformHandoffDecodeBHist
        (compactLipschitzUniformHandoffEventAt 3 ef))
      (compactLipschitzUniformHandoffDecodeBHist
        (compactLipschitzUniformHandoffEventAt 4 ef))
      (compactLipschitzUniformHandoffDecodeBHist
        (compactLipschitzUniformHandoffEventAt 5 ef))
      (compactLipschitzUniformHandoffDecodeBHist
        (compactLipschitzUniformHandoffEventAt 6 ef))
      (compactLipschitzUniformHandoffDecodeBHist
        (compactLipschitzUniformHandoffEventAt 7 ef))
      (compactLipschitzUniformHandoffDecodeBHist
        (compactLipschitzUniformHandoffEventAt 8 ef))
      (compactLipschitzUniformHandoffDecodeBHist
        (compactLipschitzUniformHandoffEventAt 9 ef)))

private theorem CompactLipschitzUniformHandoffTasteGate_single_carrier_alignment_round_trip
    (x : CompactLipschitzUniformHandoffUp) :
    compactLipschitzUniformHandoffFromEventFlow
      (compactLipschitzUniformHandoffToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk K G T R U E H C P N =>
      change
        some
          (CompactLipschitzUniformHandoffUp.mk
            (compactLipschitzUniformHandoffDecodeBHist
              (compactLipschitzUniformHandoffEncodeBHist K))
            (compactLipschitzUniformHandoffDecodeBHist
              (compactLipschitzUniformHandoffEncodeBHist G))
            (compactLipschitzUniformHandoffDecodeBHist
              (compactLipschitzUniformHandoffEncodeBHist T))
            (compactLipschitzUniformHandoffDecodeBHist
              (compactLipschitzUniformHandoffEncodeBHist R))
            (compactLipschitzUniformHandoffDecodeBHist
              (compactLipschitzUniformHandoffEncodeBHist U))
            (compactLipschitzUniformHandoffDecodeBHist
              (compactLipschitzUniformHandoffEncodeBHist E))
            (compactLipschitzUniformHandoffDecodeBHist
              (compactLipschitzUniformHandoffEncodeBHist H))
            (compactLipschitzUniformHandoffDecodeBHist
              (compactLipschitzUniformHandoffEncodeBHist C))
            (compactLipschitzUniformHandoffDecodeBHist
              (compactLipschitzUniformHandoffEncodeBHist P))
            (compactLipschitzUniformHandoffDecodeBHist
              (compactLipschitzUniformHandoffEncodeBHist N))) =
          some (CompactLipschitzUniformHandoffUp.mk K G T R U E H C P N)
      rw [CompactLipschitzUniformHandoffTasteGate_single_carrier_alignment_decode_encode K,
        CompactLipschitzUniformHandoffTasteGate_single_carrier_alignment_decode_encode G,
        CompactLipschitzUniformHandoffTasteGate_single_carrier_alignment_decode_encode T,
        CompactLipschitzUniformHandoffTasteGate_single_carrier_alignment_decode_encode R,
        CompactLipschitzUniformHandoffTasteGate_single_carrier_alignment_decode_encode U,
        CompactLipschitzUniformHandoffTasteGate_single_carrier_alignment_decode_encode E,
        CompactLipschitzUniformHandoffTasteGate_single_carrier_alignment_decode_encode H,
        CompactLipschitzUniformHandoffTasteGate_single_carrier_alignment_decode_encode C,
        CompactLipschitzUniformHandoffTasteGate_single_carrier_alignment_decode_encode P,
        CompactLipschitzUniformHandoffTasteGate_single_carrier_alignment_decode_encode N]

private theorem CompactLipschitzUniformHandoffTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompactLipschitzUniformHandoffUp} :
    compactLipschitzUniformHandoffToEventFlow x =
      compactLipschitzUniformHandoffToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactLipschitzUniformHandoffFromEventFlow
          (compactLipschitzUniformHandoffToEventFlow x) =
        compactLipschitzUniformHandoffFromEventFlow
          (compactLipschitzUniformHandoffToEventFlow y) :=
    congrArg compactLipschitzUniformHandoffFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CompactLipschitzUniformHandoffTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompactLipschitzUniformHandoffTasteGate_single_carrier_alignment_round_trip y)))

instance compactLipschitzUniformHandoffBHistCarrier :
    BHistCarrier CompactLipschitzUniformHandoffUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactLipschitzUniformHandoffToEventFlow
  fromEventFlow := compactLipschitzUniformHandoffFromEventFlow

instance compactLipschitzUniformHandoffChapterTasteGate :
    ChapterTasteGate CompactLipschitzUniformHandoffUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactLipschitzUniformHandoffFromEventFlow
        (compactLipschitzUniformHandoffToEventFlow x) = some x
    exact CompactLipschitzUniformHandoffTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CompactLipschitzUniformHandoffTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def CompactLipschitzUniformHandoffTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate CompactLipschitzUniformHandoffUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactLipschitzUniformHandoffChapterTasteGate

theorem CompactLipschitzUniformHandoffTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      compactLipschitzUniformHandoffDecodeBHist
        (compactLipschitzUniformHandoffEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CompactLipschitzUniformHandoffUp) ∧
        Nonempty (ChapterTasteGate CompactLipschitzUniformHandoffUp) ∧
          compactLipschitzUniformHandoffEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CompactLipschitzUniformHandoffTasteGate_single_carrier_alignment_decode_encode,
      ⟨compactLipschitzUniformHandoffBHistCarrier⟩,
      ⟨compactLipschitzUniformHandoffChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.CompactLipschitzUniformHandoffUp
