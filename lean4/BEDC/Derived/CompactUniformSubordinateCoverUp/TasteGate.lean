import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactUniformSubordinateCoverUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactUniformSubordinateCoverUp : Type where
  | mk (K G Q F L M H C P N : BHist) : CompactUniformSubordinateCoverUp
  deriving DecidableEq

def compactUniformSubordinateCoverEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactUniformSubordinateCoverEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactUniformSubordinateCoverEncodeBHist h

def compactUniformSubordinateCoverDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactUniformSubordinateCoverDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactUniformSubordinateCoverDecodeBHist tail)

private theorem CompactUniformSubordinateCoverTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      compactUniformSubordinateCoverDecodeBHist
        (compactUniformSubordinateCoverEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactUniformSubordinateCoverToEventFlow :
    CompactUniformSubordinateCoverUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CompactUniformSubordinateCoverUp.mk K G Q F L M H C P N =>
      [compactUniformSubordinateCoverEncodeBHist K,
        compactUniformSubordinateCoverEncodeBHist G,
        compactUniformSubordinateCoverEncodeBHist Q,
        compactUniformSubordinateCoverEncodeBHist F,
        compactUniformSubordinateCoverEncodeBHist L,
        compactUniformSubordinateCoverEncodeBHist M,
        compactUniformSubordinateCoverEncodeBHist H,
        compactUniformSubordinateCoverEncodeBHist C,
        compactUniformSubordinateCoverEncodeBHist P,
        compactUniformSubordinateCoverEncodeBHist N]

private def compactUniformSubordinateCoverEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      compactUniformSubordinateCoverEventAtDefault index rest

def compactUniformSubordinateCoverFromEventFlow :
    EventFlow → Option CompactUniformSubordinateCoverUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (CompactUniformSubordinateCoverUp.mk
        (compactUniformSubordinateCoverDecodeBHist
          (compactUniformSubordinateCoverEventAtDefault 0 ef))
        (compactUniformSubordinateCoverDecodeBHist
          (compactUniformSubordinateCoverEventAtDefault 1 ef))
        (compactUniformSubordinateCoverDecodeBHist
          (compactUniformSubordinateCoverEventAtDefault 2 ef))
        (compactUniformSubordinateCoverDecodeBHist
          (compactUniformSubordinateCoverEventAtDefault 3 ef))
        (compactUniformSubordinateCoverDecodeBHist
          (compactUniformSubordinateCoverEventAtDefault 4 ef))
        (compactUniformSubordinateCoverDecodeBHist
          (compactUniformSubordinateCoverEventAtDefault 5 ef))
        (compactUniformSubordinateCoverDecodeBHist
          (compactUniformSubordinateCoverEventAtDefault 6 ef))
        (compactUniformSubordinateCoverDecodeBHist
          (compactUniformSubordinateCoverEventAtDefault 7 ef))
        (compactUniformSubordinateCoverDecodeBHist
          (compactUniformSubordinateCoverEventAtDefault 8 ef))
        (compactUniformSubordinateCoverDecodeBHist
          (compactUniformSubordinateCoverEventAtDefault 9 ef)))

private theorem CompactUniformSubordinateCoverTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CompactUniformSubordinateCoverUp,
      compactUniformSubordinateCoverFromEventFlow
        (compactUniformSubordinateCoverToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K G Q F L M H C P N =>
      change
        some
          (CompactUniformSubordinateCoverUp.mk
            (compactUniformSubordinateCoverDecodeBHist
              (compactUniformSubordinateCoverEncodeBHist K))
            (compactUniformSubordinateCoverDecodeBHist
              (compactUniformSubordinateCoverEncodeBHist G))
            (compactUniformSubordinateCoverDecodeBHist
              (compactUniformSubordinateCoverEncodeBHist Q))
            (compactUniformSubordinateCoverDecodeBHist
              (compactUniformSubordinateCoverEncodeBHist F))
            (compactUniformSubordinateCoverDecodeBHist
              (compactUniformSubordinateCoverEncodeBHist L))
            (compactUniformSubordinateCoverDecodeBHist
              (compactUniformSubordinateCoverEncodeBHist M))
            (compactUniformSubordinateCoverDecodeBHist
              (compactUniformSubordinateCoverEncodeBHist H))
            (compactUniformSubordinateCoverDecodeBHist
              (compactUniformSubordinateCoverEncodeBHist C))
            (compactUniformSubordinateCoverDecodeBHist
              (compactUniformSubordinateCoverEncodeBHist P))
            (compactUniformSubordinateCoverDecodeBHist
              (compactUniformSubordinateCoverEncodeBHist N))) =
          some (CompactUniformSubordinateCoverUp.mk K G Q F L M H C P N)
      rw [CompactUniformSubordinateCoverTasteGate_single_carrier_alignment_decode_encode K,
        CompactUniformSubordinateCoverTasteGate_single_carrier_alignment_decode_encode G,
        CompactUniformSubordinateCoverTasteGate_single_carrier_alignment_decode_encode Q,
        CompactUniformSubordinateCoverTasteGate_single_carrier_alignment_decode_encode F,
        CompactUniformSubordinateCoverTasteGate_single_carrier_alignment_decode_encode L,
        CompactUniformSubordinateCoverTasteGate_single_carrier_alignment_decode_encode M,
        CompactUniformSubordinateCoverTasteGate_single_carrier_alignment_decode_encode H,
        CompactUniformSubordinateCoverTasteGate_single_carrier_alignment_decode_encode C,
        CompactUniformSubordinateCoverTasteGate_single_carrier_alignment_decode_encode P,
        CompactUniformSubordinateCoverTasteGate_single_carrier_alignment_decode_encode N]

private theorem CompactUniformSubordinateCoverTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompactUniformSubordinateCoverUp} :
    compactUniformSubordinateCoverToEventFlow x =
      compactUniformSubordinateCoverToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactUniformSubordinateCoverFromEventFlow
          (compactUniformSubordinateCoverToEventFlow x) =
        compactUniformSubordinateCoverFromEventFlow
          (compactUniformSubordinateCoverToEventFlow y) :=
    congrArg compactUniformSubordinateCoverFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CompactUniformSubordinateCoverTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompactUniformSubordinateCoverTasteGate_single_carrier_alignment_round_trip y)))

instance compactUniformSubordinateCoverBHistCarrier :
    BHistCarrier CompactUniformSubordinateCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactUniformSubordinateCoverToEventFlow
  fromEventFlow := compactUniformSubordinateCoverFromEventFlow

instance compactUniformSubordinateCoverChapterTasteGate :
    ChapterTasteGate CompactUniformSubordinateCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change compactUniformSubordinateCoverFromEventFlow
      (compactUniformSubordinateCoverToEventFlow x) = some x
    exact CompactUniformSubordinateCoverTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CompactUniformSubordinateCoverTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate CompactUniformSubordinateCoverUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactUniformSubordinateCoverChapterTasteGate

theorem CompactUniformSubordinateCoverTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      compactUniformSubordinateCoverDecodeBHist
        (compactUniformSubordinateCoverEncodeBHist h) = h) ∧
      compactUniformSubordinateCoverEncodeBHist BHist.Empty = ([] : RawEvent) ∧
      compactUniformSubordinateCoverDecodeBHist [BMark.b0] =
        BHist.e0 BHist.Empty ∧
      Nonempty (BHistCarrier CompactUniformSubordinateCoverUp) ∧
      Nonempty (ChapterTasteGate CompactUniformSubordinateCoverUp) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CompactUniformSubordinateCoverTasteGate_single_carrier_alignment_decode_encode,
      rfl, rfl, ⟨compactUniformSubordinateCoverBHistCarrier⟩,
      ⟨compactUniformSubordinateCoverChapterTasteGate⟩⟩

end BEDC.Derived.CompactUniformSubordinateCoverUp
