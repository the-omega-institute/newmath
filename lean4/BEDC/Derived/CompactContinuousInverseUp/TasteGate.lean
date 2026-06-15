import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactContinuousInverseUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactContinuousInverseUp : Type where
  | mk (K F B S G M H C P N : BHist) : CompactContinuousInverseUp
  deriving DecidableEq

def compactContinuousInverseEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactContinuousInverseEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactContinuousInverseEncodeBHist h

def compactContinuousInverseDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactContinuousInverseDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactContinuousInverseDecodeBHist tail)

private theorem CompactContinuousInverseTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, compactContinuousInverseDecodeBHist
      (compactContinuousInverseEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactContinuousInverseFields : CompactContinuousInverseUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactContinuousInverseUp.mk K F B S G M H C P N => [K, F, B, S, G, M, H, C, P, N]

def compactContinuousInverseToEventFlow : CompactContinuousInverseUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (compactContinuousInverseFields x).map compactContinuousInverseEncodeBHist

private def compactContinuousInverseEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => compactContinuousInverseEventAtDefault index rest

def compactContinuousInverseFromEventFlow
    (ef : EventFlow) : Option CompactContinuousInverseUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompactContinuousInverseUp.mk
      (compactContinuousInverseDecodeBHist (compactContinuousInverseEventAtDefault 0 ef))
      (compactContinuousInverseDecodeBHist (compactContinuousInverseEventAtDefault 1 ef))
      (compactContinuousInverseDecodeBHist (compactContinuousInverseEventAtDefault 2 ef))
      (compactContinuousInverseDecodeBHist (compactContinuousInverseEventAtDefault 3 ef))
      (compactContinuousInverseDecodeBHist (compactContinuousInverseEventAtDefault 4 ef))
      (compactContinuousInverseDecodeBHist (compactContinuousInverseEventAtDefault 5 ef))
      (compactContinuousInverseDecodeBHist (compactContinuousInverseEventAtDefault 6 ef))
      (compactContinuousInverseDecodeBHist (compactContinuousInverseEventAtDefault 7 ef))
      (compactContinuousInverseDecodeBHist (compactContinuousInverseEventAtDefault 8 ef))
      (compactContinuousInverseDecodeBHist (compactContinuousInverseEventAtDefault 9 ef)))

private theorem CompactContinuousInverseTasteGate_single_carrier_alignment_round_trip
    (x : CompactContinuousInverseUp) :
    compactContinuousInverseFromEventFlow (compactContinuousInverseToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk K F B S G M H C P N =>
      change
        some
          (CompactContinuousInverseUp.mk
            (compactContinuousInverseDecodeBHist (compactContinuousInverseEncodeBHist K))
            (compactContinuousInverseDecodeBHist (compactContinuousInverseEncodeBHist F))
            (compactContinuousInverseDecodeBHist (compactContinuousInverseEncodeBHist B))
            (compactContinuousInverseDecodeBHist (compactContinuousInverseEncodeBHist S))
            (compactContinuousInverseDecodeBHist (compactContinuousInverseEncodeBHist G))
            (compactContinuousInverseDecodeBHist (compactContinuousInverseEncodeBHist M))
            (compactContinuousInverseDecodeBHist (compactContinuousInverseEncodeBHist H))
            (compactContinuousInverseDecodeBHist (compactContinuousInverseEncodeBHist C))
            (compactContinuousInverseDecodeBHist (compactContinuousInverseEncodeBHist P))
            (compactContinuousInverseDecodeBHist (compactContinuousInverseEncodeBHist N))) =
          some (CompactContinuousInverseUp.mk K F B S G M H C P N)
      rw [CompactContinuousInverseTasteGate_single_carrier_alignment_decode_encode K,
        CompactContinuousInverseTasteGate_single_carrier_alignment_decode_encode F,
        CompactContinuousInverseTasteGate_single_carrier_alignment_decode_encode B,
        CompactContinuousInverseTasteGate_single_carrier_alignment_decode_encode S,
        CompactContinuousInverseTasteGate_single_carrier_alignment_decode_encode G,
        CompactContinuousInverseTasteGate_single_carrier_alignment_decode_encode M,
        CompactContinuousInverseTasteGate_single_carrier_alignment_decode_encode H,
        CompactContinuousInverseTasteGate_single_carrier_alignment_decode_encode C,
        CompactContinuousInverseTasteGate_single_carrier_alignment_decode_encode P,
        CompactContinuousInverseTasteGate_single_carrier_alignment_decode_encode N]

private theorem CompactContinuousInverseTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompactContinuousInverseUp} :
    compactContinuousInverseToEventFlow x = compactContinuousInverseToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactContinuousInverseFromEventFlow (compactContinuousInverseToEventFlow x) =
        compactContinuousInverseFromEventFlow (compactContinuousInverseToEventFlow y) :=
    congrArg compactContinuousInverseFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CompactContinuousInverseTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompactContinuousInverseTasteGate_single_carrier_alignment_round_trip y)))

private theorem CompactContinuousInverseTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : CompactContinuousInverseUp, compactContinuousInverseFields x =
      compactContinuousInverseFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K1 F1 B1 S1 G1 M1 H1 C1 P1 N1 =>
      cases y with
      | mk K2 F2 B2 S2 G2 M2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance compactContinuousInverseBHistCarrier : BHistCarrier CompactContinuousInverseUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactContinuousInverseToEventFlow
  fromEventFlow := compactContinuousInverseFromEventFlow

instance compactContinuousInverseChapterTasteGate :
    ChapterTasteGate CompactContinuousInverseUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change compactContinuousInverseFromEventFlow
      (compactContinuousInverseToEventFlow x) = some x
    exact CompactContinuousInverseTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CompactContinuousInverseTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance compactContinuousInverseFieldFaithful : FieldFaithful CompactContinuousInverseUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := compactContinuousInverseFields
  field_faithful := CompactContinuousInverseTasteGate_single_carrier_alignment_fields_faithful

theorem CompactContinuousInverseTasteGate_single_carrier_alignment :
    (∀ h : BHist, compactContinuousInverseDecodeBHist
      (compactContinuousInverseEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CompactContinuousInverseUp) ∧
        Nonempty (ChapterTasteGate CompactContinuousInverseUp) ∧
          compactContinuousInverseEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CompactContinuousInverseTasteGate_single_carrier_alignment_decode_encode,
      ⟨compactContinuousInverseBHistCarrier⟩,
      ⟨compactContinuousInverseChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.CompactContinuousInverseUp
