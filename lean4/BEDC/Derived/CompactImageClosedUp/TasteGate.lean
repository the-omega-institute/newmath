import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactImageClosedUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactImageClosedUp : Type where
  | mk (K F I S C M R H T P N : BHist) : CompactImageClosedUp
  deriving DecidableEq

def compactImageClosedEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactImageClosedEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactImageClosedEncodeBHist h

def compactImageClosedDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactImageClosedDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactImageClosedDecodeBHist tail)

private theorem CompactImageClosedTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, compactImageClosedDecodeBHist (compactImageClosedEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactImageClosedToEventFlow : CompactImageClosedUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CompactImageClosedUp.mk K F I S C M R H T P N =>
      [[BMark.b1, BMark.b0, BMark.b1],
        compactImageClosedEncodeBHist K,
        compactImageClosedEncodeBHist F,
        compactImageClosedEncodeBHist I,
        compactImageClosedEncodeBHist S,
        compactImageClosedEncodeBHist C,
        compactImageClosedEncodeBHist M,
        compactImageClosedEncodeBHist R,
        compactImageClosedEncodeBHist H,
        compactImageClosedEncodeBHist T,
        compactImageClosedEncodeBHist P,
        compactImageClosedEncodeBHist N]

private def compactImageClosedEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => compactImageClosedEventAtDefault index rest

def compactImageClosedFromEventFlow (ef : EventFlow) : Option CompactImageClosedUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompactImageClosedUp.mk
      (compactImageClosedDecodeBHist (compactImageClosedEventAtDefault 1 ef))
      (compactImageClosedDecodeBHist (compactImageClosedEventAtDefault 2 ef))
      (compactImageClosedDecodeBHist (compactImageClosedEventAtDefault 3 ef))
      (compactImageClosedDecodeBHist (compactImageClosedEventAtDefault 4 ef))
      (compactImageClosedDecodeBHist (compactImageClosedEventAtDefault 5 ef))
      (compactImageClosedDecodeBHist (compactImageClosedEventAtDefault 6 ef))
      (compactImageClosedDecodeBHist (compactImageClosedEventAtDefault 7 ef))
      (compactImageClosedDecodeBHist (compactImageClosedEventAtDefault 8 ef))
      (compactImageClosedDecodeBHist (compactImageClosedEventAtDefault 9 ef))
      (compactImageClosedDecodeBHist (compactImageClosedEventAtDefault 10 ef))
      (compactImageClosedDecodeBHist (compactImageClosedEventAtDefault 11 ef)))

private theorem CompactImageClosedTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CompactImageClosedUp,
      compactImageClosedFromEventFlow (compactImageClosedToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K F I S C M R H T P N =>
      change
        some
          (CompactImageClosedUp.mk
            (compactImageClosedDecodeBHist (compactImageClosedEncodeBHist K))
            (compactImageClosedDecodeBHist (compactImageClosedEncodeBHist F))
            (compactImageClosedDecodeBHist (compactImageClosedEncodeBHist I))
            (compactImageClosedDecodeBHist (compactImageClosedEncodeBHist S))
            (compactImageClosedDecodeBHist (compactImageClosedEncodeBHist C))
            (compactImageClosedDecodeBHist (compactImageClosedEncodeBHist M))
            (compactImageClosedDecodeBHist (compactImageClosedEncodeBHist R))
            (compactImageClosedDecodeBHist (compactImageClosedEncodeBHist H))
            (compactImageClosedDecodeBHist (compactImageClosedEncodeBHist T))
            (compactImageClosedDecodeBHist (compactImageClosedEncodeBHist P))
            (compactImageClosedDecodeBHist (compactImageClosedEncodeBHist N))) =
          some (CompactImageClosedUp.mk K F I S C M R H T P N)
      rw [CompactImageClosedTasteGate_single_carrier_alignment_decode K,
        CompactImageClosedTasteGate_single_carrier_alignment_decode F,
        CompactImageClosedTasteGate_single_carrier_alignment_decode I,
        CompactImageClosedTasteGate_single_carrier_alignment_decode S,
        CompactImageClosedTasteGate_single_carrier_alignment_decode C,
        CompactImageClosedTasteGate_single_carrier_alignment_decode M,
        CompactImageClosedTasteGate_single_carrier_alignment_decode R,
        CompactImageClosedTasteGate_single_carrier_alignment_decode H,
        CompactImageClosedTasteGate_single_carrier_alignment_decode T,
        CompactImageClosedTasteGate_single_carrier_alignment_decode P,
        CompactImageClosedTasteGate_single_carrier_alignment_decode N]

private theorem CompactImageClosedTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompactImageClosedUp} :
    compactImageClosedToEventFlow x = compactImageClosedToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactImageClosedFromEventFlow (compactImageClosedToEventFlow x) =
        compactImageClosedFromEventFlow (compactImageClosedToEventFlow y) :=
    congrArg compactImageClosedFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CompactImageClosedTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CompactImageClosedTasteGate_single_carrier_alignment_round_trip y)))

private def compactImageClosedFields : CompactImageClosedUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactImageClosedUp.mk K F I S C M R H T P N => [K, F, I, S, C, M, R, H, T, P, N]

private theorem CompactImageClosedTasteGate_single_carrier_alignment_fields :
    ∀ x y : CompactImageClosedUp, compactImageClosedFields x = compactImageClosedFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K1 F1 I1 S1 C1 M1 R1 H1 T1 P1 N1 =>
      cases y with
      | mk K2 F2 I2 S2 C2 M2 R2 H2 T2 P2 N2 =>
          cases hfields
          rfl

instance compactImageClosedBHistCarrier : BHistCarrier CompactImageClosedUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactImageClosedToEventFlow
  fromEventFlow := compactImageClosedFromEventFlow

instance compactImageClosedChapterTasteGate : ChapterTasteGate CompactImageClosedUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change compactImageClosedFromEventFlow (compactImageClosedToEventFlow x) = some x
    exact CompactImageClosedTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CompactImageClosedTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance compactImageClosedFieldFaithful : FieldFaithful CompactImageClosedUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := compactImageClosedFields
  field_faithful := CompactImageClosedTasteGate_single_carrier_alignment_fields

instance compactImageClosedNontrivial : Nontrivial CompactImageClosedUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompactImageClosedUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CompactImageClosedUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CompactImageClosedUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactImageClosedChapterTasteGate

theorem CompactImageClosedTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CompactImageClosedUp) ∧
      Nonempty (FieldFaithful CompactImageClosedUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial CompactImageClosedUp) ∧
          (∀ h : BHist,
            compactImageClosedDecodeBHist (compactImageClosedEncodeBHist h) = h) ∧
            (∀ x : CompactImageClosedUp,
              compactImageClosedFromEventFlow (compactImageClosedToEventFlow x) = some x) ∧
              (∀ x y : CompactImageClosedUp,
                compactImageClosedToEventFlow x = compactImageClosedToEventFlow y → x = y) ∧
                compactImageClosedEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨compactImageClosedChapterTasteGate⟩,
      ⟨compactImageClosedFieldFaithful⟩,
      ⟨compactImageClosedNontrivial⟩,
      CompactImageClosedTasteGate_single_carrier_alignment_decode,
      CompactImageClosedTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => CompactImageClosedTasteGate_single_carrier_alignment_toEventFlow_injective
        heq),
      rfl⟩

end BEDC.Derived.CompactImageClosedUp
