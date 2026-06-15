import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.QuotientFreeCompletionSealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive QuotientFreeCompletionSealUp : Type where
  | mk (D S R E L H C P N : BHist) : QuotientFreeCompletionSealUp
  deriving DecidableEq

def quotientFreeCompletionSealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: quotientFreeCompletionSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: quotientFreeCompletionSealEncodeBHist h

def quotientFreeCompletionSealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (quotientFreeCompletionSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (quotientFreeCompletionSealDecodeBHist tail)

private theorem QuotientFreeCompletionSealTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      quotientFreeCompletionSealDecodeBHist
        (quotientFreeCompletionSealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def quotientFreeCompletionSealFields : QuotientFreeCompletionSealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | QuotientFreeCompletionSealUp.mk D S R E L H C P N => [D, S, R, E, L, H, C, P, N]

def quotientFreeCompletionSealToEventFlow : QuotientFreeCompletionSealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (quotientFreeCompletionSealFields x).map quotientFreeCompletionSealEncodeBHist

private def QuotientFreeCompletionSealTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      QuotientFreeCompletionSealTasteGate_single_carrier_alignment_eventAt index rest

def quotientFreeCompletionSealFromEventFlow : EventFlow → Option QuotientFreeCompletionSealUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (QuotientFreeCompletionSealUp.mk
          (quotientFreeCompletionSealDecodeBHist
            (QuotientFreeCompletionSealTasteGate_single_carrier_alignment_eventAt 0 ef))
          (quotientFreeCompletionSealDecodeBHist
            (QuotientFreeCompletionSealTasteGate_single_carrier_alignment_eventAt 1 ef))
          (quotientFreeCompletionSealDecodeBHist
            (QuotientFreeCompletionSealTasteGate_single_carrier_alignment_eventAt 2 ef))
          (quotientFreeCompletionSealDecodeBHist
            (QuotientFreeCompletionSealTasteGate_single_carrier_alignment_eventAt 3 ef))
          (quotientFreeCompletionSealDecodeBHist
            (QuotientFreeCompletionSealTasteGate_single_carrier_alignment_eventAt 4 ef))
          (quotientFreeCompletionSealDecodeBHist
            (QuotientFreeCompletionSealTasteGate_single_carrier_alignment_eventAt 5 ef))
          (quotientFreeCompletionSealDecodeBHist
            (QuotientFreeCompletionSealTasteGate_single_carrier_alignment_eventAt 6 ef))
          (quotientFreeCompletionSealDecodeBHist
            (QuotientFreeCompletionSealTasteGate_single_carrier_alignment_eventAt 7 ef))
          (quotientFreeCompletionSealDecodeBHist
            (QuotientFreeCompletionSealTasteGate_single_carrier_alignment_eventAt 8 ef)))

private theorem QuotientFreeCompletionSealTasteGate_single_carrier_alignment_round_trip :
    ∀ x : QuotientFreeCompletionSealUp,
      quotientFreeCompletionSealFromEventFlow
        (quotientFreeCompletionSealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D S R E L H C P N =>
      change
        some
          (QuotientFreeCompletionSealUp.mk
            (quotientFreeCompletionSealDecodeBHist
              (quotientFreeCompletionSealEncodeBHist D))
            (quotientFreeCompletionSealDecodeBHist
              (quotientFreeCompletionSealEncodeBHist S))
            (quotientFreeCompletionSealDecodeBHist
              (quotientFreeCompletionSealEncodeBHist R))
            (quotientFreeCompletionSealDecodeBHist
              (quotientFreeCompletionSealEncodeBHist E))
            (quotientFreeCompletionSealDecodeBHist
              (quotientFreeCompletionSealEncodeBHist L))
            (quotientFreeCompletionSealDecodeBHist
              (quotientFreeCompletionSealEncodeBHist H))
            (quotientFreeCompletionSealDecodeBHist
              (quotientFreeCompletionSealEncodeBHist C))
            (quotientFreeCompletionSealDecodeBHist
              (quotientFreeCompletionSealEncodeBHist P))
            (quotientFreeCompletionSealDecodeBHist
              (quotientFreeCompletionSealEncodeBHist N))) =
          some (QuotientFreeCompletionSealUp.mk D S R E L H C P N)
      rw [QuotientFreeCompletionSealTasteGate_single_carrier_alignment_decode D,
        QuotientFreeCompletionSealTasteGate_single_carrier_alignment_decode S,
        QuotientFreeCompletionSealTasteGate_single_carrier_alignment_decode R,
        QuotientFreeCompletionSealTasteGate_single_carrier_alignment_decode E,
        QuotientFreeCompletionSealTasteGate_single_carrier_alignment_decode L,
        QuotientFreeCompletionSealTasteGate_single_carrier_alignment_decode H,
        QuotientFreeCompletionSealTasteGate_single_carrier_alignment_decode C,
        QuotientFreeCompletionSealTasteGate_single_carrier_alignment_decode P,
        QuotientFreeCompletionSealTasteGate_single_carrier_alignment_decode N]

private theorem QuotientFreeCompletionSealTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : QuotientFreeCompletionSealUp} :
    quotientFreeCompletionSealToEventFlow x =
      quotientFreeCompletionSealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      quotientFreeCompletionSealFromEventFlow
          (quotientFreeCompletionSealToEventFlow x) =
        quotientFreeCompletionSealFromEventFlow
          (quotientFreeCompletionSealToEventFlow y) :=
    congrArg quotientFreeCompletionSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (QuotientFreeCompletionSealTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (QuotientFreeCompletionSealTasteGate_single_carrier_alignment_round_trip y)))

private theorem QuotientFreeCompletionSealTasteGate_single_carrier_alignment_fields :
    ∀ x y : QuotientFreeCompletionSealUp,
      quotientFreeCompletionSealFields x = quotientFreeCompletionSealFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D₁ S₁ R₁ E₁ L₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk D₂ S₂ R₂ E₂ L₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance quotientFreeCompletionSealBHistCarrier : BHistCarrier QuotientFreeCompletionSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := quotientFreeCompletionSealToEventFlow
  fromEventFlow := quotientFreeCompletionSealFromEventFlow

instance quotientFreeCompletionSealChapterTasteGate :
    ChapterTasteGate QuotientFreeCompletionSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := QuotientFreeCompletionSealTasteGate_single_carrier_alignment_round_trip
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (QuotientFreeCompletionSealTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance quotientFreeCompletionSealFieldFaithful :
    FieldFaithful QuotientFreeCompletionSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := quotientFreeCompletionSealFields
  field_faithful := QuotientFreeCompletionSealTasteGate_single_carrier_alignment_fields

instance quotientFreeCompletionSealNontrivial : Nontrivial QuotientFreeCompletionSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨QuotientFreeCompletionSealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      QuotientFreeCompletionSealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem QuotientFreeCompletionSealTasteGate_single_carrier_alignment :
    (forall h : BHist,
      quotientFreeCompletionSealDecodeBHist (quotientFreeCompletionSealEncodeBHist h) = h) ∧
      (forall x : QuotientFreeCompletionSealUp,
        quotientFreeCompletionSealFromEventFlow
          (quotientFreeCompletionSealToEventFlow x) = some x) ∧
        (forall x y : QuotientFreeCompletionSealUp,
          quotientFreeCompletionSealToEventFlow x =
            quotientFreeCompletionSealToEventFlow y -> x = y) ∧
          quotientFreeCompletionSealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact QuotientFreeCompletionSealTasteGate_single_carrier_alignment_decode
  · constructor
    · exact QuotientFreeCompletionSealTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y
        exact QuotientFreeCompletionSealTasteGate_single_carrier_alignment_toEventFlow_injective
      · rfl

end BEDC.Derived.QuotientFreeCompletionSealUp
