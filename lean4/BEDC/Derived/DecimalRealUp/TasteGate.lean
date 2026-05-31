import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DecimalRealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DecimalRealUp : Type where
  | mk (S A W T R L H C P N : BHist) : DecimalRealUp
  deriving DecidableEq

def decimalRealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: decimalRealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: decimalRealEncodeBHist h

def decimalRealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (decimalRealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (decimalRealDecodeBHist tail)

private theorem DecimalRealTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, decimalRealDecodeBHist (decimalRealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def decimalRealFields : DecimalRealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DecimalRealUp.mk S A W T R L H C P N => [S, A, W, T, R, L, H, C, P, N]

def decimalRealToEventFlow : DecimalRealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (decimalRealFields x).map decimalRealEncodeBHist

private def DecimalRealTasteGate_single_carrier_alignment_eventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      DecimalRealTasteGate_single_carrier_alignment_eventAt index rest

def decimalRealFromEventFlow (ef : EventFlow) : Option DecimalRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DecimalRealUp.mk
      (decimalRealDecodeBHist (DecimalRealTasteGate_single_carrier_alignment_eventAt 0 ef))
      (decimalRealDecodeBHist (DecimalRealTasteGate_single_carrier_alignment_eventAt 1 ef))
      (decimalRealDecodeBHist (DecimalRealTasteGate_single_carrier_alignment_eventAt 2 ef))
      (decimalRealDecodeBHist (DecimalRealTasteGate_single_carrier_alignment_eventAt 3 ef))
      (decimalRealDecodeBHist (DecimalRealTasteGate_single_carrier_alignment_eventAt 4 ef))
      (decimalRealDecodeBHist (DecimalRealTasteGate_single_carrier_alignment_eventAt 5 ef))
      (decimalRealDecodeBHist (DecimalRealTasteGate_single_carrier_alignment_eventAt 6 ef))
      (decimalRealDecodeBHist (DecimalRealTasteGate_single_carrier_alignment_eventAt 7 ef))
      (decimalRealDecodeBHist (DecimalRealTasteGate_single_carrier_alignment_eventAt 8 ef))
      (decimalRealDecodeBHist (DecimalRealTasteGate_single_carrier_alignment_eventAt 9 ef)))

private theorem DecimalRealTasteGate_single_carrier_alignment_round_trip
    (x : DecimalRealUp) :
    decimalRealFromEventFlow (decimalRealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S A W T R L H C P N =>
      change
        some
          (DecimalRealUp.mk
            (decimalRealDecodeBHist (decimalRealEncodeBHist S))
            (decimalRealDecodeBHist (decimalRealEncodeBHist A))
            (decimalRealDecodeBHist (decimalRealEncodeBHist W))
            (decimalRealDecodeBHist (decimalRealEncodeBHist T))
            (decimalRealDecodeBHist (decimalRealEncodeBHist R))
            (decimalRealDecodeBHist (decimalRealEncodeBHist L))
            (decimalRealDecodeBHist (decimalRealEncodeBHist H))
            (decimalRealDecodeBHist (decimalRealEncodeBHist C))
            (decimalRealDecodeBHist (decimalRealEncodeBHist P))
            (decimalRealDecodeBHist (decimalRealEncodeBHist N))) =
          some (DecimalRealUp.mk S A W T R L H C P N)
      rw [DecimalRealTasteGate_single_carrier_alignment_decode_encode S,
        DecimalRealTasteGate_single_carrier_alignment_decode_encode A,
        DecimalRealTasteGate_single_carrier_alignment_decode_encode W,
        DecimalRealTasteGate_single_carrier_alignment_decode_encode T,
        DecimalRealTasteGate_single_carrier_alignment_decode_encode R,
        DecimalRealTasteGate_single_carrier_alignment_decode_encode L,
        DecimalRealTasteGate_single_carrier_alignment_decode_encode H,
        DecimalRealTasteGate_single_carrier_alignment_decode_encode C,
        DecimalRealTasteGate_single_carrier_alignment_decode_encode P,
        DecimalRealTasteGate_single_carrier_alignment_decode_encode N]

private theorem DecimalRealTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DecimalRealUp} :
    decimalRealToEventFlow x = decimalRealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      decimalRealFromEventFlow (decimalRealToEventFlow x) =
        decimalRealFromEventFlow (decimalRealToEventFlow y) :=
    congrArg decimalRealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DecimalRealTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DecimalRealTasteGate_single_carrier_alignment_round_trip y)))

private theorem DecimalRealTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : DecimalRealUp, decimalRealFields x = decimalRealFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S₁ A₁ W₁ T₁ R₁ L₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ A₂ W₂ T₂ R₂ L₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance decimalRealBHistCarrier : BHistCarrier DecimalRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := decimalRealToEventFlow
  fromEventFlow := decimalRealFromEventFlow

instance decimalRealChapterTasteGate : ChapterTasteGate DecimalRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change decimalRealFromEventFlow (decimalRealToEventFlow x) = some x
    exact DecimalRealTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DecimalRealTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance decimalRealFieldFaithful : FieldFaithful DecimalRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := decimalRealFields
  field_faithful := DecimalRealTasteGate_single_carrier_alignment_fields_faithful

instance decimalRealNontrivial : BEDC.Meta.TasteGate.Nontrivial DecimalRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DecimalRealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DecimalRealUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DecimalRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  decimalRealChapterTasteGate

theorem DecimalRealTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate DecimalRealUp) ∧
      Nonempty (FieldFaithful DecimalRealUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial DecimalRealUp) ∧
          (∀ h : BHist, decimalRealDecodeBHist (decimalRealEncodeBHist h) = h) ∧
            (∀ x : DecimalRealUp,
              decimalRealFromEventFlow (decimalRealToEventFlow x) = some x) ∧
              (∀ x y : DecimalRealUp,
                decimalRealToEventFlow x = decimalRealToEventFlow y → x = y) ∧
                decimalRealEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨decimalRealChapterTasteGate⟩,
      ⟨decimalRealFieldFaithful⟩,
      ⟨decimalRealNontrivial⟩,
      DecimalRealTasteGate_single_carrier_alignment_decode_encode,
      DecimalRealTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => DecimalRealTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.DecimalRealUp
