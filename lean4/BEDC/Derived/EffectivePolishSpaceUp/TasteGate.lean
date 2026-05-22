import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EffectivePolishSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EffectivePolishSpaceUp : Type where
  | mk (P D Q S R M L H C G N : BHist) : EffectivePolishSpaceUp
  deriving DecidableEq

def effectivePolishSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: effectivePolishSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: effectivePolishSpaceEncodeBHist h

def effectivePolishSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (effectivePolishSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (effectivePolishSpaceDecodeBHist tail)

private theorem EffectivePolishSpaceUpTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      effectivePolishSpaceDecodeBHist (effectivePolishSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def effectivePolishSpaceFields : EffectivePolishSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EffectivePolishSpaceUp.mk P D Q S R M L H C G N => [P, D, Q, S, R, M, L, H, C, G, N]

def effectivePolishSpaceToEventFlow : EffectivePolishSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | token => (effectivePolishSpaceFields token).map effectivePolishSpaceEncodeBHist

private def effectivePolishSpaceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => effectivePolishSpaceEventAtDefault index rest

def effectivePolishSpaceFromEventFlow (ef : EventFlow) : Option EffectivePolishSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (EffectivePolishSpaceUp.mk
      (effectivePolishSpaceDecodeBHist (effectivePolishSpaceEventAtDefault 0 ef))
      (effectivePolishSpaceDecodeBHist (effectivePolishSpaceEventAtDefault 1 ef))
      (effectivePolishSpaceDecodeBHist (effectivePolishSpaceEventAtDefault 2 ef))
      (effectivePolishSpaceDecodeBHist (effectivePolishSpaceEventAtDefault 3 ef))
      (effectivePolishSpaceDecodeBHist (effectivePolishSpaceEventAtDefault 4 ef))
      (effectivePolishSpaceDecodeBHist (effectivePolishSpaceEventAtDefault 5 ef))
      (effectivePolishSpaceDecodeBHist (effectivePolishSpaceEventAtDefault 6 ef))
      (effectivePolishSpaceDecodeBHist (effectivePolishSpaceEventAtDefault 7 ef))
      (effectivePolishSpaceDecodeBHist (effectivePolishSpaceEventAtDefault 8 ef))
      (effectivePolishSpaceDecodeBHist (effectivePolishSpaceEventAtDefault 9 ef))
      (effectivePolishSpaceDecodeBHist (effectivePolishSpaceEventAtDefault 10 ef)))

private theorem EffectivePolishSpaceUpTasteGate_single_carrier_alignment_round_trip :
    ∀ x : EffectivePolishSpaceUp,
      effectivePolishSpaceFromEventFlow (effectivePolishSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk P D Q S R M L H C G N =>
      change
        some
          (EffectivePolishSpaceUp.mk
            (effectivePolishSpaceDecodeBHist (effectivePolishSpaceEncodeBHist P))
            (effectivePolishSpaceDecodeBHist (effectivePolishSpaceEncodeBHist D))
            (effectivePolishSpaceDecodeBHist (effectivePolishSpaceEncodeBHist Q))
            (effectivePolishSpaceDecodeBHist (effectivePolishSpaceEncodeBHist S))
            (effectivePolishSpaceDecodeBHist (effectivePolishSpaceEncodeBHist R))
            (effectivePolishSpaceDecodeBHist (effectivePolishSpaceEncodeBHist M))
            (effectivePolishSpaceDecodeBHist (effectivePolishSpaceEncodeBHist L))
            (effectivePolishSpaceDecodeBHist (effectivePolishSpaceEncodeBHist H))
            (effectivePolishSpaceDecodeBHist (effectivePolishSpaceEncodeBHist C))
            (effectivePolishSpaceDecodeBHist (effectivePolishSpaceEncodeBHist G))
            (effectivePolishSpaceDecodeBHist (effectivePolishSpaceEncodeBHist N))) =
          some (EffectivePolishSpaceUp.mk P D Q S R M L H C G N)
      rw [EffectivePolishSpaceUpTasteGate_single_carrier_alignment_decode P,
        EffectivePolishSpaceUpTasteGate_single_carrier_alignment_decode D,
        EffectivePolishSpaceUpTasteGate_single_carrier_alignment_decode Q,
        EffectivePolishSpaceUpTasteGate_single_carrier_alignment_decode S,
        EffectivePolishSpaceUpTasteGate_single_carrier_alignment_decode R,
        EffectivePolishSpaceUpTasteGate_single_carrier_alignment_decode M,
        EffectivePolishSpaceUpTasteGate_single_carrier_alignment_decode L,
        EffectivePolishSpaceUpTasteGate_single_carrier_alignment_decode H,
        EffectivePolishSpaceUpTasteGate_single_carrier_alignment_decode C,
        EffectivePolishSpaceUpTasteGate_single_carrier_alignment_decode G,
        EffectivePolishSpaceUpTasteGate_single_carrier_alignment_decode N]

private theorem EffectivePolishSpaceUpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : EffectivePolishSpaceUp} :
    effectivePolishSpaceToEventFlow x = effectivePolishSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      effectivePolishSpaceFromEventFlow (effectivePolishSpaceToEventFlow x) =
        effectivePolishSpaceFromEventFlow (effectivePolishSpaceToEventFlow y) :=
    congrArg effectivePolishSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (EffectivePolishSpaceUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (EffectivePolishSpaceUpTasteGate_single_carrier_alignment_round_trip y)))

private theorem EffectivePolishSpaceUpTasteGate_single_carrier_alignment_fields :
    ∀ x y : EffectivePolishSpaceUp,
      effectivePolishSpaceFields x = effectivePolishSpaceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk P1 D1 Q1 S1 R1 M1 L1 H1 C1 G1 N1 =>
      cases y with
      | mk P2 D2 Q2 S2 R2 M2 L2 H2 C2 G2 N2 =>
          cases hfields
          rfl

instance effectivePolishSpaceBHistCarrier : BHistCarrier EffectivePolishSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := effectivePolishSpaceToEventFlow
  fromEventFlow := effectivePolishSpaceFromEventFlow

instance effectivePolishSpaceChapterTasteGate : ChapterTasteGate EffectivePolishSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change effectivePolishSpaceFromEventFlow (effectivePolishSpaceToEventFlow x) = some x
    exact EffectivePolishSpaceUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (EffectivePolishSpaceUpTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance effectivePolishSpaceFieldFaithful : FieldFaithful EffectivePolishSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := effectivePolishSpaceFields
  field_faithful := EffectivePolishSpaceUpTasteGate_single_carrier_alignment_fields

instance effectivePolishSpaceNontrivial : Nontrivial EffectivePolishSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨EffectivePolishSpaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      EffectivePolishSpaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem EffectivePolishSpaceUpTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate EffectivePolishSpaceUp) ∧ Nonempty (FieldFaithful EffectivePolishSpaceUp) ∧ Nonempty (BEDC.Meta.TasteGate.Nontrivial EffectivePolishSpaceUp) ∧ (∀ h : BHist, effectivePolishSpaceDecodeBHist (effectivePolishSpaceEncodeBHist h) = h) ∧ (∀ x : EffectivePolishSpaceUp, effectivePolishSpaceFromEventFlow (effectivePolishSpaceToEventFlow x) = some x) ∧ (∀ x y : EffectivePolishSpaceUp, effectivePolishSpaceToEventFlow x = effectivePolishSpaceToEventFlow y → x = y) ∧ effectivePolishSpaceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨effectivePolishSpaceChapterTasteGate⟩,
      ⟨effectivePolishSpaceFieldFaithful⟩,
      ⟨effectivePolishSpaceNontrivial⟩,
      EffectivePolishSpaceUpTasteGate_single_carrier_alignment_decode,
      EffectivePolishSpaceUpTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        EffectivePolishSpaceUpTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.EffectivePolishSpaceUp
