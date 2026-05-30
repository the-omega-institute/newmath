import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyRealEqualityUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyRealEqualityUp : Type where
  | mk (L0 L1 S0 S1 R0 R1 D H C P N : BHist) : CauchyRealEqualityUp
  deriving DecidableEq

def cauchyRealEqualityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyRealEqualityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyRealEqualityEncodeBHist h

def cauchyRealEqualityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyRealEqualityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyRealEqualityDecodeBHist tail)

private theorem CauchyRealEqualityTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyRealEqualityDecodeBHist (cauchyRealEqualityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyRealEqualityFields : CauchyRealEqualityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyRealEqualityUp.mk L0 L1 S0 S1 R0 R1 D H C P N =>
      [L0, L1, S0, S1, R0, R1, D, H, C, P, N]

def cauchyRealEqualityToEventFlow : CauchyRealEqualityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyRealEqualityFields x).map cauchyRealEqualityEncodeBHist

private def cauchyRealEqualityEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyRealEqualityEventAt index rest

def cauchyRealEqualityFromEventFlow : EventFlow → Option CauchyRealEqualityUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (CauchyRealEqualityUp.mk
          (cauchyRealEqualityDecodeBHist (cauchyRealEqualityEventAt 0 ef))
          (cauchyRealEqualityDecodeBHist (cauchyRealEqualityEventAt 1 ef))
          (cauchyRealEqualityDecodeBHist (cauchyRealEqualityEventAt 2 ef))
          (cauchyRealEqualityDecodeBHist (cauchyRealEqualityEventAt 3 ef))
          (cauchyRealEqualityDecodeBHist (cauchyRealEqualityEventAt 4 ef))
          (cauchyRealEqualityDecodeBHist (cauchyRealEqualityEventAt 5 ef))
          (cauchyRealEqualityDecodeBHist (cauchyRealEqualityEventAt 6 ef))
          (cauchyRealEqualityDecodeBHist (cauchyRealEqualityEventAt 7 ef))
          (cauchyRealEqualityDecodeBHist (cauchyRealEqualityEventAt 8 ef))
          (cauchyRealEqualityDecodeBHist (cauchyRealEqualityEventAt 9 ef))
          (cauchyRealEqualityDecodeBHist (cauchyRealEqualityEventAt 10 ef)))

private theorem CauchyRealEqualityTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyRealEqualityUp,
      cauchyRealEqualityFromEventFlow (cauchyRealEqualityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L0 L1 S0 S1 R0 R1 D H C P N =>
      change
        some
          (CauchyRealEqualityUp.mk
            (cauchyRealEqualityDecodeBHist (cauchyRealEqualityEncodeBHist L0))
            (cauchyRealEqualityDecodeBHist (cauchyRealEqualityEncodeBHist L1))
            (cauchyRealEqualityDecodeBHist (cauchyRealEqualityEncodeBHist S0))
            (cauchyRealEqualityDecodeBHist (cauchyRealEqualityEncodeBHist S1))
            (cauchyRealEqualityDecodeBHist (cauchyRealEqualityEncodeBHist R0))
            (cauchyRealEqualityDecodeBHist (cauchyRealEqualityEncodeBHist R1))
            (cauchyRealEqualityDecodeBHist (cauchyRealEqualityEncodeBHist D))
            (cauchyRealEqualityDecodeBHist (cauchyRealEqualityEncodeBHist H))
            (cauchyRealEqualityDecodeBHist (cauchyRealEqualityEncodeBHist C))
            (cauchyRealEqualityDecodeBHist (cauchyRealEqualityEncodeBHist P))
            (cauchyRealEqualityDecodeBHist (cauchyRealEqualityEncodeBHist N))) =
          some (CauchyRealEqualityUp.mk L0 L1 S0 S1 R0 R1 D H C P N)
      rw [CauchyRealEqualityTasteGate_single_carrier_alignment_decode_encode L0,
        CauchyRealEqualityTasteGate_single_carrier_alignment_decode_encode L1,
        CauchyRealEqualityTasteGate_single_carrier_alignment_decode_encode S0,
        CauchyRealEqualityTasteGate_single_carrier_alignment_decode_encode S1,
        CauchyRealEqualityTasteGate_single_carrier_alignment_decode_encode R0,
        CauchyRealEqualityTasteGate_single_carrier_alignment_decode_encode R1,
        CauchyRealEqualityTasteGate_single_carrier_alignment_decode_encode D,
        CauchyRealEqualityTasteGate_single_carrier_alignment_decode_encode H,
        CauchyRealEqualityTasteGate_single_carrier_alignment_decode_encode C,
        CauchyRealEqualityTasteGate_single_carrier_alignment_decode_encode P,
        CauchyRealEqualityTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyRealEqualityTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyRealEqualityUp} :
    cauchyRealEqualityToEventFlow x = cauchyRealEqualityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyRealEqualityFromEventFlow (cauchyRealEqualityToEventFlow x) =
        cauchyRealEqualityFromEventFlow (cauchyRealEqualityToEventFlow y) :=
    congrArg cauchyRealEqualityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyRealEqualityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyRealEqualityTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyRealEqualityTasteGate_single_carrier_alignment_fields :
    ∀ x y : CauchyRealEqualityUp,
      cauchyRealEqualityFields x = cauchyRealEqualityFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk L0₁ L1₁ S0₁ S1₁ R0₁ R1₁ D₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk L0₂ L1₂ S0₂ S1₂ R0₂ R1₂ D₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance cauchyRealEqualityBHistCarrier : BHistCarrier CauchyRealEqualityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyRealEqualityToEventFlow
  fromEventFlow := cauchyRealEqualityFromEventFlow

instance cauchyRealEqualityChapterTasteGate : ChapterTasteGate CauchyRealEqualityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyRealEqualityFromEventFlow (cauchyRealEqualityToEventFlow x) = some x
    exact CauchyRealEqualityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyRealEqualityTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cauchyRealEqualityFieldFaithful : FieldFaithful CauchyRealEqualityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyRealEqualityFields
  field_faithful := CauchyRealEqualityTasteGate_single_carrier_alignment_fields

instance cauchyRealEqualityNontrivial : Nontrivial CauchyRealEqualityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyRealEqualityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyRealEqualityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem CauchyRealEqualityTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CauchyRealEqualityUp) ∧
      Nonempty (FieldFaithful CauchyRealEqualityUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial CauchyRealEqualityUp) ∧
          (∀ h : BHist, cauchyRealEqualityDecodeBHist (cauchyRealEqualityEncodeBHist h) = h) ∧
            (∀ x : CauchyRealEqualityUp,
              cauchyRealEqualityFromEventFlow (cauchyRealEqualityToEventFlow x) = some x) ∧
              (∀ x y : CauchyRealEqualityUp,
                cauchyRealEqualityToEventFlow x = cauchyRealEqualityToEventFlow y → x = y) ∧
                cauchyRealEqualityEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨cauchyRealEqualityChapterTasteGate⟩, ⟨cauchyRealEqualityFieldFaithful⟩,
      ⟨cauchyRealEqualityNontrivial⟩,
      CauchyRealEqualityTasteGate_single_carrier_alignment_decode_encode,
      CauchyRealEqualityTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CauchyRealEqualityTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyRealEqualityUp.TasteGate
