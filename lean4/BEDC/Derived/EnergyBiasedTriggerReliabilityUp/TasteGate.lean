import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EnergyBiasedTriggerReliabilityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EnergyBiasedTriggerReliabilityUp : Type where
  | mk (W B V A G F L R H C P N : BHist) : EnergyBiasedTriggerReliabilityUp
  deriving DecidableEq

def energyBiasedTriggerReliabilityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: energyBiasedTriggerReliabilityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: energyBiasedTriggerReliabilityEncodeBHist h

def energyBiasedTriggerReliabilityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (energyBiasedTriggerReliabilityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (energyBiasedTriggerReliabilityDecodeBHist tail)

private theorem
    EnergyBiasedTriggerReliabilityTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      energyBiasedTriggerReliabilityDecodeBHist
        (energyBiasedTriggerReliabilityEncodeBHist h) =
          h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def energyBiasedTriggerReliabilityFields :
    EnergyBiasedTriggerReliabilityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EnergyBiasedTriggerReliabilityUp.mk W B V A G F L R H C P N =>
      [W, B, V, A, G, F, L, R, H, C, P, N]

def energyBiasedTriggerReliabilityToEventFlow :
    EnergyBiasedTriggerReliabilityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (energyBiasedTriggerReliabilityFields x).map
      energyBiasedTriggerReliabilityEncodeBHist

private def energyBiasedTriggerReliabilityEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      energyBiasedTriggerReliabilityEventAtDefault index rest

def energyBiasedTriggerReliabilityFromEventFlow
    (ef : EventFlow) : Option EnergyBiasedTriggerReliabilityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (EnergyBiasedTriggerReliabilityUp.mk
      (energyBiasedTriggerReliabilityDecodeBHist
        (energyBiasedTriggerReliabilityEventAtDefault 0 ef))
      (energyBiasedTriggerReliabilityDecodeBHist
        (energyBiasedTriggerReliabilityEventAtDefault 1 ef))
      (energyBiasedTriggerReliabilityDecodeBHist
        (energyBiasedTriggerReliabilityEventAtDefault 2 ef))
      (energyBiasedTriggerReliabilityDecodeBHist
        (energyBiasedTriggerReliabilityEventAtDefault 3 ef))
      (energyBiasedTriggerReliabilityDecodeBHist
        (energyBiasedTriggerReliabilityEventAtDefault 4 ef))
      (energyBiasedTriggerReliabilityDecodeBHist
        (energyBiasedTriggerReliabilityEventAtDefault 5 ef))
      (energyBiasedTriggerReliabilityDecodeBHist
        (energyBiasedTriggerReliabilityEventAtDefault 6 ef))
      (energyBiasedTriggerReliabilityDecodeBHist
        (energyBiasedTriggerReliabilityEventAtDefault 7 ef))
      (energyBiasedTriggerReliabilityDecodeBHist
        (energyBiasedTriggerReliabilityEventAtDefault 8 ef))
      (energyBiasedTriggerReliabilityDecodeBHist
        (energyBiasedTriggerReliabilityEventAtDefault 9 ef))
      (energyBiasedTriggerReliabilityDecodeBHist
        (energyBiasedTriggerReliabilityEventAtDefault 10 ef))
      (energyBiasedTriggerReliabilityDecodeBHist
        (energyBiasedTriggerReliabilityEventAtDefault 11 ef)))

private theorem EnergyBiasedTriggerReliabilityTasteGate_single_carrier_alignment_round_trip
    (x : EnergyBiasedTriggerReliabilityUp) :
    energyBiasedTriggerReliabilityFromEventFlow
      (energyBiasedTriggerReliabilityToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk W B V A G F L R H C P N =>
      change
        some
          (EnergyBiasedTriggerReliabilityUp.mk
            (energyBiasedTriggerReliabilityDecodeBHist
              (energyBiasedTriggerReliabilityEncodeBHist W))
            (energyBiasedTriggerReliabilityDecodeBHist
              (energyBiasedTriggerReliabilityEncodeBHist B))
            (energyBiasedTriggerReliabilityDecodeBHist
              (energyBiasedTriggerReliabilityEncodeBHist V))
            (energyBiasedTriggerReliabilityDecodeBHist
              (energyBiasedTriggerReliabilityEncodeBHist A))
            (energyBiasedTriggerReliabilityDecodeBHist
              (energyBiasedTriggerReliabilityEncodeBHist G))
            (energyBiasedTriggerReliabilityDecodeBHist
              (energyBiasedTriggerReliabilityEncodeBHist F))
            (energyBiasedTriggerReliabilityDecodeBHist
              (energyBiasedTriggerReliabilityEncodeBHist L))
            (energyBiasedTriggerReliabilityDecodeBHist
              (energyBiasedTriggerReliabilityEncodeBHist R))
            (energyBiasedTriggerReliabilityDecodeBHist
              (energyBiasedTriggerReliabilityEncodeBHist H))
            (energyBiasedTriggerReliabilityDecodeBHist
              (energyBiasedTriggerReliabilityEncodeBHist C))
            (energyBiasedTriggerReliabilityDecodeBHist
              (energyBiasedTriggerReliabilityEncodeBHist P))
            (energyBiasedTriggerReliabilityDecodeBHist
              (energyBiasedTriggerReliabilityEncodeBHist N))) =
          some (EnergyBiasedTriggerReliabilityUp.mk W B V A G F L R H C P N)
      rw [
        EnergyBiasedTriggerReliabilityTasteGate_single_carrier_alignment_decode_encode W,
        EnergyBiasedTriggerReliabilityTasteGate_single_carrier_alignment_decode_encode B,
        EnergyBiasedTriggerReliabilityTasteGate_single_carrier_alignment_decode_encode V,
        EnergyBiasedTriggerReliabilityTasteGate_single_carrier_alignment_decode_encode A,
        EnergyBiasedTriggerReliabilityTasteGate_single_carrier_alignment_decode_encode G,
        EnergyBiasedTriggerReliabilityTasteGate_single_carrier_alignment_decode_encode F,
        EnergyBiasedTriggerReliabilityTasteGate_single_carrier_alignment_decode_encode L,
        EnergyBiasedTriggerReliabilityTasteGate_single_carrier_alignment_decode_encode R,
        EnergyBiasedTriggerReliabilityTasteGate_single_carrier_alignment_decode_encode H,
        EnergyBiasedTriggerReliabilityTasteGate_single_carrier_alignment_decode_encode C,
        EnergyBiasedTriggerReliabilityTasteGate_single_carrier_alignment_decode_encode P,
        EnergyBiasedTriggerReliabilityTasteGate_single_carrier_alignment_decode_encode N]

private theorem EnergyBiasedTriggerReliabilityTasteGate_single_carrier_alignment_injective
    {x y : EnergyBiasedTriggerReliabilityUp} :
    energyBiasedTriggerReliabilityToEventFlow x =
      energyBiasedTriggerReliabilityToEventFlow y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      energyBiasedTriggerReliabilityFromEventFlow
          (energyBiasedTriggerReliabilityToEventFlow x) =
        energyBiasedTriggerReliabilityFromEventFlow
          (energyBiasedTriggerReliabilityToEventFlow y) :=
    congrArg energyBiasedTriggerReliabilityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (EnergyBiasedTriggerReliabilityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (EnergyBiasedTriggerReliabilityTasteGate_single_carrier_alignment_round_trip y)))

private theorem EnergyBiasedTriggerReliabilityTasteGate_single_carrier_alignment_fields :
    ∀ x y : EnergyBiasedTriggerReliabilityUp,
      energyBiasedTriggerReliabilityFields x =
        energyBiasedTriggerReliabilityFields y →
          x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk W₁ B₁ V₁ A₁ G₁ F₁ L₁ R₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk W₂ B₂ V₂ A₂ G₂ F₂ L₂ R₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance energyBiasedTriggerReliabilityBHistCarrier :
    BHistCarrier EnergyBiasedTriggerReliabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := energyBiasedTriggerReliabilityToEventFlow
  fromEventFlow := energyBiasedTriggerReliabilityFromEventFlow

instance energyBiasedTriggerReliabilityChapterTasteGate :
    ChapterTasteGate EnergyBiasedTriggerReliabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      energyBiasedTriggerReliabilityFromEventFlow
        (energyBiasedTriggerReliabilityToEventFlow x) = some x
    exact EnergyBiasedTriggerReliabilityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (EnergyBiasedTriggerReliabilityTasteGate_single_carrier_alignment_injective heq)

instance energyBiasedTriggerReliabilityFieldFaithful :
    FieldFaithful EnergyBiasedTriggerReliabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := energyBiasedTriggerReliabilityFields
  field_faithful :=
    EnergyBiasedTriggerReliabilityTasteGate_single_carrier_alignment_fields

instance energyBiasedTriggerReliabilityNontrivial :
    BEDC.Meta.TasteGate.Nontrivial EnergyBiasedTriggerReliabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨EnergyBiasedTriggerReliabilityUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      EnergyBiasedTriggerReliabilityUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def EnergyBiasedTriggerReliabilityTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate EnergyBiasedTriggerReliabilityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  energyBiasedTriggerReliabilityChapterTasteGate

theorem EnergyBiasedTriggerReliabilityTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      energyBiasedTriggerReliabilityDecodeBHist
        (energyBiasedTriggerReliabilityEncodeBHist h) = h) ∧
      (∀ x : EnergyBiasedTriggerReliabilityUp,
        energyBiasedTriggerReliabilityFromEventFlow
          (energyBiasedTriggerReliabilityToEventFlow x) =
            some x) ∧
        (∀ x y : EnergyBiasedTriggerReliabilityUp,
          energyBiasedTriggerReliabilityToEventFlow x =
            energyBiasedTriggerReliabilityToEventFlow y →
              x = y) ∧
          energyBiasedTriggerReliabilityEncodeBHist BHist.Empty =
            ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact EnergyBiasedTriggerReliabilityTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact EnergyBiasedTriggerReliabilityTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact EnergyBiasedTriggerReliabilityTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.EnergyBiasedTriggerReliabilityUp
