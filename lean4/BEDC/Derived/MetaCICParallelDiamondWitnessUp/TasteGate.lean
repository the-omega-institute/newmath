import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICParallelDiamondWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICParallelDiamondWitnessUp : Type where
  | mk (T L R S J B A O H C P N : BHist) : MetaCICParallelDiamondWitnessUp
  deriving DecidableEq

def metaCICParallelDiamondWitnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaCICParallelDiamondWitnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaCICParallelDiamondWitnessEncodeBHist h

def metaCICParallelDiamondWitnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaCICParallelDiamondWitnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaCICParallelDiamondWitnessDecodeBHist tail)

private theorem metaCICParallelDiamondWitnessDecode_encode :
    ∀ h : BHist,
      metaCICParallelDiamondWitnessDecodeBHist
        (metaCICParallelDiamondWitnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metaCICParallelDiamondWitnessFields :
    MetaCICParallelDiamondWitnessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICParallelDiamondWitnessUp.mk T L R S J B A O H C P N =>
      [T, L, R, S, J, B, A, O, H, C, P, N]

def metaCICParallelDiamondWitnessToEventFlow :
    MetaCICParallelDiamondWitnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICParallelDiamondWitnessUp.mk T L R S J B A O H C P N =>
      [metaCICParallelDiamondWitnessEncodeBHist T,
        metaCICParallelDiamondWitnessEncodeBHist L,
        metaCICParallelDiamondWitnessEncodeBHist R,
        metaCICParallelDiamondWitnessEncodeBHist S,
        metaCICParallelDiamondWitnessEncodeBHist J,
        metaCICParallelDiamondWitnessEncodeBHist B,
        metaCICParallelDiamondWitnessEncodeBHist A,
        metaCICParallelDiamondWitnessEncodeBHist O,
        metaCICParallelDiamondWitnessEncodeBHist H,
        metaCICParallelDiamondWitnessEncodeBHist C,
        metaCICParallelDiamondWitnessEncodeBHist P,
        metaCICParallelDiamondWitnessEncodeBHist N]

private def metaCICParallelDiamondWitnessEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => metaCICParallelDiamondWitnessEventAt index rest

def metaCICParallelDiamondWitnessFromEventFlow :
    EventFlow → Option MetaCICParallelDiamondWitnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (MetaCICParallelDiamondWitnessUp.mk
        (metaCICParallelDiamondWitnessDecodeBHist
          (metaCICParallelDiamondWitnessEventAt 0 ef))
        (metaCICParallelDiamondWitnessDecodeBHist
          (metaCICParallelDiamondWitnessEventAt 1 ef))
        (metaCICParallelDiamondWitnessDecodeBHist
          (metaCICParallelDiamondWitnessEventAt 2 ef))
        (metaCICParallelDiamondWitnessDecodeBHist
          (metaCICParallelDiamondWitnessEventAt 3 ef))
        (metaCICParallelDiamondWitnessDecodeBHist
          (metaCICParallelDiamondWitnessEventAt 4 ef))
        (metaCICParallelDiamondWitnessDecodeBHist
          (metaCICParallelDiamondWitnessEventAt 5 ef))
        (metaCICParallelDiamondWitnessDecodeBHist
          (metaCICParallelDiamondWitnessEventAt 6 ef))
        (metaCICParallelDiamondWitnessDecodeBHist
          (metaCICParallelDiamondWitnessEventAt 7 ef))
        (metaCICParallelDiamondWitnessDecodeBHist
          (metaCICParallelDiamondWitnessEventAt 8 ef))
        (metaCICParallelDiamondWitnessDecodeBHist
          (metaCICParallelDiamondWitnessEventAt 9 ef))
        (metaCICParallelDiamondWitnessDecodeBHist
          (metaCICParallelDiamondWitnessEventAt 10 ef))
        (metaCICParallelDiamondWitnessDecodeBHist
          (metaCICParallelDiamondWitnessEventAt 11 ef)))

private theorem metaCICParallelDiamondWitness_round_trip :
    ∀ x : MetaCICParallelDiamondWitnessUp,
      metaCICParallelDiamondWitnessFromEventFlow
          (metaCICParallelDiamondWitnessToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T L R S J B A O H C P N =>
      change
        some
            (MetaCICParallelDiamondWitnessUp.mk
              (metaCICParallelDiamondWitnessDecodeBHist
                (metaCICParallelDiamondWitnessEncodeBHist T))
              (metaCICParallelDiamondWitnessDecodeBHist
                (metaCICParallelDiamondWitnessEncodeBHist L))
              (metaCICParallelDiamondWitnessDecodeBHist
                (metaCICParallelDiamondWitnessEncodeBHist R))
              (metaCICParallelDiamondWitnessDecodeBHist
                (metaCICParallelDiamondWitnessEncodeBHist S))
              (metaCICParallelDiamondWitnessDecodeBHist
                (metaCICParallelDiamondWitnessEncodeBHist J))
              (metaCICParallelDiamondWitnessDecodeBHist
                (metaCICParallelDiamondWitnessEncodeBHist B))
              (metaCICParallelDiamondWitnessDecodeBHist
                (metaCICParallelDiamondWitnessEncodeBHist A))
              (metaCICParallelDiamondWitnessDecodeBHist
                (metaCICParallelDiamondWitnessEncodeBHist O))
              (metaCICParallelDiamondWitnessDecodeBHist
                (metaCICParallelDiamondWitnessEncodeBHist H))
              (metaCICParallelDiamondWitnessDecodeBHist
                (metaCICParallelDiamondWitnessEncodeBHist C))
              (metaCICParallelDiamondWitnessDecodeBHist
                (metaCICParallelDiamondWitnessEncodeBHist P))
              (metaCICParallelDiamondWitnessDecodeBHist
                (metaCICParallelDiamondWitnessEncodeBHist N))) =
          some (MetaCICParallelDiamondWitnessUp.mk T L R S J B A O H C P N)
      rw [metaCICParallelDiamondWitnessDecode_encode T,
        metaCICParallelDiamondWitnessDecode_encode L,
        metaCICParallelDiamondWitnessDecode_encode R,
        metaCICParallelDiamondWitnessDecode_encode S,
        metaCICParallelDiamondWitnessDecode_encode J,
        metaCICParallelDiamondWitnessDecode_encode B,
        metaCICParallelDiamondWitnessDecode_encode A,
        metaCICParallelDiamondWitnessDecode_encode O,
        metaCICParallelDiamondWitnessDecode_encode H,
        metaCICParallelDiamondWitnessDecode_encode C,
        metaCICParallelDiamondWitnessDecode_encode P,
        metaCICParallelDiamondWitnessDecode_encode N]

private theorem metaCICParallelDiamondWitnessToEventFlow_injective
    {x y : MetaCICParallelDiamondWitnessUp} :
    metaCICParallelDiamondWitnessToEventFlow x =
      metaCICParallelDiamondWitnessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaCICParallelDiamondWitnessFromEventFlow
          (metaCICParallelDiamondWitnessToEventFlow x) =
        metaCICParallelDiamondWitnessFromEventFlow
          (metaCICParallelDiamondWitnessToEventFlow y) :=
    congrArg metaCICParallelDiamondWitnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metaCICParallelDiamondWitness_round_trip x).symm
      (Eq.trans hread (metaCICParallelDiamondWitness_round_trip y)))

private theorem metaCICParallelDiamondWitnessFieldFaithfulProof :
    ∀ x y : MetaCICParallelDiamondWitnessUp,
      metaCICParallelDiamondWitnessFields x =
        metaCICParallelDiamondWitnessFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T₁ L₁ R₁ S₁ J₁ B₁ A₁ O₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk T₂ L₂ R₂ S₂ J₂ B₂ A₂ O₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance metaCICParallelDiamondWitnessBHistCarrier :
    BHistCarrier MetaCICParallelDiamondWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaCICParallelDiamondWitnessToEventFlow
  fromEventFlow := metaCICParallelDiamondWitnessFromEventFlow

instance metaCICParallelDiamondWitnessChapterTasteGate :
    ChapterTasteGate MetaCICParallelDiamondWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metaCICParallelDiamondWitnessFromEventFlow
          (metaCICParallelDiamondWitnessToEventFlow x) =
        some x
    exact metaCICParallelDiamondWitness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metaCICParallelDiamondWitnessToEventFlow_injective heq)

instance metaCICParallelDiamondWitnessFieldFaithful :
    FieldFaithful MetaCICParallelDiamondWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metaCICParallelDiamondWitnessFields
  field_faithful := metaCICParallelDiamondWitnessFieldFaithfulProof

instance metaCICParallelDiamondWitnessNontrivial :
    BEDC.Meta.TasteGate.Nontrivial MetaCICParallelDiamondWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetaCICParallelDiamondWitnessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      MetaCICParallelDiamondWitnessUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MetaCICParallelDiamondWitnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metaCICParallelDiamondWitnessChapterTasteGate

def taste_gate_witness :
    FieldFaithful MetaCICParallelDiamondWitnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metaCICParallelDiamondWitnessFieldFaithful

theorem MetaCICParallelDiamondWitnessTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate MetaCICParallelDiamondWitnessUp) ∧
      Nonempty (FieldFaithful MetaCICParallelDiamondWitnessUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial MetaCICParallelDiamondWitnessUp) ∧
      (∀ h : BHist,
        metaCICParallelDiamondWitnessDecodeBHist
            (metaCICParallelDiamondWitnessEncodeBHist h) =
          h) ∧
      (∀ x : MetaCICParallelDiamondWitnessUp,
        metaCICParallelDiamondWitnessFromEventFlow
            (metaCICParallelDiamondWitnessToEventFlow x) =
          some x) ∧
      (∀ x y : MetaCICParallelDiamondWitnessUp,
        metaCICParallelDiamondWitnessToEventFlow x =
          metaCICParallelDiamondWitnessToEventFlow y → x = y) ∧
      metaCICParallelDiamondWitnessEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨metaCICParallelDiamondWitnessChapterTasteGate⟩
  constructor
  · exact ⟨metaCICParallelDiamondWitnessFieldFaithful⟩
  constructor
  · exact ⟨metaCICParallelDiamondWitnessNontrivial⟩
  constructor
  · exact metaCICParallelDiamondWitnessDecode_encode
  constructor
  · exact metaCICParallelDiamondWitness_round_trip
  constructor
  · intro x y
    exact metaCICParallelDiamondWitnessToEventFlow_injective
  · rfl

end BEDC.Derived.MetaCICParallelDiamondWitnessUp
