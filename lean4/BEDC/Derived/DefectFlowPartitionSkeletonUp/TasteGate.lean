import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DefectFlowPartitionSkeletonUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DefectFlowPartitionSkeletonUp : Type where
  | mk (B I L T A M X H C P N : BHist) : DefectFlowPartitionSkeletonUp
  deriving DecidableEq

def defectFlowPartitionSkeletonEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: defectFlowPartitionSkeletonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: defectFlowPartitionSkeletonEncodeBHist h

def defectFlowPartitionSkeletonDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (defectFlowPartitionSkeletonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (defectFlowPartitionSkeletonDecodeBHist tail)

private theorem DefectFlowPartitionSkeletonTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      defectFlowPartitionSkeletonDecodeBHist (defectFlowPartitionSkeletonEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def defectFlowPartitionSkeletonFields : DefectFlowPartitionSkeletonUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DefectFlowPartitionSkeletonUp.mk B I L T A M X H C P N =>
      [B, I, L, T, A, M, X, H, C, P, N]

def defectFlowPartitionSkeletonToEventFlow : DefectFlowPartitionSkeletonUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (defectFlowPartitionSkeletonFields x).map defectFlowPartitionSkeletonEncodeBHist

private def defectFlowPartitionSkeletonEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => defectFlowPartitionSkeletonEventAt index rest

def defectFlowPartitionSkeletonFromEventFlow
    (ef : EventFlow) : Option DefectFlowPartitionSkeletonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DefectFlowPartitionSkeletonUp.mk
      (defectFlowPartitionSkeletonDecodeBHist (defectFlowPartitionSkeletonEventAt 0 ef))
      (defectFlowPartitionSkeletonDecodeBHist (defectFlowPartitionSkeletonEventAt 1 ef))
      (defectFlowPartitionSkeletonDecodeBHist (defectFlowPartitionSkeletonEventAt 2 ef))
      (defectFlowPartitionSkeletonDecodeBHist (defectFlowPartitionSkeletonEventAt 3 ef))
      (defectFlowPartitionSkeletonDecodeBHist (defectFlowPartitionSkeletonEventAt 4 ef))
      (defectFlowPartitionSkeletonDecodeBHist (defectFlowPartitionSkeletonEventAt 5 ef))
      (defectFlowPartitionSkeletonDecodeBHist (defectFlowPartitionSkeletonEventAt 6 ef))
      (defectFlowPartitionSkeletonDecodeBHist (defectFlowPartitionSkeletonEventAt 7 ef))
      (defectFlowPartitionSkeletonDecodeBHist (defectFlowPartitionSkeletonEventAt 8 ef))
      (defectFlowPartitionSkeletonDecodeBHist (defectFlowPartitionSkeletonEventAt 9 ef))
      (defectFlowPartitionSkeletonDecodeBHist (defectFlowPartitionSkeletonEventAt 10 ef)))

private theorem DefectFlowPartitionSkeletonTasteGate_single_carrier_alignment_round_trip
    (x : DefectFlowPartitionSkeletonUp) :
    defectFlowPartitionSkeletonFromEventFlow (defectFlowPartitionSkeletonToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk B I L T A M X H C P N =>
      change
        some
          (DefectFlowPartitionSkeletonUp.mk
            (defectFlowPartitionSkeletonDecodeBHist
              (defectFlowPartitionSkeletonEncodeBHist B))
            (defectFlowPartitionSkeletonDecodeBHist
              (defectFlowPartitionSkeletonEncodeBHist I))
            (defectFlowPartitionSkeletonDecodeBHist
              (defectFlowPartitionSkeletonEncodeBHist L))
            (defectFlowPartitionSkeletonDecodeBHist
              (defectFlowPartitionSkeletonEncodeBHist T))
            (defectFlowPartitionSkeletonDecodeBHist
              (defectFlowPartitionSkeletonEncodeBHist A))
            (defectFlowPartitionSkeletonDecodeBHist
              (defectFlowPartitionSkeletonEncodeBHist M))
            (defectFlowPartitionSkeletonDecodeBHist
              (defectFlowPartitionSkeletonEncodeBHist X))
            (defectFlowPartitionSkeletonDecodeBHist
              (defectFlowPartitionSkeletonEncodeBHist H))
            (defectFlowPartitionSkeletonDecodeBHist
              (defectFlowPartitionSkeletonEncodeBHist C))
            (defectFlowPartitionSkeletonDecodeBHist
              (defectFlowPartitionSkeletonEncodeBHist P))
            (defectFlowPartitionSkeletonDecodeBHist
              (defectFlowPartitionSkeletonEncodeBHist N))) =
          some (DefectFlowPartitionSkeletonUp.mk B I L T A M X H C P N)
      rw [DefectFlowPartitionSkeletonTasteGate_single_carrier_alignment_decode B,
        DefectFlowPartitionSkeletonTasteGate_single_carrier_alignment_decode I,
        DefectFlowPartitionSkeletonTasteGate_single_carrier_alignment_decode L,
        DefectFlowPartitionSkeletonTasteGate_single_carrier_alignment_decode T,
        DefectFlowPartitionSkeletonTasteGate_single_carrier_alignment_decode A,
        DefectFlowPartitionSkeletonTasteGate_single_carrier_alignment_decode M,
        DefectFlowPartitionSkeletonTasteGate_single_carrier_alignment_decode X,
        DefectFlowPartitionSkeletonTasteGate_single_carrier_alignment_decode H,
        DefectFlowPartitionSkeletonTasteGate_single_carrier_alignment_decode C,
        DefectFlowPartitionSkeletonTasteGate_single_carrier_alignment_decode P,
        DefectFlowPartitionSkeletonTasteGate_single_carrier_alignment_decode N]

theorem defectFlowPartitionSkeletonToEventFlow_injective
    {x y : DefectFlowPartitionSkeletonUp} :
    defectFlowPartitionSkeletonToEventFlow x =
        defectFlowPartitionSkeletonToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      defectFlowPartitionSkeletonFromEventFlow
          (defectFlowPartitionSkeletonToEventFlow x) =
        defectFlowPartitionSkeletonFromEventFlow
          (defectFlowPartitionSkeletonToEventFlow y) :=
    congrArg defectFlowPartitionSkeletonFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DefectFlowPartitionSkeletonTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DefectFlowPartitionSkeletonTasteGate_single_carrier_alignment_round_trip y)))

private theorem DefectFlowPartitionSkeletonTasteGate_single_carrier_alignment_fields :
    ∀ x y : DefectFlowPartitionSkeletonUp,
      defectFlowPartitionSkeletonFields x = defectFlowPartitionSkeletonFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B₁ I₁ L₁ T₁ A₁ M₁ X₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk B₂ I₂ L₂ T₂ A₂ M₂ X₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance defectFlowPartitionSkeletonBHistCarrier :
    BHistCarrier DefectFlowPartitionSkeletonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := defectFlowPartitionSkeletonToEventFlow
  fromEventFlow := defectFlowPartitionSkeletonFromEventFlow

instance defectFlowPartitionSkeletonChapterTasteGate :
    ChapterTasteGate DefectFlowPartitionSkeletonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      defectFlowPartitionSkeletonFromEventFlow
          (defectFlowPartitionSkeletonToEventFlow x) =
        some x
    exact DefectFlowPartitionSkeletonTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (defectFlowPartitionSkeletonToEventFlow_injective heq)

instance defectFlowPartitionSkeletonFieldFaithful :
    FieldFaithful DefectFlowPartitionSkeletonUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := defectFlowPartitionSkeletonFields
  field_faithful := DefectFlowPartitionSkeletonTasteGate_single_carrier_alignment_fields

instance defectFlowPartitionSkeletonNontrivial :
    Nontrivial DefectFlowPartitionSkeletonUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DefectFlowPartitionSkeletonUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DefectFlowPartitionSkeletonUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def DefectFlowPartitionSkeletonTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate DefectFlowPartitionSkeletonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  defectFlowPartitionSkeletonChapterTasteGate

theorem DefectFlowPartitionSkeletonTasteGate_single_carrier_alignment :
    (∀ x : DefectFlowPartitionSkeletonUp,
      defectFlowPartitionSkeletonFromEventFlow (defectFlowPartitionSkeletonToEventFlow x) =
        some x) ∧
      (∀ x y : DefectFlowPartitionSkeletonUp,
        defectFlowPartitionSkeletonToEventFlow x =
            defectFlowPartitionSkeletonToEventFlow y →
          x = y) ∧
        Nonempty (BHistCarrier DefectFlowPartitionSkeletonUp) ∧
          Nonempty (ChapterTasteGate DefectFlowPartitionSkeletonUp) ∧
            Nonempty (FieldFaithful DefectFlowPartitionSkeletonUp) ∧
              Nonempty (Nontrivial DefectFlowPartitionSkeletonUp) ∧
                defectFlowPartitionSkeletonFields
                    (DefectFlowPartitionSkeletonUp.mk BHist.Empty BHist.Empty BHist.Empty
                      BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                      BHist.Empty BHist.Empty) =
                  [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
                    BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
                    BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact DefectFlowPartitionSkeletonTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact defectFlowPartitionSkeletonToEventFlow_injective heq
  constructor
  · exact ⟨defectFlowPartitionSkeletonBHistCarrier⟩
  constructor
  · exact ⟨defectFlowPartitionSkeletonChapterTasteGate⟩
  constructor
  · exact ⟨defectFlowPartitionSkeletonFieldFaithful⟩
  constructor
  · exact ⟨defectFlowPartitionSkeletonNontrivial⟩
  · rfl

end BEDC.Derived.DefectFlowPartitionSkeletonUp
