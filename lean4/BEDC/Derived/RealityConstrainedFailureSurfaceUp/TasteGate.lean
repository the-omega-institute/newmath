import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealityConstrainedFailureSurfaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealityConstrainedFailureSurfaceUp : Type where
  | mk : (O D K U L H C P N : BHist) → RealityConstrainedFailureSurfaceUp
  deriving DecidableEq

def realityConstrainedFailureSurfaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realityConstrainedFailureSurfaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realityConstrainedFailureSurfaceEncodeBHist h

def realityConstrainedFailureSurfaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realityConstrainedFailureSurfaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realityConstrainedFailureSurfaceDecodeBHist tail)

private theorem RealityConstrainedFailureSurfaceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      realityConstrainedFailureSurfaceDecodeBHist
        (realityConstrainedFailureSurfaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realityConstrainedFailureSurfaceFields :
    RealityConstrainedFailureSurfaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealityConstrainedFailureSurfaceUp.mk O D K U L H C P N => [O, D, K, U, L, H, C, P, N]

def realityConstrainedFailureSurfaceToEventFlow :
    RealityConstrainedFailureSurfaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealityConstrainedFailureSurfaceUp.mk O D K U L H C P N =>
      [[BMark.b0],
        realityConstrainedFailureSurfaceEncodeBHist O,
        [BMark.b1, BMark.b0],
        realityConstrainedFailureSurfaceEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedFailureSurfaceEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedFailureSurfaceEncodeBHist U,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedFailureSurfaceEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedFailureSurfaceEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedFailureSurfaceEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        realityConstrainedFailureSurfaceEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        realityConstrainedFailureSurfaceEncodeBHist N]

private def RealityConstrainedFailureSurfaceTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      RealityConstrainedFailureSurfaceTasteGate_single_carrier_alignment_eventAtDefault index
        rest

def realityConstrainedFailureSurfaceFromEventFlow
    (ef : EventFlow) : Option RealityConstrainedFailureSurfaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealityConstrainedFailureSurfaceUp.mk
      (realityConstrainedFailureSurfaceDecodeBHist
        (RealityConstrainedFailureSurfaceTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
      (realityConstrainedFailureSurfaceDecodeBHist
        (RealityConstrainedFailureSurfaceTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
      (realityConstrainedFailureSurfaceDecodeBHist
        (RealityConstrainedFailureSurfaceTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
      (realityConstrainedFailureSurfaceDecodeBHist
        (RealityConstrainedFailureSurfaceTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
      (realityConstrainedFailureSurfaceDecodeBHist
        (RealityConstrainedFailureSurfaceTasteGate_single_carrier_alignment_eventAtDefault 9 ef))
      (realityConstrainedFailureSurfaceDecodeBHist
        (RealityConstrainedFailureSurfaceTasteGate_single_carrier_alignment_eventAtDefault 11 ef))
      (realityConstrainedFailureSurfaceDecodeBHist
        (RealityConstrainedFailureSurfaceTasteGate_single_carrier_alignment_eventAtDefault 13 ef))
      (realityConstrainedFailureSurfaceDecodeBHist
        (RealityConstrainedFailureSurfaceTasteGate_single_carrier_alignment_eventAtDefault 15 ef))
      (realityConstrainedFailureSurfaceDecodeBHist
        (RealityConstrainedFailureSurfaceTasteGate_single_carrier_alignment_eventAtDefault 17 ef)))

private theorem RealityConstrainedFailureSurfaceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RealityConstrainedFailureSurfaceUp,
      realityConstrainedFailureSurfaceFromEventFlow
        (realityConstrainedFailureSurfaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk O D K U L H C P N =>
      change
        some
          (RealityConstrainedFailureSurfaceUp.mk
            (realityConstrainedFailureSurfaceDecodeBHist
              (realityConstrainedFailureSurfaceEncodeBHist O))
            (realityConstrainedFailureSurfaceDecodeBHist
              (realityConstrainedFailureSurfaceEncodeBHist D))
            (realityConstrainedFailureSurfaceDecodeBHist
              (realityConstrainedFailureSurfaceEncodeBHist K))
            (realityConstrainedFailureSurfaceDecodeBHist
              (realityConstrainedFailureSurfaceEncodeBHist U))
            (realityConstrainedFailureSurfaceDecodeBHist
              (realityConstrainedFailureSurfaceEncodeBHist L))
            (realityConstrainedFailureSurfaceDecodeBHist
              (realityConstrainedFailureSurfaceEncodeBHist H))
            (realityConstrainedFailureSurfaceDecodeBHist
              (realityConstrainedFailureSurfaceEncodeBHist C))
            (realityConstrainedFailureSurfaceDecodeBHist
              (realityConstrainedFailureSurfaceEncodeBHist P))
            (realityConstrainedFailureSurfaceDecodeBHist
              (realityConstrainedFailureSurfaceEncodeBHist N))) =
          some (RealityConstrainedFailureSurfaceUp.mk O D K U L H C P N)
      rw [RealityConstrainedFailureSurfaceTasteGate_single_carrier_alignment_decode O,
        RealityConstrainedFailureSurfaceTasteGate_single_carrier_alignment_decode D,
        RealityConstrainedFailureSurfaceTasteGate_single_carrier_alignment_decode K,
        RealityConstrainedFailureSurfaceTasteGate_single_carrier_alignment_decode U,
        RealityConstrainedFailureSurfaceTasteGate_single_carrier_alignment_decode L,
        RealityConstrainedFailureSurfaceTasteGate_single_carrier_alignment_decode H,
        RealityConstrainedFailureSurfaceTasteGate_single_carrier_alignment_decode C,
        RealityConstrainedFailureSurfaceTasteGate_single_carrier_alignment_decode P,
        RealityConstrainedFailureSurfaceTasteGate_single_carrier_alignment_decode N]

private theorem RealityConstrainedFailureSurfaceToEventFlow_injective
    {x y : RealityConstrainedFailureSurfaceUp} :
    realityConstrainedFailureSurfaceToEventFlow x =
      realityConstrainedFailureSurfaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realityConstrainedFailureSurfaceFromEventFlow
          (realityConstrainedFailureSurfaceToEventFlow x) =
        realityConstrainedFailureSurfaceFromEventFlow
          (realityConstrainedFailureSurfaceToEventFlow y) :=
    congrArg realityConstrainedFailureSurfaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RealityConstrainedFailureSurfaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RealityConstrainedFailureSurfaceTasteGate_single_carrier_alignment_round_trip y)))

private theorem RealityConstrainedFailureSurfaceTasteGate_single_carrier_alignment_fields :
    ∀ x y : RealityConstrainedFailureSurfaceUp,
      realityConstrainedFailureSurfaceFields x = realityConstrainedFailureSurfaceFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk O₁ D₁ K₁ U₁ L₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk O₂ D₂ K₂ U₂ L₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance realityConstrainedFailureSurfaceBHistCarrier :
    BHistCarrier RealityConstrainedFailureSurfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realityConstrainedFailureSurfaceToEventFlow
  fromEventFlow := realityConstrainedFailureSurfaceFromEventFlow

instance realityConstrainedFailureSurfaceChapterTasteGate :
    ChapterTasteGate RealityConstrainedFailureSurfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realityConstrainedFailureSurfaceFromEventFlow
        (realityConstrainedFailureSurfaceToEventFlow x) = some x
    exact RealityConstrainedFailureSurfaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealityConstrainedFailureSurfaceToEventFlow_injective heq)

instance realityConstrainedFailureSurfaceFieldFaithful :
    FieldFaithful RealityConstrainedFailureSurfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realityConstrainedFailureSurfaceFields
  field_faithful := RealityConstrainedFailureSurfaceTasteGate_single_carrier_alignment_fields

instance realityConstrainedFailureSurfaceNontrivial :
    Nontrivial RealityConstrainedFailureSurfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealityConstrainedFailureSurfaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealityConstrainedFailureSurfaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealityConstrainedFailureSurfaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realityConstrainedFailureSurfaceChapterTasteGate

theorem RealityConstrainedFailureSurfaceTasteGate_single_carrier_alignment :
    Nonempty (Nontrivial RealityConstrainedFailureSurfaceUp) ∧
      Nonempty (FieldFaithful RealityConstrainedFailureSurfaceUp) ∧
        Nonempty (ChapterTasteGate RealityConstrainedFailureSurfaceUp) ∧
          BHistCarrier.toEventFlow
              (RealityConstrainedFailureSurfaceUp.mk BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) ≠
            BHistCarrier.toEventFlow
              (RealityConstrainedFailureSurfaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact ⟨realityConstrainedFailureSurfaceNontrivial⟩
  · constructor
    · exact ⟨realityConstrainedFailureSurfaceFieldFaithful⟩
    · constructor
      · exact ⟨realityConstrainedFailureSurfaceChapterTasteGate⟩
      · intro heq
        have hxy :=
          RealityConstrainedFailureSurfaceToEventFlow_injective
            (x := RealityConstrainedFailureSurfaceUp.mk BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty)
            (y := RealityConstrainedFailureSurfaceUp.mk (BHist.e0 BHist.Empty)
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty)
            heq
        cases hxy

end BEDC.Derived.RealityConstrainedFailureSurfaceUp
