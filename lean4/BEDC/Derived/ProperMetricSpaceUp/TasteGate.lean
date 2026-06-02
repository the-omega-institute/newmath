import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ProperMetricSpaceUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ProperMetricSpaceUp : Type where
  | mk (X B R K O H C P N : BHist) : ProperMetricSpaceUp
  deriving DecidableEq

def properMetricSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: properMetricSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: properMetricSpaceEncodeBHist h

def properMetricSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (properMetricSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (properMetricSpaceDecodeBHist tail)

private theorem ProperMetricSpaceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, properMetricSpaceDecodeBHist (properMetricSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def properMetricSpaceFields : ProperMetricSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ProperMetricSpaceUp.mk X B R K O H C P N => [X, B, R, K, O, H, C, P, N]

def properMetricSpaceToEventFlow : ProperMetricSpaceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (properMetricSpaceFields x).map properMetricSpaceEncodeBHist

private def properMetricSpaceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => properMetricSpaceEventAt index rest

def properMetricSpaceFromEventFlow (ef : EventFlow) : Option ProperMetricSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ProperMetricSpaceUp.mk
      (properMetricSpaceDecodeBHist (properMetricSpaceEventAt 0 ef))
      (properMetricSpaceDecodeBHist (properMetricSpaceEventAt 1 ef))
      (properMetricSpaceDecodeBHist (properMetricSpaceEventAt 2 ef))
      (properMetricSpaceDecodeBHist (properMetricSpaceEventAt 3 ef))
      (properMetricSpaceDecodeBHist (properMetricSpaceEventAt 4 ef))
      (properMetricSpaceDecodeBHist (properMetricSpaceEventAt 5 ef))
      (properMetricSpaceDecodeBHist (properMetricSpaceEventAt 6 ef))
      (properMetricSpaceDecodeBHist (properMetricSpaceEventAt 7 ef))
      (properMetricSpaceDecodeBHist (properMetricSpaceEventAt 8 ef)))

private theorem ProperMetricSpaceTasteGate_single_carrier_alignment_round_trip
    (x : ProperMetricSpaceUp) :
    properMetricSpaceFromEventFlow (properMetricSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X B R K O H C P N =>
      change
        some
          (ProperMetricSpaceUp.mk
            (properMetricSpaceDecodeBHist (properMetricSpaceEncodeBHist X))
            (properMetricSpaceDecodeBHist (properMetricSpaceEncodeBHist B))
            (properMetricSpaceDecodeBHist (properMetricSpaceEncodeBHist R))
            (properMetricSpaceDecodeBHist (properMetricSpaceEncodeBHist K))
            (properMetricSpaceDecodeBHist (properMetricSpaceEncodeBHist O))
            (properMetricSpaceDecodeBHist (properMetricSpaceEncodeBHist H))
            (properMetricSpaceDecodeBHist (properMetricSpaceEncodeBHist C))
            (properMetricSpaceDecodeBHist (properMetricSpaceEncodeBHist P))
            (properMetricSpaceDecodeBHist (properMetricSpaceEncodeBHist N))) =
          some (ProperMetricSpaceUp.mk X B R K O H C P N)
      rw [ProperMetricSpaceTasteGate_single_carrier_alignment_decode X,
        ProperMetricSpaceTasteGate_single_carrier_alignment_decode B,
        ProperMetricSpaceTasteGate_single_carrier_alignment_decode R,
        ProperMetricSpaceTasteGate_single_carrier_alignment_decode K,
        ProperMetricSpaceTasteGate_single_carrier_alignment_decode O,
        ProperMetricSpaceTasteGate_single_carrier_alignment_decode H,
        ProperMetricSpaceTasteGate_single_carrier_alignment_decode C,
        ProperMetricSpaceTasteGate_single_carrier_alignment_decode P,
        ProperMetricSpaceTasteGate_single_carrier_alignment_decode N]

private theorem ProperMetricSpaceTasteGate_single_carrier_alignment_injective
    {x y : ProperMetricSpaceUp} :
    properMetricSpaceToEventFlow x = properMetricSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      properMetricSpaceFromEventFlow (properMetricSpaceToEventFlow x) =
        properMetricSpaceFromEventFlow (properMetricSpaceToEventFlow y) :=
    congrArg properMetricSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ProperMetricSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ProperMetricSpaceTasteGate_single_carrier_alignment_round_trip y)))

private theorem ProperMetricSpaceTasteGate_single_carrier_alignment_fields :
    ∀ x y : ProperMetricSpaceUp,
      properMetricSpaceFields x = properMetricSpaceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X₁ B₁ R₁ K₁ O₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk X₂ B₂ R₂ K₂ O₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance properMetricSpaceBHistCarrier : BHistCarrier ProperMetricSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := properMetricSpaceToEventFlow
  fromEventFlow := properMetricSpaceFromEventFlow

instance properMetricSpaceChapterTasteGate : ChapterTasteGate ProperMetricSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change properMetricSpaceFromEventFlow (properMetricSpaceToEventFlow x) = some x
    exact ProperMetricSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ProperMetricSpaceTasteGate_single_carrier_alignment_injective heq)

instance properMetricSpaceFieldFaithful : FieldFaithful ProperMetricSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := properMetricSpaceFields
  field_faithful := ProperMetricSpaceTasteGate_single_carrier_alignment_fields

instance properMetricSpaceNontrivial : Nontrivial ProperMetricSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ProperMetricSpaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ProperMetricSpaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def properMetricSpaceTasteGate : ChapterTasteGate ProperMetricSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  properMetricSpaceChapterTasteGate

theorem ProperMetricSpaceTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ProperMetricSpaceUp) ∧
      Nonempty (FieldFaithful ProperMetricSpaceUp) ∧
        Nonempty (Nontrivial ProperMetricSpaceUp) ∧
          (∀ h : BHist, properMetricSpaceDecodeBHist (properMetricSpaceEncodeBHist h) = h) ∧
            (∀ x : ProperMetricSpaceUp,
              properMetricSpaceFromEventFlow (properMetricSpaceToEventFlow x) = some x) ∧
              (∀ x y : ProperMetricSpaceUp,
                properMetricSpaceToEventFlow x = properMetricSpaceToEventFlow y -> x = y) ∧
                properMetricSpaceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨properMetricSpaceChapterTasteGate⟩,
      ⟨properMetricSpaceFieldFaithful⟩,
      ⟨properMetricSpaceNontrivial⟩,
      ProperMetricSpaceTasteGate_single_carrier_alignment_decode,
      ProperMetricSpaceTasteGate_single_carrier_alignment_round_trip,
      fun x y => ProperMetricSpaceTasteGate_single_carrier_alignment_injective,
      rfl⟩

end BEDC.Derived.ProperMetricSpaceUp.TasteGate
