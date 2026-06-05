import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MeasurableSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MeasurableSpaceUp : Type where
  | mk (X A B E H C P N : BHist) : MeasurableSpaceUp
  deriving DecidableEq

def measurableSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: measurableSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: measurableSpaceEncodeBHist h

def measurableSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (measurableSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (measurableSpaceDecodeBHist tail)

private theorem MeasurableSpaceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, measurableSpaceDecodeBHist (measurableSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def measurableSpaceFields : MeasurableSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MeasurableSpaceUp.mk X A B E H C P N => [X, A, B, E, H, C, P, N]

def measurableSpaceToEventFlow : MeasurableSpaceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (measurableSpaceFields x).map measurableSpaceEncodeBHist

private def measurableSpaceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => measurableSpaceEventAtDefault index rest

def measurableSpaceFromEventFlow (ef : EventFlow) : Option MeasurableSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MeasurableSpaceUp.mk
      (measurableSpaceDecodeBHist (measurableSpaceEventAtDefault 0 ef))
      (measurableSpaceDecodeBHist (measurableSpaceEventAtDefault 1 ef))
      (measurableSpaceDecodeBHist (measurableSpaceEventAtDefault 2 ef))
      (measurableSpaceDecodeBHist (measurableSpaceEventAtDefault 3 ef))
      (measurableSpaceDecodeBHist (measurableSpaceEventAtDefault 4 ef))
      (measurableSpaceDecodeBHist (measurableSpaceEventAtDefault 5 ef))
      (measurableSpaceDecodeBHist (measurableSpaceEventAtDefault 6 ef))
      (measurableSpaceDecodeBHist (measurableSpaceEventAtDefault 7 ef)))

private theorem MeasurableSpaceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : MeasurableSpaceUp,
      measurableSpaceFromEventFlow (measurableSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X A B E H C P N =>
      change
        some
          (MeasurableSpaceUp.mk
            (measurableSpaceDecodeBHist (measurableSpaceEncodeBHist X))
            (measurableSpaceDecodeBHist (measurableSpaceEncodeBHist A))
            (measurableSpaceDecodeBHist (measurableSpaceEncodeBHist B))
            (measurableSpaceDecodeBHist (measurableSpaceEncodeBHist E))
            (measurableSpaceDecodeBHist (measurableSpaceEncodeBHist H))
            (measurableSpaceDecodeBHist (measurableSpaceEncodeBHist C))
            (measurableSpaceDecodeBHist (measurableSpaceEncodeBHist P))
            (measurableSpaceDecodeBHist (measurableSpaceEncodeBHist N))) =
          some (MeasurableSpaceUp.mk X A B E H C P N)
      rw [MeasurableSpaceTasteGate_single_carrier_alignment_decode X,
        MeasurableSpaceTasteGate_single_carrier_alignment_decode A,
        MeasurableSpaceTasteGate_single_carrier_alignment_decode B,
        MeasurableSpaceTasteGate_single_carrier_alignment_decode E,
        MeasurableSpaceTasteGate_single_carrier_alignment_decode H,
        MeasurableSpaceTasteGate_single_carrier_alignment_decode C,
        MeasurableSpaceTasteGate_single_carrier_alignment_decode P,
        MeasurableSpaceTasteGate_single_carrier_alignment_decode N]

private theorem MeasurableSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MeasurableSpaceUp} :
    measurableSpaceToEventFlow x = measurableSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      measurableSpaceFromEventFlow (measurableSpaceToEventFlow x) =
        measurableSpaceFromEventFlow (measurableSpaceToEventFlow y) :=
    congrArg measurableSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (MeasurableSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (MeasurableSpaceTasteGate_single_carrier_alignment_round_trip y)))

private theorem MeasurableSpaceTasteGate_single_carrier_alignment_fields :
    ∀ x y : MeasurableSpaceUp, measurableSpaceFields x = measurableSpaceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X₁ A₁ B₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk X₂ A₂ B₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance measurableSpaceBHistCarrier : BHistCarrier MeasurableSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := measurableSpaceToEventFlow
  fromEventFlow := measurableSpaceFromEventFlow

instance measurableSpaceChapterTasteGate : ChapterTasteGate MeasurableSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change measurableSpaceFromEventFlow (measurableSpaceToEventFlow x) = some x
    exact MeasurableSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MeasurableSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance measurableSpaceFieldFaithful : FieldFaithful MeasurableSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := measurableSpaceFields
  field_faithful := MeasurableSpaceTasteGate_single_carrier_alignment_fields

instance measurableSpaceNontrivial : BEDC.Meta.TasteGate.Nontrivial MeasurableSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MeasurableSpaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      MeasurableSpaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MeasurableSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  measurableSpaceChapterTasteGate

theorem MeasurableSpaceTasteGate_single_carrier_alignment :
    (forall h : BHist, measurableSpaceDecodeBHist (measurableSpaceEncodeBHist h) = h) ∧
      (forall x : MeasurableSpaceUp,
        measurableSpaceFromEventFlow (measurableSpaceToEventFlow x) = some x) ∧
        (forall x y : MeasurableSpaceUp,
          measurableSpaceToEventFlow x = measurableSpaceToEventFlow y -> x = y) ∧
          measurableSpaceFields
              (MeasurableSpaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
            [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
              BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨MeasurableSpaceTasteGate_single_carrier_alignment_decode,
      MeasurableSpaceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => MeasurableSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.MeasurableSpaceUp
