import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.OuterMeasureUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive OuterMeasureUp : Type where
  | mk (X S Z M F B H C P N : BHist) : OuterMeasureUp
  deriving DecidableEq

def outerMeasureEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: outerMeasureEncodeBHist h
  | BHist.e1 h => BMark.b1 :: outerMeasureEncodeBHist h

def outerMeasureDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => outerMeasureDecodeBHist tail |> BHist.e0
  | BMark.b1 :: tail => outerMeasureDecodeBHist tail |> BHist.e1

private theorem OuterMeasureTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, outerMeasureDecodeBHist (outerMeasureEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def outerMeasureFields : OuterMeasureUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | OuterMeasureUp.mk X S Z M F B H C P N => [X, S, Z, M, F, B, H, C, P, N]

def outerMeasureToEventFlow : OuterMeasureUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | OuterMeasureUp.mk X S Z M F B H C P N =>
      [[BMark.b0],
        outerMeasureEncodeBHist X,
        [BMark.b1, BMark.b0],
        outerMeasureEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b0],
        outerMeasureEncodeBHist Z,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        outerMeasureEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        outerMeasureEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        outerMeasureEncodeBHist B,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        outerMeasureEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        outerMeasureEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        outerMeasureEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        outerMeasureEncodeBHist N]

private def outerMeasureEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => outerMeasureEventAtDefault index rest

def outerMeasureFromEventFlow (ef : EventFlow) : Option OuterMeasureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (OuterMeasureUp.mk
      (outerMeasureDecodeBHist (outerMeasureEventAtDefault 1 ef))
      (outerMeasureDecodeBHist (outerMeasureEventAtDefault 3 ef))
      (outerMeasureDecodeBHist (outerMeasureEventAtDefault 5 ef))
      (outerMeasureDecodeBHist (outerMeasureEventAtDefault 7 ef))
      (outerMeasureDecodeBHist (outerMeasureEventAtDefault 9 ef))
      (outerMeasureDecodeBHist (outerMeasureEventAtDefault 11 ef))
      (outerMeasureDecodeBHist (outerMeasureEventAtDefault 13 ef))
      (outerMeasureDecodeBHist (outerMeasureEventAtDefault 15 ef))
      (outerMeasureDecodeBHist (outerMeasureEventAtDefault 17 ef))
      (outerMeasureDecodeBHist (outerMeasureEventAtDefault 19 ef)))

private theorem OuterMeasureTasteGate_single_carrier_alignment_round_trip
    (x : OuterMeasureUp) :
    outerMeasureFromEventFlow (outerMeasureToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X S Z M F B H C P N =>
      change
        some
          (OuterMeasureUp.mk
            (outerMeasureDecodeBHist (outerMeasureEncodeBHist X))
            (outerMeasureDecodeBHist (outerMeasureEncodeBHist S))
            (outerMeasureDecodeBHist (outerMeasureEncodeBHist Z))
            (outerMeasureDecodeBHist (outerMeasureEncodeBHist M))
            (outerMeasureDecodeBHist (outerMeasureEncodeBHist F))
            (outerMeasureDecodeBHist (outerMeasureEncodeBHist B))
            (outerMeasureDecodeBHist (outerMeasureEncodeBHist H))
            (outerMeasureDecodeBHist (outerMeasureEncodeBHist C))
            (outerMeasureDecodeBHist (outerMeasureEncodeBHist P))
            (outerMeasureDecodeBHist (outerMeasureEncodeBHist N))) =
          some (OuterMeasureUp.mk X S Z M F B H C P N)
      rw [OuterMeasureTasteGate_single_carrier_alignment_decode_encode X,
        OuterMeasureTasteGate_single_carrier_alignment_decode_encode S,
        OuterMeasureTasteGate_single_carrier_alignment_decode_encode Z,
        OuterMeasureTasteGate_single_carrier_alignment_decode_encode M,
        OuterMeasureTasteGate_single_carrier_alignment_decode_encode F,
        OuterMeasureTasteGate_single_carrier_alignment_decode_encode B,
        OuterMeasureTasteGate_single_carrier_alignment_decode_encode H,
        OuterMeasureTasteGate_single_carrier_alignment_decode_encode C,
        OuterMeasureTasteGate_single_carrier_alignment_decode_encode P,
        OuterMeasureTasteGate_single_carrier_alignment_decode_encode N]

private theorem OuterMeasureTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : OuterMeasureUp} :
    outerMeasureToEventFlow x = outerMeasureToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      outerMeasureFromEventFlow (outerMeasureToEventFlow x) =
        outerMeasureFromEventFlow (outerMeasureToEventFlow y) :=
    congrArg outerMeasureFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (OuterMeasureTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (OuterMeasureTasteGate_single_carrier_alignment_round_trip y)))

private theorem OuterMeasureTasteGate_single_carrier_alignment_fields :
    ∀ x y : OuterMeasureUp, outerMeasureFields x = outerMeasureFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X₁ S₁ Z₁ M₁ F₁ B₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk X₂ S₂ Z₂ M₂ F₂ B₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance outerMeasureBHistCarrier : BHistCarrier OuterMeasureUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := outerMeasureToEventFlow
  fromEventFlow := outerMeasureFromEventFlow

instance outerMeasureChapterTasteGate : ChapterTasteGate OuterMeasureUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change outerMeasureFromEventFlow (outerMeasureToEventFlow x) = some x
    exact OuterMeasureTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (OuterMeasureTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance outerMeasureFieldFaithful : FieldFaithful OuterMeasureUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := outerMeasureFields
  field_faithful := OuterMeasureTasteGate_single_carrier_alignment_fields

instance outerMeasureNontrivial : Nontrivial OuterMeasureUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨OuterMeasureUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      OuterMeasureUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def OuterMeasureTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate OuterMeasureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  outerMeasureChapterTasteGate

theorem OuterMeasureTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate OuterMeasureUp) ∧
      Nonempty (FieldFaithful OuterMeasureUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial OuterMeasureUp) ∧
      (∀ h : BHist, outerMeasureDecodeBHist (outerMeasureEncodeBHist h) = h) ∧
      (∀ x : OuterMeasureUp, outerMeasureFromEventFlow (outerMeasureToEventFlow x) = some x) ∧
      outerMeasureEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact ⟨outerMeasureChapterTasteGate⟩
  · constructor
    · exact ⟨outerMeasureFieldFaithful⟩
    · constructor
      · exact ⟨outerMeasureNontrivial⟩
      · constructor
        · exact OuterMeasureTasteGate_single_carrier_alignment_decode_encode
        · constructor
          · exact OuterMeasureTasteGate_single_carrier_alignment_round_trip
          · rfl

end BEDC.Derived.OuterMeasureUp
