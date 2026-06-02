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
  | BMark.b0 :: tail => BHist.e0 (outerMeasureDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (outerMeasureDecodeBHist tail)

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
  | x => (outerMeasureFields x).map outerMeasureEncodeBHist

private def outerMeasureEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => outerMeasureEventAt index rest

def outerMeasureFromEventFlow : EventFlow → Option OuterMeasureUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (OuterMeasureUp.mk
          (outerMeasureDecodeBHist (outerMeasureEventAt 0 ef))
          (outerMeasureDecodeBHist (outerMeasureEventAt 1 ef))
          (outerMeasureDecodeBHist (outerMeasureEventAt 2 ef))
          (outerMeasureDecodeBHist (outerMeasureEventAt 3 ef))
          (outerMeasureDecodeBHist (outerMeasureEventAt 4 ef))
          (outerMeasureDecodeBHist (outerMeasureEventAt 5 ef))
          (outerMeasureDecodeBHist (outerMeasureEventAt 6 ef))
          (outerMeasureDecodeBHist (outerMeasureEventAt 7 ef))
          (outerMeasureDecodeBHist (outerMeasureEventAt 8 ef))
          (outerMeasureDecodeBHist (outerMeasureEventAt 9 ef)))

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
      (Eq.trans hread (OuterMeasureTasteGate_single_carrier_alignment_round_trip y)))

private theorem OuterMeasureTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : OuterMeasureUp, outerMeasureFields x = outerMeasureFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X₁ S₁ Z₁ M₁ F₁ B₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk X₂ S₂ Z₂ M₂ F₂ B₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hX tail0
          injection tail0 with hS tail1
          injection tail1 with hZ tail2
          injection tail2 with hM tail3
          injection tail3 with hF tail4
          injection tail4 with hB tail5
          injection tail5 with hH tail6
          injection tail6 with hC tail7
          injection tail7 with hP tail8
          injection tail8 with hN _
          subst hX
          subst hS
          subst hZ
          subst hM
          subst hF
          subst hB
          subst hH
          subst hC
          subst hP
          subst hN
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
  field_faithful := OuterMeasureTasteGate_single_carrier_alignment_fields_faithful

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
    (∀ h : BHist, outerMeasureDecodeBHist (outerMeasureEncodeBHist h) = h) ∧
      (∀ x : OuterMeasureUp,
        outerMeasureFromEventFlow (outerMeasureToEventFlow x) = some x) ∧
        (∀ x y : OuterMeasureUp,
          outerMeasureToEventFlow x = outerMeasureToEventFlow y → x = y) ∧
          outerMeasureEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨OuterMeasureTasteGate_single_carrier_alignment_decode_encode,
      OuterMeasureTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => OuterMeasureTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.OuterMeasureUp
