import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.YonedaCompletionUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive YonedaCompletionUp : Type where
  | mk (M B F D S Q R A H C P N : BHist) : YonedaCompletionUp
  deriving DecidableEq

def yonedaCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: yonedaCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: yonedaCompletionEncodeBHist h

def yonedaCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (yonedaCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (yonedaCompletionDecodeBHist tail)

private theorem YonedaCompletionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, yonedaCompletionDecodeBHist (yonedaCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def yonedaCompletionFields : YonedaCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | YonedaCompletionUp.mk M B F D S Q R A H C P N => [M, B, F, D, S, Q, R, A, H, C, P, N]

def yonedaCompletionToEventFlow : YonedaCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (yonedaCompletionFields x).map yonedaCompletionEncodeBHist

private def YonedaCompletionTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      YonedaCompletionTasteGate_single_carrier_alignment_eventAt index rest

def yonedaCompletionFromEventFlow (ef : EventFlow) : Option YonedaCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (YonedaCompletionUp.mk
      (yonedaCompletionDecodeBHist
        (YonedaCompletionTasteGate_single_carrier_alignment_eventAt 0 ef))
      (yonedaCompletionDecodeBHist
        (YonedaCompletionTasteGate_single_carrier_alignment_eventAt 1 ef))
      (yonedaCompletionDecodeBHist
        (YonedaCompletionTasteGate_single_carrier_alignment_eventAt 2 ef))
      (yonedaCompletionDecodeBHist
        (YonedaCompletionTasteGate_single_carrier_alignment_eventAt 3 ef))
      (yonedaCompletionDecodeBHist
        (YonedaCompletionTasteGate_single_carrier_alignment_eventAt 4 ef))
      (yonedaCompletionDecodeBHist
        (YonedaCompletionTasteGate_single_carrier_alignment_eventAt 5 ef))
      (yonedaCompletionDecodeBHist
        (YonedaCompletionTasteGate_single_carrier_alignment_eventAt 6 ef))
      (yonedaCompletionDecodeBHist
        (YonedaCompletionTasteGate_single_carrier_alignment_eventAt 7 ef))
      (yonedaCompletionDecodeBHist
        (YonedaCompletionTasteGate_single_carrier_alignment_eventAt 8 ef))
      (yonedaCompletionDecodeBHist
        (YonedaCompletionTasteGate_single_carrier_alignment_eventAt 9 ef))
      (yonedaCompletionDecodeBHist
        (YonedaCompletionTasteGate_single_carrier_alignment_eventAt 10 ef))
      (yonedaCompletionDecodeBHist
        (YonedaCompletionTasteGate_single_carrier_alignment_eventAt 11 ef)))

private theorem YonedaCompletionTasteGate_single_carrier_alignment_round_trip
    (x : YonedaCompletionUp) :
    yonedaCompletionFromEventFlow (yonedaCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk M B F D S Q R A H C P N =>
      change
        some
          (YonedaCompletionUp.mk
            (yonedaCompletionDecodeBHist (yonedaCompletionEncodeBHist M))
            (yonedaCompletionDecodeBHist (yonedaCompletionEncodeBHist B))
            (yonedaCompletionDecodeBHist (yonedaCompletionEncodeBHist F))
            (yonedaCompletionDecodeBHist (yonedaCompletionEncodeBHist D))
            (yonedaCompletionDecodeBHist (yonedaCompletionEncodeBHist S))
            (yonedaCompletionDecodeBHist (yonedaCompletionEncodeBHist Q))
            (yonedaCompletionDecodeBHist (yonedaCompletionEncodeBHist R))
            (yonedaCompletionDecodeBHist (yonedaCompletionEncodeBHist A))
            (yonedaCompletionDecodeBHist (yonedaCompletionEncodeBHist H))
            (yonedaCompletionDecodeBHist (yonedaCompletionEncodeBHist C))
            (yonedaCompletionDecodeBHist (yonedaCompletionEncodeBHist P))
            (yonedaCompletionDecodeBHist (yonedaCompletionEncodeBHist N))) =
          some (YonedaCompletionUp.mk M B F D S Q R A H C P N)
      rw [YonedaCompletionTasteGate_single_carrier_alignment_decode_encode M,
        YonedaCompletionTasteGate_single_carrier_alignment_decode_encode B,
        YonedaCompletionTasteGate_single_carrier_alignment_decode_encode F,
        YonedaCompletionTasteGate_single_carrier_alignment_decode_encode D,
        YonedaCompletionTasteGate_single_carrier_alignment_decode_encode S,
        YonedaCompletionTasteGate_single_carrier_alignment_decode_encode Q,
        YonedaCompletionTasteGate_single_carrier_alignment_decode_encode R,
        YonedaCompletionTasteGate_single_carrier_alignment_decode_encode A,
        YonedaCompletionTasteGate_single_carrier_alignment_decode_encode H,
        YonedaCompletionTasteGate_single_carrier_alignment_decode_encode C,
        YonedaCompletionTasteGate_single_carrier_alignment_decode_encode P,
        YonedaCompletionTasteGate_single_carrier_alignment_decode_encode N]

private theorem YonedaCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : YonedaCompletionUp} :
    yonedaCompletionToEventFlow x = yonedaCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      yonedaCompletionFromEventFlow (yonedaCompletionToEventFlow x) =
        yonedaCompletionFromEventFlow (yonedaCompletionToEventFlow y) :=
    congrArg yonedaCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (YonedaCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (YonedaCompletionTasteGate_single_carrier_alignment_round_trip y)))

private theorem YonedaCompletionTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : YonedaCompletionUp, yonedaCompletionFields x = yonedaCompletionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M₁ B₁ F₁ D₁ S₁ Q₁ R₁ A₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk M₂ B₂ F₂ D₂ S₂ Q₂ R₂ A₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance yonedaCompletionBHistCarrier : BHistCarrier YonedaCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := yonedaCompletionToEventFlow
  fromEventFlow := yonedaCompletionFromEventFlow

instance yonedaCompletionChapterTasteGate : ChapterTasteGate YonedaCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change yonedaCompletionFromEventFlow (yonedaCompletionToEventFlow x) = some x
    exact YonedaCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (YonedaCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance yonedaCompletionFieldFaithful : FieldFaithful YonedaCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := yonedaCompletionFields
  field_faithful := YonedaCompletionTasteGate_single_carrier_alignment_fields_faithful

instance yonedaCompletionNontrivial :
    BEDC.Meta.TasteGate.Nontrivial YonedaCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨YonedaCompletionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      YonedaCompletionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def yonedaCompletionTasteGate : ChapterTasteGate YonedaCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  yonedaCompletionChapterTasteGate

theorem YonedaCompletionTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier YonedaCompletionUp) ∧
      Nonempty (ChapterTasteGate YonedaCompletionUp) ∧
        Nonempty (FieldFaithful YonedaCompletionUp) ∧
          Nonempty (BEDC.Meta.TasteGate.Nontrivial YonedaCompletionUp) ∧
            (∀ h : BHist, yonedaCompletionDecodeBHist (yonedaCompletionEncodeBHist h) = h) ∧
              yonedaCompletionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨yonedaCompletionBHistCarrier⟩,
      ⟨yonedaCompletionChapterTasteGate⟩,
      ⟨yonedaCompletionFieldFaithful⟩,
      ⟨yonedaCompletionNontrivial⟩,
      YonedaCompletionTasteGate_single_carrier_alignment_decode_encode,
      rfl⟩

end BEDC.Derived.YonedaCompletionUp.TasteGate
