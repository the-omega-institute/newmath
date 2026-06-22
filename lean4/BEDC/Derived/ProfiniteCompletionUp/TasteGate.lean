import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ProfiniteCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ProfiniteCompletionUp : Type where
  | mk (Q Pi W B K H C P N : BHist) : ProfiniteCompletionUp
  deriving DecidableEq

def profiniteCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: profiniteCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: profiniteCompletionEncodeBHist h

def profiniteCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (profiniteCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (profiniteCompletionDecodeBHist tail)

private theorem profiniteCompletionDecodeEncode :
    ∀ h : BHist, profiniteCompletionDecodeBHist
      (profiniteCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def profiniteCompletionFields : ProfiniteCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ProfiniteCompletionUp.mk Q Pi W B K H C P N => [Q, Pi, W, B, K, H, C, P, N]

def profiniteCompletionToEventFlow : ProfiniteCompletionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (profiniteCompletionFields x).map profiniteCompletionEncodeBHist

private def profiniteCompletionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => profiniteCompletionEventAtDefault index rest

def profiniteCompletionFromEventFlow
    (ef : EventFlow) : Option ProfiniteCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ProfiniteCompletionUp.mk
      (profiniteCompletionDecodeBHist (profiniteCompletionEventAtDefault 0 ef))
      (profiniteCompletionDecodeBHist (profiniteCompletionEventAtDefault 1 ef))
      (profiniteCompletionDecodeBHist (profiniteCompletionEventAtDefault 2 ef))
      (profiniteCompletionDecodeBHist (profiniteCompletionEventAtDefault 3 ef))
      (profiniteCompletionDecodeBHist (profiniteCompletionEventAtDefault 4 ef))
      (profiniteCompletionDecodeBHist (profiniteCompletionEventAtDefault 5 ef))
      (profiniteCompletionDecodeBHist (profiniteCompletionEventAtDefault 6 ef))
      (profiniteCompletionDecodeBHist (profiniteCompletionEventAtDefault 7 ef))
      (profiniteCompletionDecodeBHist (profiniteCompletionEventAtDefault 8 ef)))

private theorem profiniteCompletion_round_trip :
    ∀ x : ProfiniteCompletionUp,
      profiniteCompletionFromEventFlow (profiniteCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q Pi W B K H C P N =>
      change
        some
          (ProfiniteCompletionUp.mk
            (profiniteCompletionDecodeBHist (profiniteCompletionEncodeBHist Q))
            (profiniteCompletionDecodeBHist (profiniteCompletionEncodeBHist Pi))
            (profiniteCompletionDecodeBHist (profiniteCompletionEncodeBHist W))
            (profiniteCompletionDecodeBHist (profiniteCompletionEncodeBHist B))
            (profiniteCompletionDecodeBHist (profiniteCompletionEncodeBHist K))
            (profiniteCompletionDecodeBHist (profiniteCompletionEncodeBHist H))
            (profiniteCompletionDecodeBHist (profiniteCompletionEncodeBHist C))
            (profiniteCompletionDecodeBHist (profiniteCompletionEncodeBHist P))
            (profiniteCompletionDecodeBHist (profiniteCompletionEncodeBHist N))) =
          some (ProfiniteCompletionUp.mk Q Pi W B K H C P N)
      rw [profiniteCompletionDecodeEncode Q, profiniteCompletionDecodeEncode Pi,
        profiniteCompletionDecodeEncode W, profiniteCompletionDecodeEncode B,
        profiniteCompletionDecodeEncode K, profiniteCompletionDecodeEncode H,
        profiniteCompletionDecodeEncode C, profiniteCompletionDecodeEncode P,
        profiniteCompletionDecodeEncode N]

private theorem profiniteCompletionToEventFlow_injective {x y : ProfiniteCompletionUp} :
    profiniteCompletionToEventFlow x = profiniteCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      profiniteCompletionFromEventFlow (profiniteCompletionToEventFlow x) =
        profiniteCompletionFromEventFlow (profiniteCompletionToEventFlow y) :=
    congrArg profiniteCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (profiniteCompletion_round_trip x).symm
      (Eq.trans hread (profiniteCompletion_round_trip y)))

private theorem profiniteCompletionFieldFaithfulProof :
    ∀ x y : ProfiniteCompletionUp,
      profiniteCompletionFields x = profiniteCompletionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk Q₁ Pi₁ W₁ B₁ K₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk Q₂ Pi₂ W₂ B₂ K₂ H₂ C₂ P₂ N₂ =>
          change [Q₁, Pi₁, W₁, B₁, K₁, H₁, C₁, P₁, N₁] =
            [Q₂, Pi₂, W₂, B₂, K₂, H₂, C₂, P₂, N₂] at h
          cases h
          rfl

instance profiniteCompletionBHistCarrier :
    BHistCarrier ProfiniteCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := profiniteCompletionToEventFlow
  fromEventFlow := profiniteCompletionFromEventFlow

instance profiniteCompletionChapterTasteGate :
    ChapterTasteGate ProfiniteCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change profiniteCompletionFromEventFlow
      (profiniteCompletionToEventFlow x) = some x
    exact profiniteCompletion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (profiniteCompletionToEventFlow_injective heq)

instance profiniteCompletionFieldFaithful :
    FieldFaithful ProfiniteCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := profiniteCompletionFields
  field_faithful := profiniteCompletionFieldFaithfulProof

instance profiniteCompletionNontrivial :
    Nontrivial ProfiniteCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ProfiniteCompletionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ProfiniteCompletionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem ProfiniteCompletionTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ProfiniteCompletionUp) ∧
      Nonempty (FieldFaithful ProfiniteCompletionUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial ProfiniteCompletionUp) ∧
          (∀ h : BHist,
            profiniteCompletionDecodeBHist (profiniteCompletionEncodeBHist h) = h) ∧
            (∀ x : ProfiniteCompletionUp,
              profiniteCompletionFromEventFlow (profiniteCompletionToEventFlow x) =
                some x) ∧
              (∀ x y : ProfiniteCompletionUp,
                profiniteCompletionToEventFlow x =
                  profiniteCompletionToEventFlow y → x = y) ∧
                profiniteCompletionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨profiniteCompletionChapterTasteGate⟩,
      ⟨profiniteCompletionFieldFaithful⟩,
      ⟨profiniteCompletionNontrivial⟩,
      profiniteCompletionDecodeEncode,
      profiniteCompletion_round_trip,
      by
        intro x y heq
        exact profiniteCompletionToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.ProfiniteCompletionUp
