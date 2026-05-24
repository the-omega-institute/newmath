import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionEmbeddingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionEmbeddingUp : Type where
  | mk (X U C S R D E H Q P N : BHist) : CauchyCompletionEmbeddingUp
  deriving DecidableEq

def cauchyCompletionEmbeddingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionEmbeddingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionEmbeddingEncodeBHist h

def cauchyCompletionEmbeddingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionEmbeddingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionEmbeddingDecodeBHist tail)

private theorem CauchyCompletionEmbeddingTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyCompletionEmbeddingDecodeBHist
        (cauchyCompletionEmbeddingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyCompletionEmbeddingFields : CauchyCompletionEmbeddingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionEmbeddingUp.mk X U C S R D E H Q P N =>
      [X, U, C, S, R, D, E, H, Q, P, N]

def cauchyCompletionEmbeddingToEventFlow : CauchyCompletionEmbeddingUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyCompletionEmbeddingFields x).map cauchyCompletionEmbeddingEncodeBHist

private def cauchyCompletionEmbeddingEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyCompletionEmbeddingEventAt index rest

def cauchyCompletionEmbeddingFromEventFlow (ef : EventFlow) :
    Option CauchyCompletionEmbeddingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyCompletionEmbeddingUp.mk
      (cauchyCompletionEmbeddingDecodeBHist (cauchyCompletionEmbeddingEventAt 0 ef))
      (cauchyCompletionEmbeddingDecodeBHist (cauchyCompletionEmbeddingEventAt 1 ef))
      (cauchyCompletionEmbeddingDecodeBHist (cauchyCompletionEmbeddingEventAt 2 ef))
      (cauchyCompletionEmbeddingDecodeBHist (cauchyCompletionEmbeddingEventAt 3 ef))
      (cauchyCompletionEmbeddingDecodeBHist (cauchyCompletionEmbeddingEventAt 4 ef))
      (cauchyCompletionEmbeddingDecodeBHist (cauchyCompletionEmbeddingEventAt 5 ef))
      (cauchyCompletionEmbeddingDecodeBHist (cauchyCompletionEmbeddingEventAt 6 ef))
      (cauchyCompletionEmbeddingDecodeBHist (cauchyCompletionEmbeddingEventAt 7 ef))
      (cauchyCompletionEmbeddingDecodeBHist (cauchyCompletionEmbeddingEventAt 8 ef))
      (cauchyCompletionEmbeddingDecodeBHist (cauchyCompletionEmbeddingEventAt 9 ef))
      (cauchyCompletionEmbeddingDecodeBHist (cauchyCompletionEmbeddingEventAt 10 ef)))

private theorem CauchyCompletionEmbeddingTasteGate_single_carrier_alignment_round_trip
    (x : CauchyCompletionEmbeddingUp) :
    cauchyCompletionEmbeddingFromEventFlow (cauchyCompletionEmbeddingToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X U C S R D E H Q P N =>
      change
        some
          (CauchyCompletionEmbeddingUp.mk
            (cauchyCompletionEmbeddingDecodeBHist (cauchyCompletionEmbeddingEncodeBHist X))
            (cauchyCompletionEmbeddingDecodeBHist (cauchyCompletionEmbeddingEncodeBHist U))
            (cauchyCompletionEmbeddingDecodeBHist (cauchyCompletionEmbeddingEncodeBHist C))
            (cauchyCompletionEmbeddingDecodeBHist (cauchyCompletionEmbeddingEncodeBHist S))
            (cauchyCompletionEmbeddingDecodeBHist (cauchyCompletionEmbeddingEncodeBHist R))
            (cauchyCompletionEmbeddingDecodeBHist (cauchyCompletionEmbeddingEncodeBHist D))
            (cauchyCompletionEmbeddingDecodeBHist (cauchyCompletionEmbeddingEncodeBHist E))
            (cauchyCompletionEmbeddingDecodeBHist (cauchyCompletionEmbeddingEncodeBHist H))
            (cauchyCompletionEmbeddingDecodeBHist (cauchyCompletionEmbeddingEncodeBHist Q))
            (cauchyCompletionEmbeddingDecodeBHist (cauchyCompletionEmbeddingEncodeBHist P))
            (cauchyCompletionEmbeddingDecodeBHist (cauchyCompletionEmbeddingEncodeBHist N))) =
          some (CauchyCompletionEmbeddingUp.mk X U C S R D E H Q P N)
      rw [CauchyCompletionEmbeddingTasteGate_single_carrier_alignment_decode_encode X,
        CauchyCompletionEmbeddingTasteGate_single_carrier_alignment_decode_encode U,
        CauchyCompletionEmbeddingTasteGate_single_carrier_alignment_decode_encode C,
        CauchyCompletionEmbeddingTasteGate_single_carrier_alignment_decode_encode S,
        CauchyCompletionEmbeddingTasteGate_single_carrier_alignment_decode_encode R,
        CauchyCompletionEmbeddingTasteGate_single_carrier_alignment_decode_encode D,
        CauchyCompletionEmbeddingTasteGate_single_carrier_alignment_decode_encode E,
        CauchyCompletionEmbeddingTasteGate_single_carrier_alignment_decode_encode H,
        CauchyCompletionEmbeddingTasteGate_single_carrier_alignment_decode_encode Q,
        CauchyCompletionEmbeddingTasteGate_single_carrier_alignment_decode_encode P,
        CauchyCompletionEmbeddingTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyCompletionEmbeddingTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyCompletionEmbeddingUp} :
    cauchyCompletionEmbeddingToEventFlow x = cauchyCompletionEmbeddingToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletionEmbeddingFromEventFlow (cauchyCompletionEmbeddingToEventFlow x) =
        cauchyCompletionEmbeddingFromEventFlow (cauchyCompletionEmbeddingToEventFlow y) :=
    congrArg cauchyCompletionEmbeddingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyCompletionEmbeddingTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyCompletionEmbeddingTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyCompletionEmbeddingTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : CauchyCompletionEmbeddingUp,
      cauchyCompletionEmbeddingFields x = cauchyCompletionEmbeddingFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X₁ U₁ C₁ S₁ R₁ D₁ E₁ H₁ Q₁ P₁ N₁ =>
      cases y with
      | mk X₂ U₂ C₂ S₂ R₂ D₂ E₂ H₂ Q₂ P₂ N₂ =>
          injection hfields with hX tail0
          injection tail0 with hU tail1
          injection tail1 with hC tail2
          injection tail2 with hS tail3
          injection tail3 with hR tail4
          injection tail4 with hD tail5
          injection tail5 with hE tail6
          injection tail6 with hH tail7
          injection tail7 with hQ tail8
          injection tail8 with hP tail9
          injection tail9 with hN _
          subst hX
          subst hU
          subst hC
          subst hS
          subst hR
          subst hD
          subst hE
          subst hH
          subst hQ
          subst hP
          subst hN
          rfl

instance cauchyCompletionEmbeddingBHistCarrier : BHistCarrier CauchyCompletionEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionEmbeddingToEventFlow
  fromEventFlow := cauchyCompletionEmbeddingFromEventFlow

instance cauchyCompletionEmbeddingChapterTasteGate :
    ChapterTasteGate CauchyCompletionEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompletionEmbeddingFromEventFlow (cauchyCompletionEmbeddingToEventFlow x) =
        some x
    exact CauchyCompletionEmbeddingTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyCompletionEmbeddingTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cauchyCompletionEmbeddingFieldFaithful : FieldFaithful CauchyCompletionEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyCompletionEmbeddingFields
  field_faithful :=
    CauchyCompletionEmbeddingTasteGate_single_carrier_alignment_fields_faithful

instance cauchyCompletionEmbeddingNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CauchyCompletionEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyCompletionEmbeddingUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyCompletionEmbeddingUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem CauchyCompletionEmbeddingTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CauchyCompletionEmbeddingUp) ∧
      Nonempty (FieldFaithful CauchyCompletionEmbeddingUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial CauchyCompletionEmbeddingUp) ∧
          (∀ h : BHist,
            cauchyCompletionEmbeddingDecodeBHist
              (cauchyCompletionEmbeddingEncodeBHist h) = h) ∧
            (∀ x : CauchyCompletionEmbeddingUp,
              cauchyCompletionEmbeddingFromEventFlow
                (cauchyCompletionEmbeddingToEventFlow x) = some x) ∧
              (∀ x y : CauchyCompletionEmbeddingUp,
                cauchyCompletionEmbeddingToEventFlow x =
                    cauchyCompletionEmbeddingToEventFlow y ->
                  x = y) ∧
                cauchyCompletionEmbeddingEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨cauchyCompletionEmbeddingChapterTasteGate⟩,
      ⟨cauchyCompletionEmbeddingFieldFaithful⟩,
      ⟨cauchyCompletionEmbeddingNontrivial⟩,
      CauchyCompletionEmbeddingTasteGate_single_carrier_alignment_decode_encode,
      CauchyCompletionEmbeddingTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CauchyCompletionEmbeddingTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyCompletionEmbeddingUp
