import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyReflectiveEmbeddingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyReflectiveEmbeddingUp : Type where
  | mk (C S Q D E J H T P N : BHist) : CauchyReflectiveEmbeddingUp
  deriving DecidableEq

def cauchyReflectiveEmbeddingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyReflectiveEmbeddingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyReflectiveEmbeddingEncodeBHist h

def cauchyReflectiveEmbeddingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyReflectiveEmbeddingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyReflectiveEmbeddingDecodeBHist tail)

private theorem CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyReflectiveEmbeddingDecodeBHist (cauchyReflectiveEmbeddingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyReflectiveEmbeddingFields : CauchyReflectiveEmbeddingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyReflectiveEmbeddingUp.mk C S Q D E J H T P N => [C, S, Q, D, E, J, H, T, P, N]

def cauchyReflectiveEmbeddingToEventFlow : CauchyReflectiveEmbeddingUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyReflectiveEmbeddingFields x).map cauchyReflectiveEmbeddingEncodeBHist

private def CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_eventAt index rest

def cauchyReflectiveEmbeddingFromEventFlow (ef : EventFlow) :
    Option CauchyReflectiveEmbeddingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyReflectiveEmbeddingUp.mk
      (cauchyReflectiveEmbeddingDecodeBHist
        (CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_eventAt 0 ef))
      (cauchyReflectiveEmbeddingDecodeBHist
        (CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_eventAt 1 ef))
      (cauchyReflectiveEmbeddingDecodeBHist
        (CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_eventAt 2 ef))
      (cauchyReflectiveEmbeddingDecodeBHist
        (CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_eventAt 3 ef))
      (cauchyReflectiveEmbeddingDecodeBHist
        (CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_eventAt 4 ef))
      (cauchyReflectiveEmbeddingDecodeBHist
        (CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_eventAt 5 ef))
      (cauchyReflectiveEmbeddingDecodeBHist
        (CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_eventAt 6 ef))
      (cauchyReflectiveEmbeddingDecodeBHist
        (CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_eventAt 7 ef))
      (cauchyReflectiveEmbeddingDecodeBHist
        (CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_eventAt 8 ef))
      (cauchyReflectiveEmbeddingDecodeBHist
        (CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_eventAt 9 ef)))

private theorem CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyReflectiveEmbeddingUp,
      cauchyReflectiveEmbeddingFromEventFlow (cauchyReflectiveEmbeddingToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk C S Q D E J H T P N =>
      change
        some
          (CauchyReflectiveEmbeddingUp.mk
            (cauchyReflectiveEmbeddingDecodeBHist (cauchyReflectiveEmbeddingEncodeBHist C))
            (cauchyReflectiveEmbeddingDecodeBHist (cauchyReflectiveEmbeddingEncodeBHist S))
            (cauchyReflectiveEmbeddingDecodeBHist (cauchyReflectiveEmbeddingEncodeBHist Q))
            (cauchyReflectiveEmbeddingDecodeBHist (cauchyReflectiveEmbeddingEncodeBHist D))
            (cauchyReflectiveEmbeddingDecodeBHist (cauchyReflectiveEmbeddingEncodeBHist E))
            (cauchyReflectiveEmbeddingDecodeBHist (cauchyReflectiveEmbeddingEncodeBHist J))
            (cauchyReflectiveEmbeddingDecodeBHist (cauchyReflectiveEmbeddingEncodeBHist H))
            (cauchyReflectiveEmbeddingDecodeBHist (cauchyReflectiveEmbeddingEncodeBHist T))
            (cauchyReflectiveEmbeddingDecodeBHist (cauchyReflectiveEmbeddingEncodeBHist P))
            (cauchyReflectiveEmbeddingDecodeBHist (cauchyReflectiveEmbeddingEncodeBHist N))) =
          some (CauchyReflectiveEmbeddingUp.mk C S Q D E J H T P N)
      rw [CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_decode_encode C,
        CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_decode_encode S,
        CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_decode_encode Q,
        CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_decode_encode D,
        CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_decode_encode E,
        CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_decode_encode J,
        CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_decode_encode H,
        CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_decode_encode T,
        CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_decode_encode P,
        CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyReflectiveEmbeddingUp} :
    cauchyReflectiveEmbeddingToEventFlow x = cauchyReflectiveEmbeddingToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyReflectiveEmbeddingFromEventFlow (cauchyReflectiveEmbeddingToEventFlow x) =
        cauchyReflectiveEmbeddingFromEventFlow (cauchyReflectiveEmbeddingToEventFlow y) :=
    congrArg cauchyReflectiveEmbeddingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : CauchyReflectiveEmbeddingUp,
      cauchyReflectiveEmbeddingFields x = cauchyReflectiveEmbeddingFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk C₁ S₁ Q₁ D₁ E₁ J₁ H₁ T₁ P₁ N₁ =>
      cases y with
      | mk C₂ S₂ Q₂ D₂ E₂ J₂ H₂ T₂ P₂ N₂ =>
          cases hfields
          rfl

instance cauchyReflectiveEmbeddingBHistCarrier :
    BHistCarrier CauchyReflectiveEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyReflectiveEmbeddingToEventFlow
  fromEventFlow := cauchyReflectiveEmbeddingFromEventFlow

instance cauchyReflectiveEmbeddingChapterTasteGate :
    ChapterTasteGate CauchyReflectiveEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyReflectiveEmbeddingFromEventFlow (cauchyReflectiveEmbeddingToEventFlow x) =
      some x
    exact CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cauchyReflectiveEmbeddingFieldFaithful :
    FieldFaithful CauchyReflectiveEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyReflectiveEmbeddingFields
  field_faithful :=
    CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_fields_faithful

instance cauchyReflectiveEmbeddingNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CauchyReflectiveEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyReflectiveEmbeddingUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyReflectiveEmbeddingUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CauchyReflectiveEmbeddingUp) ∧
      Nonempty (FieldFaithful CauchyReflectiveEmbeddingUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial CauchyReflectiveEmbeddingUp) ∧
      (∀ h : BHist,
        cauchyReflectiveEmbeddingDecodeBHist
            (cauchyReflectiveEmbeddingEncodeBHist h) = h) ∧
      (∀ x : CauchyReflectiveEmbeddingUp,
        cauchyReflectiveEmbeddingFromEventFlow
            (cauchyReflectiveEmbeddingToEventFlow x) = some x) ∧
      (∀ x y : CauchyReflectiveEmbeddingUp,
        cauchyReflectiveEmbeddingToEventFlow x =
            cauchyReflectiveEmbeddingToEventFlow y →
          x = y) ∧
      cauchyReflectiveEmbeddingEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact Nonempty.intro cauchyReflectiveEmbeddingChapterTasteGate
  · constructor
    · exact Nonempty.intro cauchyReflectiveEmbeddingFieldFaithful
    · constructor
      · exact Nonempty.intro cauchyReflectiveEmbeddingNontrivial
      · constructor
        · exact CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_decode_encode
        · constructor
          · exact CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_round_trip
          · constructor
            · intro x y heq
              exact
                CauchyReflectiveEmbeddingTasteGate_single_carrier_alignment_toEventFlow_injective
                  heq
            · rfl

end BEDC.Derived.CauchyReflectiveEmbeddingUp
