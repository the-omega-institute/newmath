import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HyperbolicHoroballShadowUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HyperbolicHoroballShadowUp : Type where
  | mk (B V M O S R E H C P N : BHist) : HyperbolicHoroballShadowUp
  deriving DecidableEq

def hyperbolicHoroballShadowEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hyperbolicHoroballShadowEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hyperbolicHoroballShadowEncodeBHist h

def hyperbolicHoroballShadowDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hyperbolicHoroballShadowDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hyperbolicHoroballShadowDecodeBHist tail)

private theorem hyperbolicHoroballShadow_decode_encode_bhist :
    ∀ h : BHist,
      hyperbolicHoroballShadowDecodeBHist
          (hyperbolicHoroballShadowEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def hyperbolicHoroballShadowEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      hyperbolicHoroballShadowEventAtDefault index rest

def hyperbolicHoroballShadowToEventFlow : HyperbolicHoroballShadowUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | HyperbolicHoroballShadowUp.mk B V M O S R E H C P N =>
      [hyperbolicHoroballShadowEncodeBHist B,
        hyperbolicHoroballShadowEncodeBHist V,
        hyperbolicHoroballShadowEncodeBHist M,
        hyperbolicHoroballShadowEncodeBHist O,
        hyperbolicHoroballShadowEncodeBHist S,
        hyperbolicHoroballShadowEncodeBHist R,
        hyperbolicHoroballShadowEncodeBHist E,
        hyperbolicHoroballShadowEncodeBHist H,
        hyperbolicHoroballShadowEncodeBHist C,
        hyperbolicHoroballShadowEncodeBHist P,
        hyperbolicHoroballShadowEncodeBHist N]

def hyperbolicHoroballShadowFromEventFlow
    (ef : EventFlow) : Option HyperbolicHoroballShadowUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HyperbolicHoroballShadowUp.mk
      (hyperbolicHoroballShadowDecodeBHist
        (hyperbolicHoroballShadowEventAtDefault 0 ef))
      (hyperbolicHoroballShadowDecodeBHist
        (hyperbolicHoroballShadowEventAtDefault 1 ef))
      (hyperbolicHoroballShadowDecodeBHist
        (hyperbolicHoroballShadowEventAtDefault 2 ef))
      (hyperbolicHoroballShadowDecodeBHist
        (hyperbolicHoroballShadowEventAtDefault 3 ef))
      (hyperbolicHoroballShadowDecodeBHist
        (hyperbolicHoroballShadowEventAtDefault 4 ef))
      (hyperbolicHoroballShadowDecodeBHist
        (hyperbolicHoroballShadowEventAtDefault 5 ef))
      (hyperbolicHoroballShadowDecodeBHist
        (hyperbolicHoroballShadowEventAtDefault 6 ef))
      (hyperbolicHoroballShadowDecodeBHist
        (hyperbolicHoroballShadowEventAtDefault 7 ef))
      (hyperbolicHoroballShadowDecodeBHist
        (hyperbolicHoroballShadowEventAtDefault 8 ef))
      (hyperbolicHoroballShadowDecodeBHist
        (hyperbolicHoroballShadowEventAtDefault 9 ef))
      (hyperbolicHoroballShadowDecodeBHist
        (hyperbolicHoroballShadowEventAtDefault 10 ef)))

private theorem hyperbolicHoroballShadow_round_trip :
    ∀ x : HyperbolicHoroballShadowUp,
      hyperbolicHoroballShadowFromEventFlow
          (hyperbolicHoroballShadowToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B V M O S R E H C P N =>
      change
        some
          (HyperbolicHoroballShadowUp.mk
            (hyperbolicHoroballShadowDecodeBHist
              (hyperbolicHoroballShadowEncodeBHist B))
            (hyperbolicHoroballShadowDecodeBHist
              (hyperbolicHoroballShadowEncodeBHist V))
            (hyperbolicHoroballShadowDecodeBHist
              (hyperbolicHoroballShadowEncodeBHist M))
            (hyperbolicHoroballShadowDecodeBHist
              (hyperbolicHoroballShadowEncodeBHist O))
            (hyperbolicHoroballShadowDecodeBHist
              (hyperbolicHoroballShadowEncodeBHist S))
            (hyperbolicHoroballShadowDecodeBHist
              (hyperbolicHoroballShadowEncodeBHist R))
            (hyperbolicHoroballShadowDecodeBHist
              (hyperbolicHoroballShadowEncodeBHist E))
            (hyperbolicHoroballShadowDecodeBHist
              (hyperbolicHoroballShadowEncodeBHist H))
            (hyperbolicHoroballShadowDecodeBHist
              (hyperbolicHoroballShadowEncodeBHist C))
            (hyperbolicHoroballShadowDecodeBHist
              (hyperbolicHoroballShadowEncodeBHist P))
            (hyperbolicHoroballShadowDecodeBHist
              (hyperbolicHoroballShadowEncodeBHist N))) =
          some (HyperbolicHoroballShadowUp.mk B V M O S R E H C P N)
      rw [hyperbolicHoroballShadow_decode_encode_bhist B,
        hyperbolicHoroballShadow_decode_encode_bhist V,
        hyperbolicHoroballShadow_decode_encode_bhist M,
        hyperbolicHoroballShadow_decode_encode_bhist O,
        hyperbolicHoroballShadow_decode_encode_bhist S,
        hyperbolicHoroballShadow_decode_encode_bhist R,
        hyperbolicHoroballShadow_decode_encode_bhist E,
        hyperbolicHoroballShadow_decode_encode_bhist H,
        hyperbolicHoroballShadow_decode_encode_bhist C,
        hyperbolicHoroballShadow_decode_encode_bhist P,
        hyperbolicHoroballShadow_decode_encode_bhist N]

private theorem hyperbolicHoroballShadowToEventFlow_injective
    {x y : HyperbolicHoroballShadowUp} :
    hyperbolicHoroballShadowToEventFlow x =
        hyperbolicHoroballShadowToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hyperbolicHoroballShadowFromEventFlow
          (hyperbolicHoroballShadowToEventFlow x) =
        hyperbolicHoroballShadowFromEventFlow
          (hyperbolicHoroballShadowToEventFlow y) :=
    congrArg hyperbolicHoroballShadowFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (hyperbolicHoroballShadow_round_trip x).symm
      (Eq.trans hread (hyperbolicHoroballShadow_round_trip y)))

private def hyperbolicHoroballShadowFields :
    HyperbolicHoroballShadowUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HyperbolicHoroballShadowUp.mk B V M O S R E H C P N =>
      [B, V, M, O, S, R, E, H, C, P, N]

private theorem hyperbolicHoroballShadow_fields_faithful :
    ∀ x y : HyperbolicHoroballShadowUp,
      hyperbolicHoroballShadowFields x = hyperbolicHoroballShadowFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk B₁ V₁ M₁ O₁ S₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk B₂ V₂ M₂ O₂ S₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          cases h
          rfl

instance hyperbolicHoroballShadowBHistCarrier :
    BHistCarrier HyperbolicHoroballShadowUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hyperbolicHoroballShadowToEventFlow
  fromEventFlow := hyperbolicHoroballShadowFromEventFlow

instance hyperbolicHoroballShadowChapterTasteGate :
    ChapterTasteGate HyperbolicHoroballShadowUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      hyperbolicHoroballShadowFromEventFlow
          (hyperbolicHoroballShadowToEventFlow x) =
        some x
    exact hyperbolicHoroballShadow_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (hyperbolicHoroballShadowToEventFlow_injective heq)

instance hyperbolicHoroballShadowFieldFaithful :
    FieldFaithful HyperbolicHoroballShadowUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := hyperbolicHoroballShadowFields
  field_faithful := hyperbolicHoroballShadow_fields_faithful

instance hyperbolicHoroballShadowNontrivial :
    BEDC.Meta.TasteGate.Nontrivial HyperbolicHoroballShadowUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HyperbolicHoroballShadowUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      HyperbolicHoroballShadowUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        injection h with hB _ _ _ _ _ _ _ _ _ _
        cases hB⟩

def taste_gate : ChapterTasteGate HyperbolicHoroballShadowUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hyperbolicHoroballShadowChapterTasteGate

theorem HyperbolicHoroballShadowTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      hyperbolicHoroballShadowDecodeBHist
          (hyperbolicHoroballShadowEncodeBHist h) =
        h) ∧
      (∀ x : HyperbolicHoroballShadowUp,
        hyperbolicHoroballShadowFromEventFlow
            (hyperbolicHoroballShadowToEventFlow x) =
          some x) ∧
        (∀ x y : HyperbolicHoroballShadowUp,
          hyperbolicHoroballShadowToEventFlow x =
              hyperbolicHoroballShadowToEventFlow y →
            x = y) ∧
          hyperbolicHoroballShadowEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨hyperbolicHoroballShadow_decode_encode_bhist,
      hyperbolicHoroballShadow_round_trip,
      (fun _ _ heq => hyperbolicHoroballShadowToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.HyperbolicHoroballShadowUp
