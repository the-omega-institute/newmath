import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ChoquetSimplexUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ChoquetSimplexUp : Type where
  | mk (K V P B R E H C Q N : BHist) : ChoquetSimplexUp
  deriving DecidableEq

def choquetSimplexEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: choquetSimplexEncodeBHist h
  | BHist.e1 h => BMark.b1 :: choquetSimplexEncodeBHist h

def choquetSimplexDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (choquetSimplexDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (choquetSimplexDecodeBHist tail)

private theorem ChoquetSimplexTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, choquetSimplexDecodeBHist (choquetSimplexEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def choquetSimplexFields : ChoquetSimplexUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ChoquetSimplexUp.mk K V P B R E H C Q N => [K, V, P, B, R, E, H, C, Q, N]

def choquetSimplexToEventFlow : ChoquetSimplexUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (choquetSimplexFields x).map choquetSimplexEncodeBHist

def choquetSimplexFromEventFlow : EventFlow → Option ChoquetSimplexUp
  -- BEDC touchpoint anchor: BHist BMark
  | K :: V :: P :: B :: R :: E :: H :: C :: Q :: N :: [] =>
      some
        (ChoquetSimplexUp.mk
          (choquetSimplexDecodeBHist K)
          (choquetSimplexDecodeBHist V)
          (choquetSimplexDecodeBHist P)
          (choquetSimplexDecodeBHist B)
          (choquetSimplexDecodeBHist R)
          (choquetSimplexDecodeBHist E)
          (choquetSimplexDecodeBHist H)
          (choquetSimplexDecodeBHist C)
          (choquetSimplexDecodeBHist Q)
          (choquetSimplexDecodeBHist N))
  | _ => none

private theorem ChoquetSimplexTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ChoquetSimplexUp,
      choquetSimplexFromEventFlow (choquetSimplexToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K V P B R E H C Q N =>
      change
        some
          (ChoquetSimplexUp.mk
            (choquetSimplexDecodeBHist (choquetSimplexEncodeBHist K))
            (choquetSimplexDecodeBHist (choquetSimplexEncodeBHist V))
            (choquetSimplexDecodeBHist (choquetSimplexEncodeBHist P))
            (choquetSimplexDecodeBHist (choquetSimplexEncodeBHist B))
            (choquetSimplexDecodeBHist (choquetSimplexEncodeBHist R))
            (choquetSimplexDecodeBHist (choquetSimplexEncodeBHist E))
            (choquetSimplexDecodeBHist (choquetSimplexEncodeBHist H))
            (choquetSimplexDecodeBHist (choquetSimplexEncodeBHist C))
            (choquetSimplexDecodeBHist (choquetSimplexEncodeBHist Q))
            (choquetSimplexDecodeBHist (choquetSimplexEncodeBHist N))) =
          some (ChoquetSimplexUp.mk K V P B R E H C Q N)
      rw [ChoquetSimplexTasteGate_single_carrier_alignment_decode_encode K,
        ChoquetSimplexTasteGate_single_carrier_alignment_decode_encode V,
        ChoquetSimplexTasteGate_single_carrier_alignment_decode_encode P,
        ChoquetSimplexTasteGate_single_carrier_alignment_decode_encode B,
        ChoquetSimplexTasteGate_single_carrier_alignment_decode_encode R,
        ChoquetSimplexTasteGate_single_carrier_alignment_decode_encode E,
        ChoquetSimplexTasteGate_single_carrier_alignment_decode_encode H,
        ChoquetSimplexTasteGate_single_carrier_alignment_decode_encode C,
        ChoquetSimplexTasteGate_single_carrier_alignment_decode_encode Q,
        ChoquetSimplexTasteGate_single_carrier_alignment_decode_encode N]

private theorem ChoquetSimplexTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ChoquetSimplexUp} :
    choquetSimplexToEventFlow x = choquetSimplexToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      choquetSimplexFromEventFlow (choquetSimplexToEventFlow x) =
        choquetSimplexFromEventFlow (choquetSimplexToEventFlow y) :=
    congrArg choquetSimplexFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ChoquetSimplexTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ChoquetSimplexTasteGate_single_carrier_alignment_round_trip y)))

private theorem ChoquetSimplexTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : ChoquetSimplexUp, choquetSimplexFields x = choquetSimplexFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K₁ V₁ P₁ B₁ R₁ E₁ H₁ C₁ Q₁ N₁ =>
      cases y with
      | mk K₂ V₂ P₂ B₂ R₂ E₂ H₂ C₂ Q₂ N₂ =>
          cases hfields
          rfl

instance choquetSimplexBHistCarrier : BHistCarrier ChoquetSimplexUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := choquetSimplexToEventFlow
  fromEventFlow := choquetSimplexFromEventFlow

instance choquetSimplexChapterTasteGate : ChapterTasteGate ChoquetSimplexUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change choquetSimplexFromEventFlow (choquetSimplexToEventFlow x) = some x
    exact ChoquetSimplexTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ChoquetSimplexTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance choquetSimplexFieldFaithful : FieldFaithful ChoquetSimplexUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := choquetSimplexFields
  field_faithful := ChoquetSimplexTasteGate_single_carrier_alignment_fields_faithful

instance choquetSimplexNontrivial : BEDC.Meta.TasteGate.Nontrivial ChoquetSimplexUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ChoquetSimplexUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ChoquetSimplexUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ChoquetSimplexUp :=
  -- BEDC touchpoint anchor: BHist BMark
  choquetSimplexChapterTasteGate

theorem ChoquetSimplexTasteGate_single_carrier_alignment :
    (∀ h : BHist, choquetSimplexDecodeBHist (choquetSimplexEncodeBHist h) = h) ∧
      (∀ x y : ChoquetSimplexUp, choquetSimplexFields x = choquetSimplexFields y → x = y) ∧
      (∃ x : ChoquetSimplexUp,
        choquetSimplexFields x =
          [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
            BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty]) ∧
      (∃ y : ChoquetSimplexUp,
        choquetSimplexToEventFlow y =
          [[BMark.b0], [], [], [], [], [], [], [], [], []]) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact ChoquetSimplexTasteGate_single_carrier_alignment_decode_encode
  · exact
      ⟨ChoquetSimplexTasteGate_single_carrier_alignment_fields_faithful,
        ⟨ChoquetSimplexUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty, rfl⟩,
        ⟨ChoquetSimplexUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty, rfl⟩⟩

end BEDC.Derived.ChoquetSimplexUp
