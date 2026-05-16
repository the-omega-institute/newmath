import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TypedGapSocketTaxonomyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TypedGapSocketTaxonomyUp : Type where
  | mk (K G M L H C P N : BHist) : TypedGapSocketTaxonomyUp

def typedGapSocketTaxonomyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: typedGapSocketTaxonomyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: typedGapSocketTaxonomyEncodeBHist h

def typedGapSocketTaxonomyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (typedGapSocketTaxonomyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (typedGapSocketTaxonomyDecodeBHist tail)

private theorem typedGapSocketTaxonomyDecode_encode_bhist :
    ∀ h : BHist, typedGapSocketTaxonomyDecodeBHist
      (typedGapSocketTaxonomyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem typedGapSocketTaxonomy_mk_congr
    {K₁ K₂ G₁ G₂ M₁ M₂ L₁ L₂ H₁ H₂ C₁ C₂ P₁ P₂ N₁ N₂ : BHist} :
    K₁ = K₂ → G₁ = G₂ → M₁ = M₂ → L₁ = L₂ → H₁ = H₂ → C₁ = C₂ →
      P₁ = P₂ → N₁ = N₂ →
        TypedGapSocketTaxonomyUp.mk K₁ G₁ M₁ L₁ H₁ C₁ P₁ N₁ =
          TypedGapSocketTaxonomyUp.mk K₂ G₂ M₂ L₂ H₂ C₂ P₂ N₂ := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hK hG hM hL hH hC hP hN
  cases hK
  cases hG
  cases hM
  cases hL
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def typedGapSocketTaxonomyToEventFlow : TypedGapSocketTaxonomyUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | TypedGapSocketTaxonomyUp.mk K G M L H C P N =>
      [typedGapSocketTaxonomyEncodeBHist K,
        typedGapSocketTaxonomyEncodeBHist G,
        typedGapSocketTaxonomyEncodeBHist M,
        typedGapSocketTaxonomyEncodeBHist L,
        typedGapSocketTaxonomyEncodeBHist H,
        typedGapSocketTaxonomyEncodeBHist C,
        typedGapSocketTaxonomyEncodeBHist P,
        typedGapSocketTaxonomyEncodeBHist N]

def typedGapSocketTaxonomyFromEventFlow : EventFlow → Option TypedGapSocketTaxonomyUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | K :: rest0 =>
      match rest0 with
      | [] => none
      | G :: rest1 =>
          match rest1 with
          | [] => none
          | M :: rest2 =>
              match rest2 with
              | [] => none
              | L :: rest3 =>
                  match rest3 with
                  | [] => none
                  | H :: rest4 =>
                      match rest4 with
                      | [] => none
                      | C :: rest5 =>
                          match rest5 with
                          | [] => none
                          | P :: rest6 =>
                              match rest6 with
                              | [] => none
                              | N :: rest7 =>
                                  match rest7 with
                                  | [] =>
                                      some (TypedGapSocketTaxonomyUp.mk
                                        (typedGapSocketTaxonomyDecodeBHist K)
                                        (typedGapSocketTaxonomyDecodeBHist G)
                                        (typedGapSocketTaxonomyDecodeBHist M)
                                        (typedGapSocketTaxonomyDecodeBHist L)
                                        (typedGapSocketTaxonomyDecodeBHist H)
                                        (typedGapSocketTaxonomyDecodeBHist C)
                                        (typedGapSocketTaxonomyDecodeBHist P)
                                        (typedGapSocketTaxonomyDecodeBHist N))
                                  | _ :: _ => none

private theorem typedGapSocketTaxonomy_round_trip :
    ∀ x : TypedGapSocketTaxonomyUp,
      typedGapSocketTaxonomyFromEventFlow (typedGapSocketTaxonomyToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K G M L H C P N =>
      change
        some
          (TypedGapSocketTaxonomyUp.mk
            (typedGapSocketTaxonomyDecodeBHist (typedGapSocketTaxonomyEncodeBHist K))
            (typedGapSocketTaxonomyDecodeBHist (typedGapSocketTaxonomyEncodeBHist G))
            (typedGapSocketTaxonomyDecodeBHist (typedGapSocketTaxonomyEncodeBHist M))
            (typedGapSocketTaxonomyDecodeBHist (typedGapSocketTaxonomyEncodeBHist L))
            (typedGapSocketTaxonomyDecodeBHist (typedGapSocketTaxonomyEncodeBHist H))
            (typedGapSocketTaxonomyDecodeBHist (typedGapSocketTaxonomyEncodeBHist C))
            (typedGapSocketTaxonomyDecodeBHist (typedGapSocketTaxonomyEncodeBHist P))
            (typedGapSocketTaxonomyDecodeBHist (typedGapSocketTaxonomyEncodeBHist N))) =
          some (TypedGapSocketTaxonomyUp.mk K G M L H C P N)
      have hK := typedGapSocketTaxonomyDecode_encode_bhist K
      have hG := typedGapSocketTaxonomyDecode_encode_bhist G
      have hM := typedGapSocketTaxonomyDecode_encode_bhist M
      have hL := typedGapSocketTaxonomyDecode_encode_bhist L
      have hH := typedGapSocketTaxonomyDecode_encode_bhist H
      have hC := typedGapSocketTaxonomyDecode_encode_bhist C
      have hP := typedGapSocketTaxonomyDecode_encode_bhist P
      have hN := typedGapSocketTaxonomyDecode_encode_bhist N
      exact congrArg some
        (typedGapSocketTaxonomy_mk_congr hK hG hM hL hH hC hP hN)

private theorem typedGapSocketTaxonomyToEventFlow_injective
    {x y : TypedGapSocketTaxonomyUp} :
    typedGapSocketTaxonomyToEventFlow x = typedGapSocketTaxonomyToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk K₁ G₁ M₁ L₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk K₂ G₂ M₂ L₂ H₂ C₂ P₂ N₂ =>
          injection heq with hK htail0
          injection htail0 with hG htail1
          injection htail1 with hM htail2
          injection htail2 with hL htail3
          injection htail3 with hH htail4
          injection htail4 with hC htail5
          injection htail5 with hP htail6
          injection htail6 with hN _hNil
          have hK' : K₁ = K₂ := by
            exact Eq.trans (typedGapSocketTaxonomyDecode_encode_bhist K₁).symm
              (Eq.trans (congrArg typedGapSocketTaxonomyDecodeBHist hK)
                (typedGapSocketTaxonomyDecode_encode_bhist K₂))
          have hG' : G₁ = G₂ := by
            exact Eq.trans (typedGapSocketTaxonomyDecode_encode_bhist G₁).symm
              (Eq.trans (congrArg typedGapSocketTaxonomyDecodeBHist hG)
                (typedGapSocketTaxonomyDecode_encode_bhist G₂))
          have hM' : M₁ = M₂ := by
            exact Eq.trans (typedGapSocketTaxonomyDecode_encode_bhist M₁).symm
              (Eq.trans (congrArg typedGapSocketTaxonomyDecodeBHist hM)
                (typedGapSocketTaxonomyDecode_encode_bhist M₂))
          have hL' : L₁ = L₂ := by
            exact Eq.trans (typedGapSocketTaxonomyDecode_encode_bhist L₁).symm
              (Eq.trans (congrArg typedGapSocketTaxonomyDecodeBHist hL)
                (typedGapSocketTaxonomyDecode_encode_bhist L₂))
          have hH' : H₁ = H₂ := by
            exact Eq.trans (typedGapSocketTaxonomyDecode_encode_bhist H₁).symm
              (Eq.trans (congrArg typedGapSocketTaxonomyDecodeBHist hH)
                (typedGapSocketTaxonomyDecode_encode_bhist H₂))
          have hC' : C₁ = C₂ := by
            exact Eq.trans (typedGapSocketTaxonomyDecode_encode_bhist C₁).symm
              (Eq.trans (congrArg typedGapSocketTaxonomyDecodeBHist hC)
                (typedGapSocketTaxonomyDecode_encode_bhist C₂))
          have hP' : P₁ = P₂ := by
            exact Eq.trans (typedGapSocketTaxonomyDecode_encode_bhist P₁).symm
              (Eq.trans (congrArg typedGapSocketTaxonomyDecodeBHist hP)
                (typedGapSocketTaxonomyDecode_encode_bhist P₂))
          have hN' : N₁ = N₂ := by
            exact Eq.trans (typedGapSocketTaxonomyDecode_encode_bhist N₁).symm
              (Eq.trans (congrArg typedGapSocketTaxonomyDecodeBHist hN)
                (typedGapSocketTaxonomyDecode_encode_bhist N₂))
          exact typedGapSocketTaxonomy_mk_congr hK' hG' hM' hL' hH' hC' hP' hN'

instance typedGapSocketTaxonomyBHistCarrier : BHistCarrier TypedGapSocketTaxonomyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := typedGapSocketTaxonomyToEventFlow
  fromEventFlow := typedGapSocketTaxonomyFromEventFlow

instance typedGapSocketTaxonomyChapterTasteGate :
    ChapterTasteGate TypedGapSocketTaxonomyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change typedGapSocketTaxonomyFromEventFlow
      (typedGapSocketTaxonomyToEventFlow x) = some x
    exact typedGapSocketTaxonomy_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (typedGapSocketTaxonomyToEventFlow_injective heq)

instance typedGapSocketTaxonomyFieldFaithful : FieldFaithful TypedGapSocketTaxonomyUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | TypedGapSocketTaxonomyUp.mk K G M L H C P N => [K, G, M, L, H, C, P, N]
  field_faithful := by
    intro x y h
    cases x with
    | mk K₁ G₁ M₁ L₁ H₁ C₁ P₁ N₁ =>
        cases y with
        | mk K₂ G₂ M₂ L₂ H₂ C₂ P₂ N₂ =>
            change [K₁, G₁, M₁, L₁, H₁, C₁, P₁, N₁] =
              [K₂, G₂, M₂, L₂, H₂, C₂, P₂, N₂] at h
            injection h with hK htail0
            injection htail0 with hG htail1
            injection htail1 with hM htail2
            injection htail2 with hL htail3
            injection htail3 with hH htail4
            injection htail4 with hC htail5
            injection htail5 with hP htail6
            injection htail6 with hN _hNil
            exact typedGapSocketTaxonomy_mk_congr hK hG hM hL hH hC hP hN

instance typedGapSocketTaxonomyNontrivial : Nontrivial TypedGapSocketTaxonomyUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨TypedGapSocketTaxonomyUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      TypedGapSocketTaxonomyUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem TypedGapSocketTaxonomyTasteGate_single_carrier_alignment :
    (∀ h : BHist, typedGapSocketTaxonomyDecodeBHist
      (typedGapSocketTaxonomyEncodeBHist h) = h) ∧
      (∀ x : TypedGapSocketTaxonomyUp,
        typedGapSocketTaxonomyFromEventFlow (typedGapSocketTaxonomyToEventFlow x) =
          some x) ∧
      (∀ x y : TypedGapSocketTaxonomyUp,
        typedGapSocketTaxonomyToEventFlow x = typedGapSocketTaxonomyToEventFlow y →
          x = y) ∧
      typedGapSocketTaxonomyEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact ⟨typedGapSocketTaxonomyDecode_encode_bhist, typedGapSocketTaxonomy_round_trip,
    fun _ _ heq => typedGapSocketTaxonomyToEventFlow_injective heq, rfl⟩

end BEDC.Derived.TypedGapSocketTaxonomyUp
