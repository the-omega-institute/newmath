import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICStrongNormalizationBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICStrongNormalizationBoundaryUp : Type where
  | mk (S F Z U T R H C P N : BHist) : MetaCICStrongNormalizationBoundaryUp
  deriving DecidableEq

def metaCICStrongNormalizationBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaCICStrongNormalizationBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaCICStrongNormalizationBoundaryEncodeBHist h

def metaCICStrongNormalizationBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaCICStrongNormalizationBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaCICStrongNormalizationBoundaryDecodeBHist tail)

private theorem MetaCICStrongNormalizationBoundaryTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      metaCICStrongNormalizationBoundaryDecodeBHist
        (metaCICStrongNormalizationBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem metaCICStrongNormalizationBoundaryEncodeBHist_injective
    {h k : BHist} :
    metaCICStrongNormalizationBoundaryEncodeBHist h =
      metaCICStrongNormalizationBoundaryEncodeBHist k → h = k := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  exact
    Eq.trans
      (MetaCICStrongNormalizationBoundaryTasteGate_single_carrier_alignment_decode h).symm
      (Eq.trans (congrArg metaCICStrongNormalizationBoundaryDecodeBHist heq)
        (MetaCICStrongNormalizationBoundaryTasteGate_single_carrier_alignment_decode k))

private theorem metaCICStrongNormalizationBoundary_mk_congr
    {S S' F F' Z Z' U U' T T' R R' H H' C C' P P' N N' : BHist}
    (hS : S' = S) (hF : F' = F) (hZ : Z' = Z) (hU : U' = U)
    (hT : T' = T) (hR : R' = R) (hH : H' = H) (hC : C' = C)
    (hP : P' = P) (hN : N' = N) :
    MetaCICStrongNormalizationBoundaryUp.mk S' F' Z' U' T' R' H' C' P' N' =
      MetaCICStrongNormalizationBoundaryUp.mk S F Z U T R H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hS
  cases hF
  cases hZ
  cases hU
  cases hT
  cases hR
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def metaCICStrongNormalizationBoundaryFields :
    MetaCICStrongNormalizationBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICStrongNormalizationBoundaryUp.mk S F Z U T R H C P N =>
      [S, F, Z, U, T, R, H, C, P, N]

def metaCICStrongNormalizationBoundaryToEventFlow :
    MetaCICStrongNormalizationBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICStrongNormalizationBoundaryUp.mk S F Z U T R H C P N =>
      [metaCICStrongNormalizationBoundaryEncodeBHist S,
        metaCICStrongNormalizationBoundaryEncodeBHist F,
        metaCICStrongNormalizationBoundaryEncodeBHist Z,
        metaCICStrongNormalizationBoundaryEncodeBHist U,
        metaCICStrongNormalizationBoundaryEncodeBHist T,
        metaCICStrongNormalizationBoundaryEncodeBHist R,
        metaCICStrongNormalizationBoundaryEncodeBHist H,
        metaCICStrongNormalizationBoundaryEncodeBHist C,
        metaCICStrongNormalizationBoundaryEncodeBHist P,
        metaCICStrongNormalizationBoundaryEncodeBHist N]

def metaCICStrongNormalizationBoundaryFromEventFlow :
    EventFlow → Option MetaCICStrongNormalizationBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | S :: rest0 =>
      match rest0 with
      | [] => none
      | F :: rest1 =>
          match rest1 with
          | [] => none
          | Z :: rest2 =>
              match rest2 with
              | [] => none
              | U :: rest3 =>
                  match rest3 with
                  | [] => none
                  | T :: rest4 =>
                      match rest4 with
                      | [] => none
                      | R :: rest5 =>
                          match rest5 with
                          | [] => none
                          | H :: rest6 =>
                              match rest6 with
                              | [] => none
                              | C :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | P :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | N :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (MetaCICStrongNormalizationBoundaryUp.mk
                                                  (metaCICStrongNormalizationBoundaryDecodeBHist S)
                                                  (metaCICStrongNormalizationBoundaryDecodeBHist F)
                                                  (metaCICStrongNormalizationBoundaryDecodeBHist Z)
                                                  (metaCICStrongNormalizationBoundaryDecodeBHist U)
                                                  (metaCICStrongNormalizationBoundaryDecodeBHist T)
                                                  (metaCICStrongNormalizationBoundaryDecodeBHist R)
                                                  (metaCICStrongNormalizationBoundaryDecodeBHist H)
                                                  (metaCICStrongNormalizationBoundaryDecodeBHist C)
                                                  (metaCICStrongNormalizationBoundaryDecodeBHist P)
                                                  (metaCICStrongNormalizationBoundaryDecodeBHist N))
                                          | _ :: _ => none

private theorem MetaCICStrongNormalizationBoundaryTasteGate_single_carrier_alignment_round_trip :
    ∀ x : MetaCICStrongNormalizationBoundaryUp,
      metaCICStrongNormalizationBoundaryFromEventFlow
        (metaCICStrongNormalizationBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S F Z U T R H C P N =>
      exact
        congrArg some
          (metaCICStrongNormalizationBoundary_mk_congr
            (MetaCICStrongNormalizationBoundaryTasteGate_single_carrier_alignment_decode S)
            (MetaCICStrongNormalizationBoundaryTasteGate_single_carrier_alignment_decode F)
            (MetaCICStrongNormalizationBoundaryTasteGate_single_carrier_alignment_decode Z)
            (MetaCICStrongNormalizationBoundaryTasteGate_single_carrier_alignment_decode U)
            (MetaCICStrongNormalizationBoundaryTasteGate_single_carrier_alignment_decode T)
            (MetaCICStrongNormalizationBoundaryTasteGate_single_carrier_alignment_decode R)
            (MetaCICStrongNormalizationBoundaryTasteGate_single_carrier_alignment_decode H)
            (MetaCICStrongNormalizationBoundaryTasteGate_single_carrier_alignment_decode C)
            (MetaCICStrongNormalizationBoundaryTasteGate_single_carrier_alignment_decode P)
            (MetaCICStrongNormalizationBoundaryTasteGate_single_carrier_alignment_decode N))

private theorem metaCICStrongNormalizationBoundaryToEventFlow_injective
    {x y : MetaCICStrongNormalizationBoundaryUp} :
    metaCICStrongNormalizationBoundaryToEventFlow x =
      metaCICStrongNormalizationBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaCICStrongNormalizationBoundaryFromEventFlow
          (metaCICStrongNormalizationBoundaryToEventFlow x) =
        metaCICStrongNormalizationBoundaryFromEventFlow
          (metaCICStrongNormalizationBoundaryToEventFlow y) :=
    congrArg metaCICStrongNormalizationBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (MetaCICStrongNormalizationBoundaryTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (MetaCICStrongNormalizationBoundaryTasteGate_single_carrier_alignment_round_trip y)))

private theorem MetaCICStrongNormalizationBoundaryTasteGate_single_carrier_alignment_fields :
    ∀ x y : MetaCICStrongNormalizationBoundaryUp,
      metaCICStrongNormalizationBoundaryFields x =
        metaCICStrongNormalizationBoundaryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S₁ F₁ Z₁ U₁ T₁ R₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ F₂ Z₂ U₂ T₂ R₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hS tail0
          injection tail0 with hF tail1
          injection tail1 with hZ tail2
          injection tail2 with hU tail3
          injection tail3 with hT tail4
          injection tail4 with hR tail5
          injection tail5 with hH tail6
          injection tail6 with hC tail7
          injection tail7 with hP tail8
          injection tail8 with hN _
          subst hS
          subst hF
          subst hZ
          subst hU
          subst hT
          subst hR
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance metaCICStrongNormalizationBoundaryBHistCarrier :
    BHistCarrier MetaCICStrongNormalizationBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaCICStrongNormalizationBoundaryToEventFlow
  fromEventFlow := metaCICStrongNormalizationBoundaryFromEventFlow

instance metaCICStrongNormalizationBoundaryChapterTasteGate :
    ChapterTasteGate MetaCICStrongNormalizationBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metaCICStrongNormalizationBoundaryFromEventFlow
        (metaCICStrongNormalizationBoundaryToEventFlow x) = some x
    exact MetaCICStrongNormalizationBoundaryTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metaCICStrongNormalizationBoundaryToEventFlow_injective heq)

instance metaCICStrongNormalizationBoundaryFieldFaithful :
    FieldFaithful MetaCICStrongNormalizationBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metaCICStrongNormalizationBoundaryFields
  field_faithful := MetaCICStrongNormalizationBoundaryTasteGate_single_carrier_alignment_fields

instance metaCICStrongNormalizationBoundaryNontrivial :
    Nontrivial MetaCICStrongNormalizationBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetaCICStrongNormalizationBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MetaCICStrongNormalizationBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MetaCICStrongNormalizationBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metaCICStrongNormalizationBoundaryChapterTasteGate

theorem MetaCICStrongNormalizationBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      metaCICStrongNormalizationBoundaryDecodeBHist
        (metaCICStrongNormalizationBoundaryEncodeBHist h) = h) ∧
      (∀ x : MetaCICStrongNormalizationBoundaryUp,
        metaCICStrongNormalizationBoundaryFromEventFlow
          (metaCICStrongNormalizationBoundaryToEventFlow x) = some x) ∧
      (∀ x y : MetaCICStrongNormalizationBoundaryUp,
        metaCICStrongNormalizationBoundaryToEventFlow x =
          metaCICStrongNormalizationBoundaryToEventFlow y → x = y) ∧
      metaCICStrongNormalizationBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact MetaCICStrongNormalizationBoundaryTasteGate_single_carrier_alignment_decode
  constructor
  · intro x
    cases x with
    | mk S F Z U T R H C P N =>
        exact
          congrArg some
            (metaCICStrongNormalizationBoundary_mk_congr
              (MetaCICStrongNormalizationBoundaryTasteGate_single_carrier_alignment_decode S)
              (MetaCICStrongNormalizationBoundaryTasteGate_single_carrier_alignment_decode F)
              (MetaCICStrongNormalizationBoundaryTasteGate_single_carrier_alignment_decode Z)
              (MetaCICStrongNormalizationBoundaryTasteGate_single_carrier_alignment_decode U)
              (MetaCICStrongNormalizationBoundaryTasteGate_single_carrier_alignment_decode T)
              (MetaCICStrongNormalizationBoundaryTasteGate_single_carrier_alignment_decode R)
              (MetaCICStrongNormalizationBoundaryTasteGate_single_carrier_alignment_decode H)
              (MetaCICStrongNormalizationBoundaryTasteGate_single_carrier_alignment_decode C)
              (MetaCICStrongNormalizationBoundaryTasteGate_single_carrier_alignment_decode P)
              (MetaCICStrongNormalizationBoundaryTasteGate_single_carrier_alignment_decode N))
  constructor
  · intro x y heq
    cases x with
    | mk S₁ F₁ Z₁ U₁ T₁ R₁ H₁ C₁ P₁ N₁ =>
        cases y with
        | mk S₂ F₂ Z₂ U₂ T₂ R₂ H₂ C₂ P₂ N₂ =>
            injection heq with hS tail0
            injection tail0 with hF tail1
            injection tail1 with hZ tail2
            injection tail2 with hU tail3
            injection tail3 with hT tail4
            injection tail4 with hR tail5
            injection tail5 with hH tail6
            injection tail6 with hC tail7
            injection tail7 with hP tail8
            injection tail8 with hN _
            exact
              metaCICStrongNormalizationBoundary_mk_congr
                (metaCICStrongNormalizationBoundaryEncodeBHist_injective hS)
                (metaCICStrongNormalizationBoundaryEncodeBHist_injective hF)
                (metaCICStrongNormalizationBoundaryEncodeBHist_injective hZ)
                (metaCICStrongNormalizationBoundaryEncodeBHist_injective hU)
                (metaCICStrongNormalizationBoundaryEncodeBHist_injective hT)
                (metaCICStrongNormalizationBoundaryEncodeBHist_injective hR)
                (metaCICStrongNormalizationBoundaryEncodeBHist_injective hH)
                (metaCICStrongNormalizationBoundaryEncodeBHist_injective hC)
                (metaCICStrongNormalizationBoundaryEncodeBHist_injective hP)
                (metaCICStrongNormalizationBoundaryEncodeBHist_injective hN)
  · rfl

end BEDC.Derived.MetaCICStrongNormalizationBoundaryUp
