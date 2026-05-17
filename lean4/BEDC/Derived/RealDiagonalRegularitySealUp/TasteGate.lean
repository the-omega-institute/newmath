import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealDiagonalRegularitySealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealDiagonalRegularitySealUp : Type where
  | mk (D W T Q R E H C P N : BHist) : RealDiagonalRegularitySealUp

def realDiagonalRegularitySealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realDiagonalRegularitySealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realDiagonalRegularitySealEncodeBHist h

def realDiagonalRegularitySealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realDiagonalRegularitySealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realDiagonalRegularitySealDecodeBHist tail)

private theorem realDiagonalRegularitySealDecode_encode_bhist :
    ∀ h : BHist, realDiagonalRegularitySealDecodeBHist
      (realDiagonalRegularitySealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem realDiagonalRegularitySeal_mk_congr
    {D₁ D₂ W₁ W₂ T₁ T₂ Q₁ Q₂ R₁ R₂ E₁ E₂ H₁ H₂ C₁ C₂ P₁ P₂ N₁ N₂ :
      BHist} :
    D₁ = D₂ → W₁ = W₂ → T₁ = T₂ → Q₁ = Q₂ → R₁ = R₂ → E₁ = E₂ →
      H₁ = H₂ → C₁ = C₂ → P₁ = P₂ → N₁ = N₂ →
        RealDiagonalRegularitySealUp.mk D₁ W₁ T₁ Q₁ R₁ E₁ H₁ C₁ P₁ N₁ =
          RealDiagonalRegularitySealUp.mk D₂ W₂ T₂ Q₂ R₂ E₂ H₂ C₂ P₂ N₂ := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hD hW hT hQ hR hE hH hC hP hN
  cases hD
  cases hW
  cases hT
  cases hQ
  cases hR
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def realDiagonalRegularitySealToEventFlow : RealDiagonalRegularitySealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealDiagonalRegularitySealUp.mk D W T Q R E H C P N =>
      [realDiagonalRegularitySealEncodeBHist D,
        realDiagonalRegularitySealEncodeBHist W,
        realDiagonalRegularitySealEncodeBHist T,
        realDiagonalRegularitySealEncodeBHist Q,
        realDiagonalRegularitySealEncodeBHist R,
        realDiagonalRegularitySealEncodeBHist E,
        realDiagonalRegularitySealEncodeBHist H,
        realDiagonalRegularitySealEncodeBHist C,
        realDiagonalRegularitySealEncodeBHist P,
        realDiagonalRegularitySealEncodeBHist N]

def realDiagonalRegularitySealFromEventFlow : EventFlow → Option RealDiagonalRegularitySealUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | D :: rest0 =>
      match rest0 with
      | [] => none
      | W :: rest1 =>
          match rest1 with
          | [] => none
          | T :: rest2 =>
              match rest2 with
              | [] => none
              | Q :: rest3 =>
                  match rest3 with
                  | [] => none
                  | R :: rest4 =>
                      match rest4 with
                      | [] => none
                      | E :: rest5 =>
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
                                              some (RealDiagonalRegularitySealUp.mk
                                                (realDiagonalRegularitySealDecodeBHist D)
                                                (realDiagonalRegularitySealDecodeBHist W)
                                                (realDiagonalRegularitySealDecodeBHist T)
                                                (realDiagonalRegularitySealDecodeBHist Q)
                                                (realDiagonalRegularitySealDecodeBHist R)
                                                (realDiagonalRegularitySealDecodeBHist E)
                                                (realDiagonalRegularitySealDecodeBHist H)
                                                (realDiagonalRegularitySealDecodeBHist C)
                                                (realDiagonalRegularitySealDecodeBHist P)
                                                (realDiagonalRegularitySealDecodeBHist N))
                                          | _ :: _ => none

private theorem realDiagonalRegularitySeal_round_trip :
    ∀ x : RealDiagonalRegularitySealUp,
      realDiagonalRegularitySealFromEventFlow (realDiagonalRegularitySealToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D W T Q R E H C P N =>
      change
        some
          (RealDiagonalRegularitySealUp.mk
            (realDiagonalRegularitySealDecodeBHist (realDiagonalRegularitySealEncodeBHist D))
            (realDiagonalRegularitySealDecodeBHist (realDiagonalRegularitySealEncodeBHist W))
            (realDiagonalRegularitySealDecodeBHist (realDiagonalRegularitySealEncodeBHist T))
            (realDiagonalRegularitySealDecodeBHist (realDiagonalRegularitySealEncodeBHist Q))
            (realDiagonalRegularitySealDecodeBHist (realDiagonalRegularitySealEncodeBHist R))
            (realDiagonalRegularitySealDecodeBHist (realDiagonalRegularitySealEncodeBHist E))
            (realDiagonalRegularitySealDecodeBHist (realDiagonalRegularitySealEncodeBHist H))
            (realDiagonalRegularitySealDecodeBHist (realDiagonalRegularitySealEncodeBHist C))
            (realDiagonalRegularitySealDecodeBHist (realDiagonalRegularitySealEncodeBHist P))
            (realDiagonalRegularitySealDecodeBHist (realDiagonalRegularitySealEncodeBHist N))) =
          some (RealDiagonalRegularitySealUp.mk D W T Q R E H C P N)
      have hD := realDiagonalRegularitySealDecode_encode_bhist D
      have hW := realDiagonalRegularitySealDecode_encode_bhist W
      have hT := realDiagonalRegularitySealDecode_encode_bhist T
      have hQ := realDiagonalRegularitySealDecode_encode_bhist Q
      have hR := realDiagonalRegularitySealDecode_encode_bhist R
      have hE := realDiagonalRegularitySealDecode_encode_bhist E
      have hH := realDiagonalRegularitySealDecode_encode_bhist H
      have hC := realDiagonalRegularitySealDecode_encode_bhist C
      have hP := realDiagonalRegularitySealDecode_encode_bhist P
      have hN := realDiagonalRegularitySealDecode_encode_bhist N
      exact congrArg some
        (realDiagonalRegularitySeal_mk_congr hD hW hT hQ hR hE hH hC hP hN)

private theorem realDiagonalRegularitySealToEventFlow_injective
    {x y : RealDiagonalRegularitySealUp} :
    realDiagonalRegularitySealToEventFlow x = realDiagonalRegularitySealToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk D₁ W₁ T₁ Q₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk D₂ W₂ T₂ Q₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          injection heq with hD htail0
          injection htail0 with hW htail1
          injection htail1 with hT htail2
          injection htail2 with hQ htail3
          injection htail3 with hR htail4
          injection htail4 with hE htail5
          injection htail5 with hH htail6
          injection htail6 with hC htail7
          injection htail7 with hP htail8
          injection htail8 with hN _hNil
          have hD' : D₁ = D₂ := by
            exact Eq.trans (realDiagonalRegularitySealDecode_encode_bhist D₁).symm
              (Eq.trans (congrArg realDiagonalRegularitySealDecodeBHist hD)
                (realDiagonalRegularitySealDecode_encode_bhist D₂))
          have hW' : W₁ = W₂ := by
            exact Eq.trans (realDiagonalRegularitySealDecode_encode_bhist W₁).symm
              (Eq.trans (congrArg realDiagonalRegularitySealDecodeBHist hW)
                (realDiagonalRegularitySealDecode_encode_bhist W₂))
          have hT' : T₁ = T₂ := by
            exact Eq.trans (realDiagonalRegularitySealDecode_encode_bhist T₁).symm
              (Eq.trans (congrArg realDiagonalRegularitySealDecodeBHist hT)
                (realDiagonalRegularitySealDecode_encode_bhist T₂))
          have hQ' : Q₁ = Q₂ := by
            exact Eq.trans (realDiagonalRegularitySealDecode_encode_bhist Q₁).symm
              (Eq.trans (congrArg realDiagonalRegularitySealDecodeBHist hQ)
                (realDiagonalRegularitySealDecode_encode_bhist Q₂))
          have hR' : R₁ = R₂ := by
            exact Eq.trans (realDiagonalRegularitySealDecode_encode_bhist R₁).symm
              (Eq.trans (congrArg realDiagonalRegularitySealDecodeBHist hR)
                (realDiagonalRegularitySealDecode_encode_bhist R₂))
          have hE' : E₁ = E₂ := by
            exact Eq.trans (realDiagonalRegularitySealDecode_encode_bhist E₁).symm
              (Eq.trans (congrArg realDiagonalRegularitySealDecodeBHist hE)
                (realDiagonalRegularitySealDecode_encode_bhist E₂))
          have hH' : H₁ = H₂ := by
            exact Eq.trans (realDiagonalRegularitySealDecode_encode_bhist H₁).symm
              (Eq.trans (congrArg realDiagonalRegularitySealDecodeBHist hH)
                (realDiagonalRegularitySealDecode_encode_bhist H₂))
          have hC' : C₁ = C₂ := by
            exact Eq.trans (realDiagonalRegularitySealDecode_encode_bhist C₁).symm
              (Eq.trans (congrArg realDiagonalRegularitySealDecodeBHist hC)
                (realDiagonalRegularitySealDecode_encode_bhist C₂))
          have hP' : P₁ = P₂ := by
            exact Eq.trans (realDiagonalRegularitySealDecode_encode_bhist P₁).symm
              (Eq.trans (congrArg realDiagonalRegularitySealDecodeBHist hP)
                (realDiagonalRegularitySealDecode_encode_bhist P₂))
          have hN' : N₁ = N₂ := by
            exact Eq.trans (realDiagonalRegularitySealDecode_encode_bhist N₁).symm
              (Eq.trans (congrArg realDiagonalRegularitySealDecodeBHist hN)
                (realDiagonalRegularitySealDecode_encode_bhist N₂))
          exact realDiagonalRegularitySeal_mk_congr hD' hW' hT' hQ' hR' hE' hH'
            hC' hP' hN'

instance realDiagonalRegularitySealBHistCarrier :
    BHistCarrier RealDiagonalRegularitySealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realDiagonalRegularitySealToEventFlow
  fromEventFlow := realDiagonalRegularitySealFromEventFlow

instance realDiagonalRegularitySealChapterTasteGate :
    ChapterTasteGate RealDiagonalRegularitySealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realDiagonalRegularitySealFromEventFlow
      (realDiagonalRegularitySealToEventFlow x) = some x
    exact realDiagonalRegularitySeal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realDiagonalRegularitySealToEventFlow_injective heq)

instance realDiagonalRegularitySealFieldFaithful :
    FieldFaithful RealDiagonalRegularitySealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | RealDiagonalRegularitySealUp.mk D W T Q R E H C P N =>
        [D, W, T, Q, R, E, H, C, P, N]
  field_faithful := by
    intro x y h
    cases x with
    | mk D₁ W₁ T₁ Q₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
        cases y with
        | mk D₂ W₂ T₂ Q₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
            change [D₁, W₁, T₁, Q₁, R₁, E₁, H₁, C₁, P₁, N₁] =
              [D₂, W₂, T₂, Q₂, R₂, E₂, H₂, C₂, P₂, N₂] at h
            injection h with hD htail0
            injection htail0 with hW htail1
            injection htail1 with hT htail2
            injection htail2 with hQ htail3
            injection htail3 with hR htail4
            injection htail4 with hE htail5
            injection htail5 with hH htail6
            injection htail6 with hC htail7
            injection htail7 with hP htail8
            injection htail8 with hN _hNil
            exact realDiagonalRegularitySeal_mk_congr hD hW hT hQ hR hE hH hC hP hN

instance realDiagonalRegularitySealNontrivial : Nontrivial RealDiagonalRegularitySealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealDiagonalRegularitySealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealDiagonalRegularitySealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem RealDiagonalRegularitySealTasteGate_single_carrier_alignment :
    (∀ h : BHist, realDiagonalRegularitySealDecodeBHist
      (realDiagonalRegularitySealEncodeBHist h) = h) ∧
      (∀ x : RealDiagonalRegularitySealUp,
        realDiagonalRegularitySealFromEventFlow (realDiagonalRegularitySealToEventFlow x) =
          some x) ∧
      (∀ x y : RealDiagonalRegularitySealUp,
        realDiagonalRegularitySealToEventFlow x = realDiagonalRegularitySealToEventFlow y →
          x = y) ∧
      realDiagonalRegularitySealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact ⟨realDiagonalRegularitySealDecode_encode_bhist,
    realDiagonalRegularitySeal_round_trip,
    fun _ _ heq => realDiagonalRegularitySealToEventFlow_injective heq, rfl⟩

end BEDC.Derived.RealDiagonalRegularitySealUp
