import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealityConstrainedSignatureResidueUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealityConstrainedSignatureResidueUp : Type where
  | mk : (M S G R W H C P N : BHist) → RealityConstrainedSignatureResidueUp
  deriving DecidableEq

def realityConstrainedSignatureResidueEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realityConstrainedSignatureResidueEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realityConstrainedSignatureResidueEncodeBHist h

def realityConstrainedSignatureResidueDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realityConstrainedSignatureResidueDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realityConstrainedSignatureResidueDecodeBHist tail)

private theorem realityConstrainedSignatureResidueDecode_encode_bhist :
    ∀ h : BHist,
      realityConstrainedSignatureResidueDecodeBHist
        (realityConstrainedSignatureResidueEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem realityConstrainedSignatureResidue_mk_congr
    {M M' S S' G G' R R' W W' H H' C C' P P' N N' : BHist}
    (hM : M' = M) (hS : S' = S) (hG : G' = G) (hR : R' = R)
    (hW : W' = W) (hH : H' = H) (hC : C' = C) (hP : P' = P)
    (hN : N' = N) :
    RealityConstrainedSignatureResidueUp.mk M' S' G' R' W' H' C' P' N' =
      RealityConstrainedSignatureResidueUp.mk M S G R W H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hM
  cases hS
  cases hG
  cases hR
  cases hW
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def realityConstrainedSignatureResidueToEventFlow :
    RealityConstrainedSignatureResidueUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealityConstrainedSignatureResidueUp.mk M S G R W H C P N =>
      [[BMark.b0],
        realityConstrainedSignatureResidueEncodeBHist M,
        [BMark.b1, BMark.b0],
        realityConstrainedSignatureResidueEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedSignatureResidueEncodeBHist G,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedSignatureResidueEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedSignatureResidueEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedSignatureResidueEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedSignatureResidueEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        realityConstrainedSignatureResidueEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        realityConstrainedSignatureResidueEncodeBHist N]

def realityConstrainedSignatureResidueFromEventFlow :
    EventFlow → Option RealityConstrainedSignatureResidueUp
  -- BEDC touchpoint anchor: BHist BMark
  | _tag0 :: M :: _tag1 :: S :: _tag2 :: G :: _tag3 :: R :: _tag4 :: W ::
      _tag5 :: H :: _tag6 :: C :: _tag7 :: P :: _tag8 :: N :: [] =>
      some
        (RealityConstrainedSignatureResidueUp.mk
          (realityConstrainedSignatureResidueDecodeBHist M)
          (realityConstrainedSignatureResidueDecodeBHist S)
          (realityConstrainedSignatureResidueDecodeBHist G)
          (realityConstrainedSignatureResidueDecodeBHist R)
          (realityConstrainedSignatureResidueDecodeBHist W)
          (realityConstrainedSignatureResidueDecodeBHist H)
          (realityConstrainedSignatureResidueDecodeBHist C)
          (realityConstrainedSignatureResidueDecodeBHist P)
          (realityConstrainedSignatureResidueDecodeBHist N))
  | _ => none

private theorem realityConstrainedSignatureResidue_round_trip :
    ∀ x : RealityConstrainedSignatureResidueUp,
      realityConstrainedSignatureResidueFromEventFlow
        (realityConstrainedSignatureResidueToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M S G R W H C P N =>
      change
        some
          (RealityConstrainedSignatureResidueUp.mk
            (realityConstrainedSignatureResidueDecodeBHist
              (realityConstrainedSignatureResidueEncodeBHist M))
            (realityConstrainedSignatureResidueDecodeBHist
              (realityConstrainedSignatureResidueEncodeBHist S))
            (realityConstrainedSignatureResidueDecodeBHist
              (realityConstrainedSignatureResidueEncodeBHist G))
            (realityConstrainedSignatureResidueDecodeBHist
              (realityConstrainedSignatureResidueEncodeBHist R))
            (realityConstrainedSignatureResidueDecodeBHist
              (realityConstrainedSignatureResidueEncodeBHist W))
            (realityConstrainedSignatureResidueDecodeBHist
              (realityConstrainedSignatureResidueEncodeBHist H))
            (realityConstrainedSignatureResidueDecodeBHist
              (realityConstrainedSignatureResidueEncodeBHist C))
            (realityConstrainedSignatureResidueDecodeBHist
              (realityConstrainedSignatureResidueEncodeBHist P))
            (realityConstrainedSignatureResidueDecodeBHist
              (realityConstrainedSignatureResidueEncodeBHist N))) =
          some (RealityConstrainedSignatureResidueUp.mk M S G R W H C P N)
      exact
        congrArg some
          (realityConstrainedSignatureResidue_mk_congr
            (realityConstrainedSignatureResidueDecode_encode_bhist M)
            (realityConstrainedSignatureResidueDecode_encode_bhist S)
            (realityConstrainedSignatureResidueDecode_encode_bhist G)
            (realityConstrainedSignatureResidueDecode_encode_bhist R)
            (realityConstrainedSignatureResidueDecode_encode_bhist W)
            (realityConstrainedSignatureResidueDecode_encode_bhist H)
            (realityConstrainedSignatureResidueDecode_encode_bhist C)
            (realityConstrainedSignatureResidueDecode_encode_bhist P)
            (realityConstrainedSignatureResidueDecode_encode_bhist N))

private theorem realityConstrainedSignatureResidueToEventFlow_injective
    {x y : RealityConstrainedSignatureResidueUp} :
    realityConstrainedSignatureResidueToEventFlow x =
      realityConstrainedSignatureResidueToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk M₁ S₁ G₁ R₁ W₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk M₂ S₂ G₂ R₂ W₂ H₂ C₂ P₂ N₂ =>
          injection heq with _ tail0
          injection tail0 with hM tail1
          injection tail1 with _ tail2
          injection tail2 with hS tail3
          injection tail3 with _ tail4
          injection tail4 with hG tail5
          injection tail5 with _ tail6
          injection tail6 with hR tail7
          injection tail7 with _ tail8
          injection tail8 with hW tail9
          injection tail9 with _ tail10
          injection tail10 with hH tail11
          injection tail11 with _ tail12
          injection tail12 with hC tail13
          injection tail13 with _ tail14
          injection tail14 with hP tail15
          injection tail15 with _ tail16
          injection tail16 with hN _
          have hMd : M₁ = M₂ := by
            have h := congrArg realityConstrainedSignatureResidueDecodeBHist hM
            rw [realityConstrainedSignatureResidueDecode_encode_bhist] at h
            exact Eq.trans h (realityConstrainedSignatureResidueDecode_encode_bhist M₂)
          have hSd : S₁ = S₂ := by
            have h := congrArg realityConstrainedSignatureResidueDecodeBHist hS
            rw [realityConstrainedSignatureResidueDecode_encode_bhist] at h
            exact Eq.trans h (realityConstrainedSignatureResidueDecode_encode_bhist S₂)
          have hGd : G₁ = G₂ := by
            have h := congrArg realityConstrainedSignatureResidueDecodeBHist hG
            rw [realityConstrainedSignatureResidueDecode_encode_bhist] at h
            exact Eq.trans h (realityConstrainedSignatureResidueDecode_encode_bhist G₂)
          have hRd : R₁ = R₂ := by
            have h := congrArg realityConstrainedSignatureResidueDecodeBHist hR
            rw [realityConstrainedSignatureResidueDecode_encode_bhist] at h
            exact Eq.trans h (realityConstrainedSignatureResidueDecode_encode_bhist R₂)
          have hWd : W₁ = W₂ := by
            have h := congrArg realityConstrainedSignatureResidueDecodeBHist hW
            rw [realityConstrainedSignatureResidueDecode_encode_bhist] at h
            exact Eq.trans h (realityConstrainedSignatureResidueDecode_encode_bhist W₂)
          have hHd : H₁ = H₂ := by
            have h := congrArg realityConstrainedSignatureResidueDecodeBHist hH
            rw [realityConstrainedSignatureResidueDecode_encode_bhist] at h
            exact Eq.trans h (realityConstrainedSignatureResidueDecode_encode_bhist H₂)
          have hCd : C₁ = C₂ := by
            have h := congrArg realityConstrainedSignatureResidueDecodeBHist hC
            rw [realityConstrainedSignatureResidueDecode_encode_bhist] at h
            exact Eq.trans h (realityConstrainedSignatureResidueDecode_encode_bhist C₂)
          have hPd : P₁ = P₂ := by
            have h := congrArg realityConstrainedSignatureResidueDecodeBHist hP
            rw [realityConstrainedSignatureResidueDecode_encode_bhist] at h
            exact Eq.trans h (realityConstrainedSignatureResidueDecode_encode_bhist P₂)
          have hNd : N₁ = N₂ := by
            have h := congrArg realityConstrainedSignatureResidueDecodeBHist hN
            rw [realityConstrainedSignatureResidueDecode_encode_bhist] at h
            exact Eq.trans h (realityConstrainedSignatureResidueDecode_encode_bhist N₂)
          cases hMd
          cases hSd
          cases hGd
          cases hRd
          cases hWd
          cases hHd
          cases hCd
          cases hPd
          cases hNd
          rfl

instance realityConstrainedSignatureResidueBHistCarrier :
    BHistCarrier RealityConstrainedSignatureResidueUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realityConstrainedSignatureResidueToEventFlow
  fromEventFlow := realityConstrainedSignatureResidueFromEventFlow

instance realityConstrainedSignatureResidueChapterTasteGate :
    ChapterTasteGate RealityConstrainedSignatureResidueUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realityConstrainedSignatureResidueFromEventFlow
        (realityConstrainedSignatureResidueToEventFlow x) = some x
    exact realityConstrainedSignatureResidue_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realityConstrainedSignatureResidueToEventFlow_injective heq)

def realityConstrainedSignatureResidueFields :
    RealityConstrainedSignatureResidueUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealityConstrainedSignatureResidueUp.mk M S G R W H C P N => [M, S, G, R, W, H, C, P, N]

instance realityConstrainedSignatureResidueFieldFaithful :
    FieldFaithful RealityConstrainedSignatureResidueUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realityConstrainedSignatureResidueFields
  field_faithful := by
    intro x y h
    cases x with
    | mk M₁ S₁ G₁ R₁ W₁ H₁ C₁ P₁ N₁ =>
        cases y with
        | mk M₂ S₂ G₂ R₂ W₂ H₂ C₂ P₂ N₂ =>
            injection h with hM hRest₁
            injection hRest₁ with hS hRest₂
            injection hRest₂ with hG hRest₃
            injection hRest₃ with hR hRest₄
            injection hRest₄ with hW hRest₅
            injection hRest₅ with hH hRest₆
            injection hRest₆ with hC hRest₇
            injection hRest₇ with hP hRest₈
            injection hRest₈ with hN _
            cases hM
            cases hS
            cases hG
            cases hR
            cases hW
            cases hH
            cases hC
            cases hP
            cases hN
            rfl

instance realityConstrainedSignatureResidueNontrivial :
    Nontrivial RealityConstrainedSignatureResidueUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealityConstrainedSignatureResidueUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealityConstrainedSignatureResidueUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealityConstrainedSignatureResidueUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realityConstrainedSignatureResidueChapterTasteGate

theorem RealityConstrainedSignatureResidueTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      realityConstrainedSignatureResidueDecodeBHist
        (realityConstrainedSignatureResidueEncodeBHist h) = h) ∧
      (∀ M S G R W H C P N : BHist,
        realityConstrainedSignatureResidueToEventFlow
            (RealityConstrainedSignatureResidueUp.mk M S G R W H C P N) =
          [[BMark.b0],
            realityConstrainedSignatureResidueEncodeBHist M,
            [BMark.b1, BMark.b0],
            realityConstrainedSignatureResidueEncodeBHist S,
            [BMark.b1, BMark.b1, BMark.b0],
            realityConstrainedSignatureResidueEncodeBHist G,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
            realityConstrainedSignatureResidueEncodeBHist R,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
            realityConstrainedSignatureResidueEncodeBHist W,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
            realityConstrainedSignatureResidueEncodeBHist H,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
            realityConstrainedSignatureResidueEncodeBHist C,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b0],
            realityConstrainedSignatureResidueEncodeBHist P,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b1, BMark.b0],
            realityConstrainedSignatureResidueEncodeBHist N]) ∧
        (∀ M S G R W H C P N : BHist,
          realityConstrainedSignatureResidueFields
              (RealityConstrainedSignatureResidueUp.mk M S G R W H C P N) =
            [M, S, G, R, W, H, C, P, N]) ∧
          realityConstrainedSignatureResidueEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact realityConstrainedSignatureResidueDecode_encode_bhist
  · constructor
    · intro M S G R W H C P N
      rfl
    · constructor
      · intro M S G R W H C P N
        rfl
      · rfl

end BEDC.Derived.RealityConstrainedSignatureResidueUp
