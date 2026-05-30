import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GroebnerBasisUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive GroebnerBasisUp : Type where
  | mk (P I O L S R F H C K N : BHist) : GroebnerBasisUp
  deriving DecidableEq

def GroebnerBasisTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: GroebnerBasisTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: GroebnerBasisTasteGate_single_carrier_alignment_encodeBHist h

def GroebnerBasisTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (GroebnerBasisTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (GroebnerBasisTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem GroebnerBasisTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      GroebnerBasisTasteGate_single_carrier_alignment_decodeBHist
          (GroebnerBasisTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem GroebnerBasisTasteGate_single_carrier_alignment_mk_congr
    {P P' I I' O O' L L' S S' R R' F F' H H' C C' K K' N N' : BHist}
    (hP : P' = P) (hI : I' = I) (hO : O' = O) (hL : L' = L) (hS : S' = S)
    (hR : R' = R) (hF : F' = F) (hH : H' = H) (hC : C' = C) (hK : K' = K)
    (hN : N' = N) :
    GroebnerBasisUp.mk P' I' O' L' S' R' F' H' C' K' N' =
      GroebnerBasisUp.mk P I O L S R F H C K N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hP
  cases hI
  cases hO
  cases hL
  cases hS
  cases hR
  cases hF
  cases hH
  cases hC
  cases hK
  cases hN
  rfl

def GroebnerBasisTasteGate_single_carrier_alignment_fields :
    GroebnerBasisUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | GroebnerBasisUp.mk P I O L S R F H C K N => [P, I, O, L, S, R, F, H, C, K, N]

def GroebnerBasisTasteGate_single_carrier_alignment_toEventFlow :
    GroebnerBasisUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (GroebnerBasisTasteGate_single_carrier_alignment_fields x).map
      GroebnerBasisTasteGate_single_carrier_alignment_encodeBHist

def GroebnerBasisTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option GroebnerBasisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | P :: I :: O :: L :: S :: R :: F :: H :: C :: K :: N :: [] =>
      some
        (GroebnerBasisUp.mk
          (GroebnerBasisTasteGate_single_carrier_alignment_decodeBHist P)
          (GroebnerBasisTasteGate_single_carrier_alignment_decodeBHist I)
          (GroebnerBasisTasteGate_single_carrier_alignment_decodeBHist O)
          (GroebnerBasisTasteGate_single_carrier_alignment_decodeBHist L)
          (GroebnerBasisTasteGate_single_carrier_alignment_decodeBHist S)
          (GroebnerBasisTasteGate_single_carrier_alignment_decodeBHist R)
          (GroebnerBasisTasteGate_single_carrier_alignment_decodeBHist F)
          (GroebnerBasisTasteGate_single_carrier_alignment_decodeBHist H)
          (GroebnerBasisTasteGate_single_carrier_alignment_decodeBHist C)
          (GroebnerBasisTasteGate_single_carrier_alignment_decodeBHist K)
          (GroebnerBasisTasteGate_single_carrier_alignment_decodeBHist N))
  | _ => none

private theorem GroebnerBasisTasteGate_single_carrier_alignment_round_trip :
    ∀ x : GroebnerBasisUp,
      GroebnerBasisTasteGate_single_carrier_alignment_fromEventFlow
          (GroebnerBasisTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk P I O L S R F H C K N =>
      change
        some
            (GroebnerBasisUp.mk
              (GroebnerBasisTasteGate_single_carrier_alignment_decodeBHist
                (GroebnerBasisTasteGate_single_carrier_alignment_encodeBHist P))
              (GroebnerBasisTasteGate_single_carrier_alignment_decodeBHist
                (GroebnerBasisTasteGate_single_carrier_alignment_encodeBHist I))
              (GroebnerBasisTasteGate_single_carrier_alignment_decodeBHist
                (GroebnerBasisTasteGate_single_carrier_alignment_encodeBHist O))
              (GroebnerBasisTasteGate_single_carrier_alignment_decodeBHist
                (GroebnerBasisTasteGate_single_carrier_alignment_encodeBHist L))
              (GroebnerBasisTasteGate_single_carrier_alignment_decodeBHist
                (GroebnerBasisTasteGate_single_carrier_alignment_encodeBHist S))
              (GroebnerBasisTasteGate_single_carrier_alignment_decodeBHist
                (GroebnerBasisTasteGate_single_carrier_alignment_encodeBHist R))
              (GroebnerBasisTasteGate_single_carrier_alignment_decodeBHist
                (GroebnerBasisTasteGate_single_carrier_alignment_encodeBHist F))
              (GroebnerBasisTasteGate_single_carrier_alignment_decodeBHist
                (GroebnerBasisTasteGate_single_carrier_alignment_encodeBHist H))
              (GroebnerBasisTasteGate_single_carrier_alignment_decodeBHist
                (GroebnerBasisTasteGate_single_carrier_alignment_encodeBHist C))
              (GroebnerBasisTasteGate_single_carrier_alignment_decodeBHist
                (GroebnerBasisTasteGate_single_carrier_alignment_encodeBHist K))
              (GroebnerBasisTasteGate_single_carrier_alignment_decodeBHist
                (GroebnerBasisTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (GroebnerBasisUp.mk P I O L S R F H C K N)
      exact
        congrArg some
          (GroebnerBasisTasteGate_single_carrier_alignment_mk_congr
            (GroebnerBasisTasteGate_single_carrier_alignment_decode_encode P)
            (GroebnerBasisTasteGate_single_carrier_alignment_decode_encode I)
            (GroebnerBasisTasteGate_single_carrier_alignment_decode_encode O)
            (GroebnerBasisTasteGate_single_carrier_alignment_decode_encode L)
            (GroebnerBasisTasteGate_single_carrier_alignment_decode_encode S)
            (GroebnerBasisTasteGate_single_carrier_alignment_decode_encode R)
            (GroebnerBasisTasteGate_single_carrier_alignment_decode_encode F)
            (GroebnerBasisTasteGate_single_carrier_alignment_decode_encode H)
            (GroebnerBasisTasteGate_single_carrier_alignment_decode_encode C)
            (GroebnerBasisTasteGate_single_carrier_alignment_decode_encode K)
            (GroebnerBasisTasteGate_single_carrier_alignment_decode_encode N))

private theorem GroebnerBasisTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : GroebnerBasisUp} :
    GroebnerBasisTasteGate_single_carrier_alignment_toEventFlow x =
        GroebnerBasisTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          GroebnerBasisTasteGate_single_carrier_alignment_fromEventFlow
            (GroebnerBasisTasteGate_single_carrier_alignment_toEventFlow x) :=
        (GroebnerBasisTasteGate_single_carrier_alignment_round_trip x).symm
      _ =
          GroebnerBasisTasteGate_single_carrier_alignment_fromEventFlow
            (GroebnerBasisTasteGate_single_carrier_alignment_toEventFlow y) :=
        congrArg GroebnerBasisTasteGate_single_carrier_alignment_fromEventFlow hxy
      _ = some y := GroebnerBasisTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

instance groebnerBasisBHistCarrier : BHistCarrier GroebnerBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := GroebnerBasisTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := GroebnerBasisTasteGate_single_carrier_alignment_fromEventFlow

instance groebnerBasisChapterTasteGate : ChapterTasteGate GroebnerBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      GroebnerBasisTasteGate_single_carrier_alignment_fromEventFlow
          (GroebnerBasisTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact GroebnerBasisTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (GroebnerBasisTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem GroebnerBasisTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      GroebnerBasisTasteGate_single_carrier_alignment_decodeBHist
          (GroebnerBasisTasteGate_single_carrier_alignment_encodeBHist h) =
        h) ∧
      GroebnerBasisTasteGate_single_carrier_alignment_fields
          (GroebnerBasisUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact GroebnerBasisTasteGate_single_carrier_alignment_decode_encode
  · rfl

end BEDC.Derived.GroebnerBasisUp
