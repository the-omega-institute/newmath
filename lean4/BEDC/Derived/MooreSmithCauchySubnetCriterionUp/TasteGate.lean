import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MooreSmithCauchySubnetCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MooreSmithCauchySubnetCriterionUp : Type where
  | mk (D M A W B N S G Y R H C P L : BHist) : MooreSmithCauchySubnetCriterionUp
  deriving DecidableEq

def mooreSmithCauchySubnetCriterionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: mooreSmithCauchySubnetCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: mooreSmithCauchySubnetCriterionEncodeBHist h

def mooreSmithCauchySubnetCriterionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (mooreSmithCauchySubnetCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (mooreSmithCauchySubnetCriterionDecodeBHist tail)

private theorem mooreSmithCauchySubnetCriterion_decode_encode_bhist :
    forall h : BHist,
      mooreSmithCauchySubnetCriterionDecodeBHist
          (mooreSmithCauchySubnetCriterionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem MooreSmithCauchySubnetCriterionTasteGate_single_carrier_alignment_mk_congr
    {D1 D2 M1 M2 A1 A2 W1 W2 B1 B2 N1 N2 S1 S2 G1 G2 Y1 Y2 R1 R2 H1 H2 C1 C2
      P1 P2 L1 L2 : BHist}
    (hD : D1 = D2) (hM : M1 = M2) (hA : A1 = A2) (hW : W1 = W2)
    (hB : B1 = B2) (hN : N1 = N2) (hS : S1 = S2) (hG : G1 = G2)
    (hY : Y1 = Y2) (hR : R1 = R2) (hH : H1 = H2) (hC : C1 = C2)
    (hP : P1 = P2) (hL : L1 = L2) :
    MooreSmithCauchySubnetCriterionUp.mk D1 M1 A1 W1 B1 N1 S1 G1 Y1 R1 H1 C1 P1 L1 =
      MooreSmithCauchySubnetCriterionUp.mk D2 M2 A2 W2 B2 N2 S2 G2 Y2 R2 H2 C2 P2
        L2 := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hD
  cases hM
  cases hA
  cases hW
  cases hB
  cases hN
  cases hS
  cases hG
  cases hY
  cases hR
  cases hH
  cases hC
  cases hP
  cases hL
  rfl

def mooreSmithCauchySubnetCriterionFields :
    MooreSmithCauchySubnetCriterionUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MooreSmithCauchySubnetCriterionUp.mk D M A W B N S G Y R H C P L =>
      [D, M, A, W, B, N, S, G, Y, R, H, C, P, L]

def mooreSmithCauchySubnetCriterionToEventFlow :
    MooreSmithCauchySubnetCriterionUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      List.map mooreSmithCauchySubnetCriterionEncodeBHist
        (mooreSmithCauchySubnetCriterionFields x)

def mooreSmithCauchySubnetCriterionFromEventFlow :
    EventFlow -> Option MooreSmithCauchySubnetCriterionUp
  -- BEDC touchpoint anchor: BHist BMark
  | D :: M :: A :: W :: B :: N :: S :: G :: Y :: R :: H :: C :: P :: L :: [] =>
      some
        (MooreSmithCauchySubnetCriterionUp.mk
          (mooreSmithCauchySubnetCriterionDecodeBHist D)
          (mooreSmithCauchySubnetCriterionDecodeBHist M)
          (mooreSmithCauchySubnetCriterionDecodeBHist A)
          (mooreSmithCauchySubnetCriterionDecodeBHist W)
          (mooreSmithCauchySubnetCriterionDecodeBHist B)
          (mooreSmithCauchySubnetCriterionDecodeBHist N)
          (mooreSmithCauchySubnetCriterionDecodeBHist S)
          (mooreSmithCauchySubnetCriterionDecodeBHist G)
          (mooreSmithCauchySubnetCriterionDecodeBHist Y)
          (mooreSmithCauchySubnetCriterionDecodeBHist R)
          (mooreSmithCauchySubnetCriterionDecodeBHist H)
          (mooreSmithCauchySubnetCriterionDecodeBHist C)
          (mooreSmithCauchySubnetCriterionDecodeBHist P)
          (mooreSmithCauchySubnetCriterionDecodeBHist L))
  | _ => none

private theorem mooreSmithCauchySubnetCriterion_round_trip :
    forall x : MooreSmithCauchySubnetCriterionUp,
      mooreSmithCauchySubnetCriterionFromEventFlow
          (mooreSmithCauchySubnetCriterionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D M A W B N S G Y R H C P L =>
      change
        some
          (MooreSmithCauchySubnetCriterionUp.mk
            (mooreSmithCauchySubnetCriterionDecodeBHist
              (mooreSmithCauchySubnetCriterionEncodeBHist D))
            (mooreSmithCauchySubnetCriterionDecodeBHist
              (mooreSmithCauchySubnetCriterionEncodeBHist M))
            (mooreSmithCauchySubnetCriterionDecodeBHist
              (mooreSmithCauchySubnetCriterionEncodeBHist A))
            (mooreSmithCauchySubnetCriterionDecodeBHist
              (mooreSmithCauchySubnetCriterionEncodeBHist W))
            (mooreSmithCauchySubnetCriterionDecodeBHist
              (mooreSmithCauchySubnetCriterionEncodeBHist B))
            (mooreSmithCauchySubnetCriterionDecodeBHist
              (mooreSmithCauchySubnetCriterionEncodeBHist N))
            (mooreSmithCauchySubnetCriterionDecodeBHist
              (mooreSmithCauchySubnetCriterionEncodeBHist S))
            (mooreSmithCauchySubnetCriterionDecodeBHist
              (mooreSmithCauchySubnetCriterionEncodeBHist G))
            (mooreSmithCauchySubnetCriterionDecodeBHist
              (mooreSmithCauchySubnetCriterionEncodeBHist Y))
            (mooreSmithCauchySubnetCriterionDecodeBHist
              (mooreSmithCauchySubnetCriterionEncodeBHist R))
            (mooreSmithCauchySubnetCriterionDecodeBHist
              (mooreSmithCauchySubnetCriterionEncodeBHist H))
            (mooreSmithCauchySubnetCriterionDecodeBHist
              (mooreSmithCauchySubnetCriterionEncodeBHist C))
            (mooreSmithCauchySubnetCriterionDecodeBHist
              (mooreSmithCauchySubnetCriterionEncodeBHist P))
            (mooreSmithCauchySubnetCriterionDecodeBHist
              (mooreSmithCauchySubnetCriterionEncodeBHist L))) =
          some (MooreSmithCauchySubnetCriterionUp.mk D M A W B N S G Y R H C P L)
      rw [mooreSmithCauchySubnetCriterion_decode_encode_bhist D]
      rw [mooreSmithCauchySubnetCriterion_decode_encode_bhist M]
      rw [mooreSmithCauchySubnetCriterion_decode_encode_bhist A]
      rw [mooreSmithCauchySubnetCriterion_decode_encode_bhist W]
      rw [mooreSmithCauchySubnetCriterion_decode_encode_bhist B]
      rw [mooreSmithCauchySubnetCriterion_decode_encode_bhist N]
      rw [mooreSmithCauchySubnetCriterion_decode_encode_bhist S]
      rw [mooreSmithCauchySubnetCriterion_decode_encode_bhist G]
      rw [mooreSmithCauchySubnetCriterion_decode_encode_bhist Y]
      rw [mooreSmithCauchySubnetCriterion_decode_encode_bhist R]
      rw [mooreSmithCauchySubnetCriterion_decode_encode_bhist H]
      rw [mooreSmithCauchySubnetCriterion_decode_encode_bhist C]
      rw [mooreSmithCauchySubnetCriterion_decode_encode_bhist P]
      rw [mooreSmithCauchySubnetCriterion_decode_encode_bhist L]

private theorem MooreSmithCauchySubnetCriterionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MooreSmithCauchySubnetCriterionUp} :
    mooreSmithCauchySubnetCriterionToEventFlow x =
        mooreSmithCauchySubnetCriterionToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      mooreSmithCauchySubnetCriterionFromEventFlow
          (mooreSmithCauchySubnetCriterionToEventFlow x) =
        mooreSmithCauchySubnetCriterionFromEventFlow
          (mooreSmithCauchySubnetCriterionToEventFlow y) :=
    congrArg mooreSmithCauchySubnetCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (mooreSmithCauchySubnetCriterion_round_trip x).symm
      (Eq.trans hread (mooreSmithCauchySubnetCriterion_round_trip y)))

def mooreSmithCauchySubnetCriterionBHistCarrierData :
    BHistCarrier MooreSmithCauchySubnetCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := mooreSmithCauchySubnetCriterionToEventFlow
  fromEventFlow := mooreSmithCauchySubnetCriterionFromEventFlow

instance mooreSmithCauchySubnetCriterionBHistCarrier :
    BHistCarrier MooreSmithCauchySubnetCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  mooreSmithCauchySubnetCriterionBHistCarrierData

def mooreSmithCauchySubnetCriterionChapterTasteGateData :
    @ChapterTasteGate MooreSmithCauchySubnetCriterionUp
      mooreSmithCauchySubnetCriterionBHistCarrierData where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      mooreSmithCauchySubnetCriterionFromEventFlow
          (mooreSmithCauchySubnetCriterionToEventFlow x) =
        some x
    exact mooreSmithCauchySubnetCriterion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (MooreSmithCauchySubnetCriterionTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

instance mooreSmithCauchySubnetCriterionChapterTasteGate :
    ChapterTasteGate MooreSmithCauchySubnetCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  mooreSmithCauchySubnetCriterionChapterTasteGateData

theorem MooreSmithCauchySubnetCriterionTasteGate_single_carrier_alignment :
    (forall h : BHist,
      mooreSmithCauchySubnetCriterionDecodeBHist
          (mooreSmithCauchySubnetCriterionEncodeBHist h) =
        h) ∧
      mooreSmithCauchySubnetCriterionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact ⟨mooreSmithCauchySubnetCriterion_decode_encode_bhist, rfl⟩

end BEDC.Derived.MooreSmithCauchySubnetCriterionUp
