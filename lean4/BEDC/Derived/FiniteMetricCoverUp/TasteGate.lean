import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteMetricCoverUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteMetricCoverUp : Type where
  | mk (M K T B R G H C P N : BHist) : FiniteMetricCoverUp
  deriving DecidableEq

def finiteMetricCoverFields : FiniteMetricCoverUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteMetricCoverUp.mk M K T B R G H C P N => [M, K, T, B, R, G, H, C, P, N]

def finiteMetricCoverEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteMetricCoverEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteMetricCoverEncodeBHist h

def finiteMetricCoverDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteMetricCoverDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteMetricCoverDecodeBHist tail)

theorem FiniteMetricCoverTasteGate_single_carrier_alignment_decode_encode_bhist :
    forall h : BHist, finiteMetricCoverDecodeBHist (finiteMetricCoverEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

theorem FiniteMetricCoverTasteGate_single_carrier_alignment_mk_congr
    {M1 M2 K1 K2 T1 T2 B1 B2 R1 R2 G1 G2 H1 H2 C1 C2 P1 P2 N1 N2 : BHist}
    (hM : M1 = M2) (hK : K1 = K2) (hT : T1 = T2) (hB : B1 = B2)
    (hR : R1 = R2) (hG : G1 = G2) (hH : H1 = H2) (hC : C1 = C2)
    (hP : P1 = P2) (hN : N1 = N2) :
    FiniteMetricCoverUp.mk M1 K1 T1 B1 R1 G1 H1 C1 P1 N1 =
      FiniteMetricCoverUp.mk M2 K2 T2 B2 R2 G2 H2 C2 P2 N2 := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hM
  cases hK
  cases hT
  cases hB
  cases hR
  cases hG
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def finiteMetricCoverToEventFlow : FiniteMetricCoverUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteMetricCoverUp.mk M K T B R G H C P N =>
      [finiteMetricCoverEncodeBHist M, finiteMetricCoverEncodeBHist K,
        finiteMetricCoverEncodeBHist T, finiteMetricCoverEncodeBHist B,
        finiteMetricCoverEncodeBHist R, finiteMetricCoverEncodeBHist G,
        finiteMetricCoverEncodeBHist H, finiteMetricCoverEncodeBHist C,
        finiteMetricCoverEncodeBHist P, finiteMetricCoverEncodeBHist N]

private def finiteMetricCoverEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteMetricCoverEventAtDefault index rest

def finiteMetricCoverFromEventFlow (ef : EventFlow) : Option FiniteMetricCoverUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteMetricCoverUp.mk
      (finiteMetricCoverDecodeBHist (finiteMetricCoverEventAtDefault 0 ef))
      (finiteMetricCoverDecodeBHist (finiteMetricCoverEventAtDefault 1 ef))
      (finiteMetricCoverDecodeBHist (finiteMetricCoverEventAtDefault 2 ef))
      (finiteMetricCoverDecodeBHist (finiteMetricCoverEventAtDefault 3 ef))
      (finiteMetricCoverDecodeBHist (finiteMetricCoverEventAtDefault 4 ef))
      (finiteMetricCoverDecodeBHist (finiteMetricCoverEventAtDefault 5 ef))
      (finiteMetricCoverDecodeBHist (finiteMetricCoverEventAtDefault 6 ef))
      (finiteMetricCoverDecodeBHist (finiteMetricCoverEventAtDefault 7 ef))
      (finiteMetricCoverDecodeBHist (finiteMetricCoverEventAtDefault 8 ef))
      (finiteMetricCoverDecodeBHist (finiteMetricCoverEventAtDefault 9 ef)))

theorem FiniteMetricCoverTasteGate_single_carrier_alignment_round_trip :
    forall x : FiniteMetricCoverUp,
      finiteMetricCoverFromEventFlow (finiteMetricCoverToEventFlow x) = some x
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteMetricCoverUp.mk M K T B R G H C P N =>
      congrArg some
        (FiniteMetricCoverTasteGate_single_carrier_alignment_mk_congr
          (FiniteMetricCoverTasteGate_single_carrier_alignment_decode_encode_bhist M)
          (FiniteMetricCoverTasteGate_single_carrier_alignment_decode_encode_bhist K)
          (FiniteMetricCoverTasteGate_single_carrier_alignment_decode_encode_bhist T)
          (FiniteMetricCoverTasteGate_single_carrier_alignment_decode_encode_bhist B)
          (FiniteMetricCoverTasteGate_single_carrier_alignment_decode_encode_bhist R)
          (FiniteMetricCoverTasteGate_single_carrier_alignment_decode_encode_bhist G)
          (FiniteMetricCoverTasteGate_single_carrier_alignment_decode_encode_bhist H)
          (FiniteMetricCoverTasteGate_single_carrier_alignment_decode_encode_bhist C)
          (FiniteMetricCoverTasteGate_single_carrier_alignment_decode_encode_bhist P)
          (FiniteMetricCoverTasteGate_single_carrier_alignment_decode_encode_bhist N))

theorem FiniteMetricCoverTasteGate_single_carrier_alignment_toEventFlow_injective {x y : FiniteMetricCoverUp} :
    finiteMetricCoverToEventFlow x = finiteMetricCoverToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteMetricCoverFromEventFlow (finiteMetricCoverToEventFlow x) =
        finiteMetricCoverFromEventFlow (finiteMetricCoverToEventFlow y) :=
    congrArg finiteMetricCoverFromEventFlow heq
  have hsome : some x = some y :=
    Eq.trans (FiniteMetricCoverTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FiniteMetricCoverTasteGate_single_carrier_alignment_round_trip y))
  cases hsome
  rfl

instance finiteMetricCoverBHistCarrier : BHistCarrier FiniteMetricCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteMetricCoverToEventFlow
  fromEventFlow := finiteMetricCoverFromEventFlow

instance finiteMetricCoverChapterTasteGate : ChapterTasteGate FiniteMetricCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteMetricCoverFromEventFlow (finiteMetricCoverToEventFlow x) = some x
    exact FiniteMetricCoverTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FiniteMetricCoverTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate FiniteMetricCoverUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteMetricCoverChapterTasteGate

theorem FiniteMetricCoverTasteGate_single_carrier_alignment :
    (forall h : BHist, finiteMetricCoverDecodeBHist (finiteMetricCoverEncodeBHist h) = h) ∧
      (forall x : FiniteMetricCoverUp,
        finiteMetricCoverFromEventFlow (finiteMetricCoverToEventFlow x) = some x) ∧
      (forall x y : FiniteMetricCoverUp,
        finiteMetricCoverToEventFlow x = finiteMetricCoverToEventFlow y -> x = y) ∧
      finiteMetricCoverEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact FiniteMetricCoverTasteGate_single_carrier_alignment_decode_encode_bhist
  · constructor
    · exact FiniteMetricCoverTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact FiniteMetricCoverTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · rfl

end BEDC.Derived.FiniteMetricCoverUp
