import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TotalBoundednessModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TotalBoundednessModulusUp : Type where
  | mk (M N D R E H C P L : BHist) : TotalBoundednessModulusUp
  deriving DecidableEq

def totalBoundednessModulusFields : TotalBoundednessModulusUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TotalBoundednessModulusUp.mk M N D R E H C P L =>
      [M, N, D, R, E, H, C, P, L]

def totalBoundednessModulusEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: totalBoundednessModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: totalBoundednessModulusEncodeBHist h

def totalBoundednessModulusDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (totalBoundednessModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (totalBoundednessModulusDecodeBHist tail)

theorem TotalBoundednessModulusTasteGate_single_carrier_alignment_decode_encode_bhist :
    forall h : BHist, totalBoundednessModulusDecodeBHist (totalBoundednessModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

theorem TotalBoundednessModulusTasteGate_single_carrier_alignment_mk_congr
    {M1 M2 N1 N2 D1 D2 R1 R2 E1 E2 H1 H2 C1 C2 P1 P2 L1 L2 : BHist}
    (hM : M1 = M2) (hN : N1 = N2) (hD : D1 = D2) (hR : R1 = R2)
    (hE : E1 = E2) (hH : H1 = H2) (hC : C1 = C2) (hP : P1 = P2)
    (hL : L1 = L2) :
    TotalBoundednessModulusUp.mk M1 N1 D1 R1 E1 H1 C1 P1 L1 =
      TotalBoundednessModulusUp.mk M2 N2 D2 R2 E2 H2 C2 P2 L2 := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hM
  cases hN
  cases hD
  cases hR
  cases hE
  cases hH
  cases hC
  cases hP
  cases hL
  rfl

def totalBoundednessModulusToEventFlow : TotalBoundednessModulusUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | TotalBoundednessModulusUp.mk M N D R E H C P L =>
      [totalBoundednessModulusEncodeBHist M, totalBoundednessModulusEncodeBHist N,
        totalBoundednessModulusEncodeBHist D, totalBoundednessModulusEncodeBHist R,
        totalBoundednessModulusEncodeBHist E, totalBoundednessModulusEncodeBHist H,
        totalBoundednessModulusEncodeBHist C, totalBoundednessModulusEncodeBHist P,
        totalBoundednessModulusEncodeBHist L]

private def totalBoundednessModulusEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => totalBoundednessModulusEventAtDefault index rest

def totalBoundednessModulusFromEventFlow (ef : EventFlow) : Option TotalBoundednessModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (TotalBoundednessModulusUp.mk
      (totalBoundednessModulusDecodeBHist (totalBoundednessModulusEventAtDefault 0 ef))
      (totalBoundednessModulusDecodeBHist (totalBoundednessModulusEventAtDefault 1 ef))
      (totalBoundednessModulusDecodeBHist (totalBoundednessModulusEventAtDefault 2 ef))
      (totalBoundednessModulusDecodeBHist (totalBoundednessModulusEventAtDefault 3 ef))
      (totalBoundednessModulusDecodeBHist (totalBoundednessModulusEventAtDefault 4 ef))
      (totalBoundednessModulusDecodeBHist (totalBoundednessModulusEventAtDefault 5 ef))
      (totalBoundednessModulusDecodeBHist (totalBoundednessModulusEventAtDefault 6 ef))
      (totalBoundednessModulusDecodeBHist (totalBoundednessModulusEventAtDefault 7 ef))
      (totalBoundednessModulusDecodeBHist (totalBoundednessModulusEventAtDefault 8 ef)))

theorem TotalBoundednessModulusTasteGate_single_carrier_alignment_round_trip :
    forall x : TotalBoundednessModulusUp,
      totalBoundednessModulusFromEventFlow (totalBoundednessModulusToEventFlow x) = some x
  -- BEDC touchpoint anchor: BHist BMark
  | TotalBoundednessModulusUp.mk M N D R E H C P L =>
      congrArg some
        (TotalBoundednessModulusTasteGate_single_carrier_alignment_mk_congr
          (TotalBoundednessModulusTasteGate_single_carrier_alignment_decode_encode_bhist M)
          (TotalBoundednessModulusTasteGate_single_carrier_alignment_decode_encode_bhist N)
          (TotalBoundednessModulusTasteGate_single_carrier_alignment_decode_encode_bhist D)
          (TotalBoundednessModulusTasteGate_single_carrier_alignment_decode_encode_bhist R)
          (TotalBoundednessModulusTasteGate_single_carrier_alignment_decode_encode_bhist E)
          (TotalBoundednessModulusTasteGate_single_carrier_alignment_decode_encode_bhist H)
          (TotalBoundednessModulusTasteGate_single_carrier_alignment_decode_encode_bhist C)
          (TotalBoundednessModulusTasteGate_single_carrier_alignment_decode_encode_bhist P)
          (TotalBoundednessModulusTasteGate_single_carrier_alignment_decode_encode_bhist L))

theorem TotalBoundednessModulusTasteGate_single_carrier_alignment_toEventFlow_injective {x y : TotalBoundednessModulusUp} :
    totalBoundednessModulusToEventFlow x = totalBoundednessModulusToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      totalBoundednessModulusFromEventFlow (totalBoundednessModulusToEventFlow x) =
        totalBoundednessModulusFromEventFlow (totalBoundednessModulusToEventFlow y) :=
    congrArg totalBoundednessModulusFromEventFlow heq
  have hsome : some x = some y :=
    Eq.trans (TotalBoundednessModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (TotalBoundednessModulusTasteGate_single_carrier_alignment_round_trip y))
  cases hsome
  rfl

instance totalBoundednessModulusBHistCarrier : BHistCarrier TotalBoundednessModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := totalBoundednessModulusToEventFlow
  fromEventFlow := totalBoundednessModulusFromEventFlow

instance totalBoundednessModulusChapterTasteGate : ChapterTasteGate TotalBoundednessModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change totalBoundednessModulusFromEventFlow (totalBoundednessModulusToEventFlow x) = some x
    exact TotalBoundednessModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (TotalBoundednessModulusTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate TotalBoundednessModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  totalBoundednessModulusChapterTasteGate

theorem TotalBoundednessModulusTasteGate_single_carrier_alignment :
    (forall h : BHist, totalBoundednessModulusDecodeBHist (totalBoundednessModulusEncodeBHist h) = h) ∧
      (forall x : TotalBoundednessModulusUp,
        totalBoundednessModulusFromEventFlow (totalBoundednessModulusToEventFlow x) = some x) ∧
      (forall x y : TotalBoundednessModulusUp,
        totalBoundednessModulusToEventFlow x = totalBoundednessModulusToEventFlow y -> x = y) ∧
      totalBoundednessModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact TotalBoundednessModulusTasteGate_single_carrier_alignment_decode_encode_bhist
  · constructor
    · exact TotalBoundednessModulusTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact TotalBoundednessModulusTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · rfl

end BEDC.Derived.TotalBoundednessModulusUp
