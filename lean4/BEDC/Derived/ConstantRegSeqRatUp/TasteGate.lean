import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ConstantRegSeqRatUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ConstantRegSeqRatUp : Type where
  | mk (D S R H K P N : BHist) : ConstantRegSeqRatUp
  deriving DecidableEq

def constantRegSeqRatFields : ConstantRegSeqRatUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ConstantRegSeqRatUp.mk D S R H K P N => [D, S, R, H, K, P, N]

def constantRegSeqRatEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: constantRegSeqRatEncodeBHist h
  | BHist.e1 h => BMark.b1 :: constantRegSeqRatEncodeBHist h

def constantRegSeqRatDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (constantRegSeqRatDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (constantRegSeqRatDecodeBHist tail)

theorem ConstantRegSeqRatTasteGate_single_carrier_alignment_decode_encode_bhist :
    forall h : BHist, constantRegSeqRatDecodeBHist (constantRegSeqRatEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

theorem ConstantRegSeqRatTasteGate_single_carrier_alignment_mk_congr
    {D1 D2 S1 S2 R1 R2 H1 H2 K1 K2 P1 P2 N1 N2 : BHist}
    (hD : D1 = D2) (hS : S1 = S2) (hR : R1 = R2) (hH : H1 = H2)
    (hK : K1 = K2) (hP : P1 = P2) (hN : N1 = N2) :
    ConstantRegSeqRatUp.mk D1 S1 R1 H1 K1 P1 N1 =
      ConstantRegSeqRatUp.mk D2 S2 R2 H2 K2 P2 N2 := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hD
  cases hS
  cases hR
  cases hH
  cases hK
  cases hP
  cases hN
  rfl

def constantRegSeqRatToEventFlow : ConstantRegSeqRatUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ConstantRegSeqRatUp.mk D S R H K P N =>
      [constantRegSeqRatEncodeBHist D, constantRegSeqRatEncodeBHist S,
        constantRegSeqRatEncodeBHist R, constantRegSeqRatEncodeBHist H,
        constantRegSeqRatEncodeBHist K, constantRegSeqRatEncodeBHist P,
        constantRegSeqRatEncodeBHist N]

private def constantRegSeqRatEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => constantRegSeqRatEventAtDefault index rest

def constantRegSeqRatFromEventFlow (ef : EventFlow) : Option ConstantRegSeqRatUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ConstantRegSeqRatUp.mk
      (constantRegSeqRatDecodeBHist (constantRegSeqRatEventAtDefault 0 ef))
      (constantRegSeqRatDecodeBHist (constantRegSeqRatEventAtDefault 1 ef))
      (constantRegSeqRatDecodeBHist (constantRegSeqRatEventAtDefault 2 ef))
      (constantRegSeqRatDecodeBHist (constantRegSeqRatEventAtDefault 3 ef))
      (constantRegSeqRatDecodeBHist (constantRegSeqRatEventAtDefault 4 ef))
      (constantRegSeqRatDecodeBHist (constantRegSeqRatEventAtDefault 5 ef))
      (constantRegSeqRatDecodeBHist (constantRegSeqRatEventAtDefault 6 ef)))

theorem ConstantRegSeqRatTasteGate_single_carrier_alignment_round_trip :
    forall x : ConstantRegSeqRatUp,
      constantRegSeqRatFromEventFlow (constantRegSeqRatToEventFlow x) = some x
  -- BEDC touchpoint anchor: BHist BMark
  | ConstantRegSeqRatUp.mk D S R H K P N =>
      congrArg some
        (ConstantRegSeqRatTasteGate_single_carrier_alignment_mk_congr
          (ConstantRegSeqRatTasteGate_single_carrier_alignment_decode_encode_bhist D)
          (ConstantRegSeqRatTasteGate_single_carrier_alignment_decode_encode_bhist S)
          (ConstantRegSeqRatTasteGate_single_carrier_alignment_decode_encode_bhist R)
          (ConstantRegSeqRatTasteGate_single_carrier_alignment_decode_encode_bhist H)
          (ConstantRegSeqRatTasteGate_single_carrier_alignment_decode_encode_bhist K)
          (ConstantRegSeqRatTasteGate_single_carrier_alignment_decode_encode_bhist P)
          (ConstantRegSeqRatTasteGate_single_carrier_alignment_decode_encode_bhist N))

theorem ConstantRegSeqRatTasteGate_single_carrier_alignment_toEventFlow_injective {x y : ConstantRegSeqRatUp} :
    constantRegSeqRatToEventFlow x = constantRegSeqRatToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      constantRegSeqRatFromEventFlow (constantRegSeqRatToEventFlow x) =
        constantRegSeqRatFromEventFlow (constantRegSeqRatToEventFlow y) :=
    congrArg constantRegSeqRatFromEventFlow heq
  have hsome : some x = some y :=
    Eq.trans (ConstantRegSeqRatTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ConstantRegSeqRatTasteGate_single_carrier_alignment_round_trip y))
  cases hsome
  rfl

instance constantRegSeqRatBHistCarrier : BHistCarrier ConstantRegSeqRatUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := constantRegSeqRatToEventFlow
  fromEventFlow := constantRegSeqRatFromEventFlow

instance constantRegSeqRatChapterTasteGate : ChapterTasteGate ConstantRegSeqRatUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change constantRegSeqRatFromEventFlow (constantRegSeqRatToEventFlow x) = some x
    exact ConstantRegSeqRatTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ConstantRegSeqRatTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate ConstantRegSeqRatUp :=
  -- BEDC touchpoint anchor: BHist BMark
  constantRegSeqRatChapterTasteGate

theorem ConstantRegSeqRatTasteGate_single_carrier_alignment :
    (forall h : BHist, constantRegSeqRatDecodeBHist (constantRegSeqRatEncodeBHist h) = h) ∧
      (forall x : ConstantRegSeqRatUp,
        constantRegSeqRatFromEventFlow (constantRegSeqRatToEventFlow x) = some x) ∧
      (forall x y : ConstantRegSeqRatUp,
        constantRegSeqRatToEventFlow x = constantRegSeqRatToEventFlow y -> x = y) ∧
      constantRegSeqRatEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ConstantRegSeqRatTasteGate_single_carrier_alignment_decode_encode_bhist
  · constructor
    · exact ConstantRegSeqRatTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact ConstantRegSeqRatTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · rfl

end BEDC.Derived.ConstantRegSeqRatUp
