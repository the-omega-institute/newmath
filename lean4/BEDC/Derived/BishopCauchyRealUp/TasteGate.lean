import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopCauchyRealUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopCauchyRealUp : Type where
  | mk (Q M S D R H C P N : BHist) : BishopCauchyRealUp
  deriving DecidableEq

def bishopCauchyRealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopCauchyRealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopCauchyRealEncodeBHist h

def bishopCauchyRealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopCauchyRealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopCauchyRealDecodeBHist tail)

private theorem BishopCauchyRealTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, bishopCauchyRealDecodeBHist (bishopCauchyRealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopCauchyRealFields : BishopCauchyRealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopCauchyRealUp.mk Q M S D R H C P N => [Q, M, S, D, R, H, C, P, N]

def bishopCauchyRealToEventFlow : BishopCauchyRealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bishopCauchyRealFields x).map bishopCauchyRealEncodeBHist

private def BishopCauchyRealTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      BishopCauchyRealTasteGate_single_carrier_alignment_eventAt index rest

def bishopCauchyRealDecodeFields (ef : EventFlow) : BishopCauchyRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  BishopCauchyRealUp.mk
    (bishopCauchyRealDecodeBHist
      (BishopCauchyRealTasteGate_single_carrier_alignment_eventAt 0 ef))
    (bishopCauchyRealDecodeBHist
      (BishopCauchyRealTasteGate_single_carrier_alignment_eventAt 1 ef))
    (bishopCauchyRealDecodeBHist
      (BishopCauchyRealTasteGate_single_carrier_alignment_eventAt 2 ef))
    (bishopCauchyRealDecodeBHist
      (BishopCauchyRealTasteGate_single_carrier_alignment_eventAt 3 ef))
    (bishopCauchyRealDecodeBHist
      (BishopCauchyRealTasteGate_single_carrier_alignment_eventAt 4 ef))
    (bishopCauchyRealDecodeBHist
      (BishopCauchyRealTasteGate_single_carrier_alignment_eventAt 5 ef))
    (bishopCauchyRealDecodeBHist
      (BishopCauchyRealTasteGate_single_carrier_alignment_eventAt 6 ef))
    (bishopCauchyRealDecodeBHist
      (BishopCauchyRealTasteGate_single_carrier_alignment_eventAt 7 ef))
    (bishopCauchyRealDecodeBHist
      (BishopCauchyRealTasteGate_single_carrier_alignment_eventAt 8 ef))

def bishopCauchyRealFromEventFlow (ef : EventFlow) : Option BishopCauchyRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some (bishopCauchyRealDecodeFields ef)

private theorem BishopCauchyRealTasteGate_single_carrier_alignment_round_trip
    (x : BishopCauchyRealUp) :
    bishopCauchyRealFromEventFlow (bishopCauchyRealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk Q M S D R H C P N =>
      change
        some
          (BishopCauchyRealUp.mk
            (bishopCauchyRealDecodeBHist (bishopCauchyRealEncodeBHist Q))
            (bishopCauchyRealDecodeBHist (bishopCauchyRealEncodeBHist M))
            (bishopCauchyRealDecodeBHist (bishopCauchyRealEncodeBHist S))
            (bishopCauchyRealDecodeBHist (bishopCauchyRealEncodeBHist D))
            (bishopCauchyRealDecodeBHist (bishopCauchyRealEncodeBHist R))
            (bishopCauchyRealDecodeBHist (bishopCauchyRealEncodeBHist H))
            (bishopCauchyRealDecodeBHist (bishopCauchyRealEncodeBHist C))
            (bishopCauchyRealDecodeBHist (bishopCauchyRealEncodeBHist P))
            (bishopCauchyRealDecodeBHist (bishopCauchyRealEncodeBHist N))) =
          some (BishopCauchyRealUp.mk Q M S D R H C P N)
      rw [BishopCauchyRealTasteGate_single_carrier_alignment_decode_encode Q,
        BishopCauchyRealTasteGate_single_carrier_alignment_decode_encode M,
        BishopCauchyRealTasteGate_single_carrier_alignment_decode_encode S,
        BishopCauchyRealTasteGate_single_carrier_alignment_decode_encode D,
        BishopCauchyRealTasteGate_single_carrier_alignment_decode_encode R,
        BishopCauchyRealTasteGate_single_carrier_alignment_decode_encode H,
        BishopCauchyRealTasteGate_single_carrier_alignment_decode_encode C,
        BishopCauchyRealTasteGate_single_carrier_alignment_decode_encode P,
        BishopCauchyRealTasteGate_single_carrier_alignment_decode_encode N]

private theorem BishopCauchyRealTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopCauchyRealUp} :
    bishopCauchyRealToEventFlow x = bishopCauchyRealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopCauchyRealFromEventFlow (bishopCauchyRealToEventFlow x) =
        bishopCauchyRealFromEventFlow (bishopCauchyRealToEventFlow y) :=
    congrArg bishopCauchyRealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BishopCauchyRealTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopCauchyRealTasteGate_single_carrier_alignment_round_trip y)))

instance bishopCauchyRealBHistCarrier : BHistCarrier BishopCauchyRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopCauchyRealToEventFlow
  fromEventFlow := bishopCauchyRealFromEventFlow

instance bishopCauchyRealChapterTasteGate : ChapterTasteGate BishopCauchyRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopCauchyRealFromEventFlow (bishopCauchyRealToEventFlow x) = some x
    exact BishopCauchyRealTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BishopCauchyRealTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def BishopCauchyRealTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate BishopCauchyRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopCauchyRealChapterTasteGate

theorem BishopCauchyRealTasteGate_single_carrier_alignment :
    (∀ h : BHist, bishopCauchyRealDecodeBHist (bishopCauchyRealEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier BishopCauchyRealUp) ∧
        Nonempty (ChapterTasteGate BishopCauchyRealUp) ∧
          bishopCauchyRealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨BishopCauchyRealTasteGate_single_carrier_alignment_decode_encode,
      ⟨bishopCauchyRealBHistCarrier⟩,
      ⟨bishopCauchyRealChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.BishopCauchyRealUp.TasteGate
