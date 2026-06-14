import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopCompleteRealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopCompleteRealUp : Type where
  | mk (D W R E S F H C P N : BHist) : BishopCompleteRealUp
  deriving DecidableEq

def bishopCompleteRealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopCompleteRealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopCompleteRealEncodeBHist h

def bishopCompleteRealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopCompleteRealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopCompleteRealDecodeBHist tail)

private theorem BishopCompleteRealTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      bishopCompleteRealDecodeBHist (bishopCompleteRealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopCompleteRealFields : BishopCompleteRealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopCompleteRealUp.mk D W R E S F H C P N => [D, W, R, E, S, F, H, C, P, N]

def bishopCompleteRealToEventFlow : BishopCompleteRealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map bishopCompleteRealEncodeBHist (bishopCompleteRealFields x)

private def bishopCompleteRealEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopCompleteRealEventAt index rest

def bishopCompleteRealFromEventFlow : EventFlow → Option BishopCompleteRealUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (BishopCompleteRealUp.mk
          (bishopCompleteRealDecodeBHist (bishopCompleteRealEventAt 0 ef))
          (bishopCompleteRealDecodeBHist (bishopCompleteRealEventAt 1 ef))
          (bishopCompleteRealDecodeBHist (bishopCompleteRealEventAt 2 ef))
          (bishopCompleteRealDecodeBHist (bishopCompleteRealEventAt 3 ef))
          (bishopCompleteRealDecodeBHist (bishopCompleteRealEventAt 4 ef))
          (bishopCompleteRealDecodeBHist (bishopCompleteRealEventAt 5 ef))
          (bishopCompleteRealDecodeBHist (bishopCompleteRealEventAt 6 ef))
          (bishopCompleteRealDecodeBHist (bishopCompleteRealEventAt 7 ef))
          (bishopCompleteRealDecodeBHist (bishopCompleteRealEventAt 8 ef))
          (bishopCompleteRealDecodeBHist (bishopCompleteRealEventAt 9 ef)))

private theorem BishopCompleteRealTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BishopCompleteRealUp,
      bishopCompleteRealFromEventFlow (bishopCompleteRealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D W R E S F H C P N =>
      change
        some
          (BishopCompleteRealUp.mk
            (bishopCompleteRealDecodeBHist (bishopCompleteRealEncodeBHist D))
            (bishopCompleteRealDecodeBHist (bishopCompleteRealEncodeBHist W))
            (bishopCompleteRealDecodeBHist (bishopCompleteRealEncodeBHist R))
            (bishopCompleteRealDecodeBHist (bishopCompleteRealEncodeBHist E))
            (bishopCompleteRealDecodeBHist (bishopCompleteRealEncodeBHist S))
            (bishopCompleteRealDecodeBHist (bishopCompleteRealEncodeBHist F))
            (bishopCompleteRealDecodeBHist (bishopCompleteRealEncodeBHist H))
            (bishopCompleteRealDecodeBHist (bishopCompleteRealEncodeBHist C))
            (bishopCompleteRealDecodeBHist (bishopCompleteRealEncodeBHist P))
            (bishopCompleteRealDecodeBHist (bishopCompleteRealEncodeBHist N))) =
          some (BishopCompleteRealUp.mk D W R E S F H C P N)
      rw [BishopCompleteRealTasteGate_single_carrier_alignment_decode D,
        BishopCompleteRealTasteGate_single_carrier_alignment_decode W,
        BishopCompleteRealTasteGate_single_carrier_alignment_decode R,
        BishopCompleteRealTasteGate_single_carrier_alignment_decode E,
        BishopCompleteRealTasteGate_single_carrier_alignment_decode S,
        BishopCompleteRealTasteGate_single_carrier_alignment_decode F,
        BishopCompleteRealTasteGate_single_carrier_alignment_decode H,
        BishopCompleteRealTasteGate_single_carrier_alignment_decode C,
        BishopCompleteRealTasteGate_single_carrier_alignment_decode P,
        BishopCompleteRealTasteGate_single_carrier_alignment_decode N]

private theorem BishopCompleteRealTasteGate_single_carrier_alignment_injective
    {x y : BishopCompleteRealUp} :
    bishopCompleteRealToEventFlow x = bishopCompleteRealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopCompleteRealFromEventFlow (bishopCompleteRealToEventFlow x) =
        bishopCompleteRealFromEventFlow (bishopCompleteRealToEventFlow y) :=
    congrArg bishopCompleteRealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BishopCompleteRealTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BishopCompleteRealTasteGate_single_carrier_alignment_round_trip y)))

instance bishopCompleteRealBHistCarrier : BHistCarrier BishopCompleteRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopCompleteRealToEventFlow
  fromEventFlow := bishopCompleteRealFromEventFlow

instance bishopCompleteRealChapterTasteGate : ChapterTasteGate BishopCompleteRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopCompleteRealFromEventFlow (bishopCompleteRealToEventFlow x) = some x
    exact BishopCompleteRealTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BishopCompleteRealTasteGate_single_carrier_alignment_injective heq)

theorem BishopCompleteRealTasteGate_single_carrier_alignment :
    (∀ h : BHist, bishopCompleteRealDecodeBHist (bishopCompleteRealEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier BishopCompleteRealUp) ∧
        Nonempty (ChapterTasteGate BishopCompleteRealUp) ∧
          bishopCompleteRealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact BishopCompleteRealTasteGate_single_carrier_alignment_decode
  · constructor
    · exact ⟨bishopCompleteRealBHistCarrier⟩
    · constructor
      · exact ⟨bishopCompleteRealChapterTasteGate⟩
      · rfl

end BEDC.Derived.BishopCompleteRealUp
