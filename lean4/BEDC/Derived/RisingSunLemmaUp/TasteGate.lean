import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RisingSunLemmaUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RisingSunLemmaUp : Type where
  | mk (I F E M S T H C P N : BHist) : RisingSunLemmaUp
  deriving DecidableEq

def risingSunLemmaEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: risingSunLemmaEncodeBHist h
  | BHist.e1 h => BMark.b1 :: risingSunLemmaEncodeBHist h

def risingSunLemmaDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (risingSunLemmaDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (risingSunLemmaDecodeBHist tail)

private theorem RisingSunLemmaTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, risingSunLemmaDecodeBHist (risingSunLemmaEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def risingSunLemmaFields : RisingSunLemmaUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RisingSunLemmaUp.mk I F E M S T H C P N => [I, F, E, M, S, T, H, C, P, N]

def risingSunLemmaToEventFlow : RisingSunLemmaUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (risingSunLemmaFields x).map risingSunLemmaEncodeBHist

private def risingSunLemmaEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => risingSunLemmaEventAt index rest

def risingSunLemmaFromEventFlow : EventFlow → Option RisingSunLemmaUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (RisingSunLemmaUp.mk
          (risingSunLemmaDecodeBHist (risingSunLemmaEventAt 0 ef))
          (risingSunLemmaDecodeBHist (risingSunLemmaEventAt 1 ef))
          (risingSunLemmaDecodeBHist (risingSunLemmaEventAt 2 ef))
          (risingSunLemmaDecodeBHist (risingSunLemmaEventAt 3 ef))
          (risingSunLemmaDecodeBHist (risingSunLemmaEventAt 4 ef))
          (risingSunLemmaDecodeBHist (risingSunLemmaEventAt 5 ef))
          (risingSunLemmaDecodeBHist (risingSunLemmaEventAt 6 ef))
          (risingSunLemmaDecodeBHist (risingSunLemmaEventAt 7 ef))
          (risingSunLemmaDecodeBHist (risingSunLemmaEventAt 8 ef))
          (risingSunLemmaDecodeBHist (risingSunLemmaEventAt 9 ef)))

private theorem RisingSunLemmaTasteGate_single_carrier_alignment_round_trip
    (x : RisingSunLemmaUp) :
    risingSunLemmaFromEventFlow (risingSunLemmaToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I F E M S T H C P N =>
      change
        some
          (RisingSunLemmaUp.mk
            (risingSunLemmaDecodeBHist (risingSunLemmaEncodeBHist I))
            (risingSunLemmaDecodeBHist (risingSunLemmaEncodeBHist F))
            (risingSunLemmaDecodeBHist (risingSunLemmaEncodeBHist E))
            (risingSunLemmaDecodeBHist (risingSunLemmaEncodeBHist M))
            (risingSunLemmaDecodeBHist (risingSunLemmaEncodeBHist S))
            (risingSunLemmaDecodeBHist (risingSunLemmaEncodeBHist T))
            (risingSunLemmaDecodeBHist (risingSunLemmaEncodeBHist H))
            (risingSunLemmaDecodeBHist (risingSunLemmaEncodeBHist C))
            (risingSunLemmaDecodeBHist (risingSunLemmaEncodeBHist P))
            (risingSunLemmaDecodeBHist (risingSunLemmaEncodeBHist N))) =
          some (RisingSunLemmaUp.mk I F E M S T H C P N)
      rw [RisingSunLemmaTasteGate_single_carrier_alignment_decode_encode I,
        RisingSunLemmaTasteGate_single_carrier_alignment_decode_encode F,
        RisingSunLemmaTasteGate_single_carrier_alignment_decode_encode E,
        RisingSunLemmaTasteGate_single_carrier_alignment_decode_encode M,
        RisingSunLemmaTasteGate_single_carrier_alignment_decode_encode S,
        RisingSunLemmaTasteGate_single_carrier_alignment_decode_encode T,
        RisingSunLemmaTasteGate_single_carrier_alignment_decode_encode H,
        RisingSunLemmaTasteGate_single_carrier_alignment_decode_encode C,
        RisingSunLemmaTasteGate_single_carrier_alignment_decode_encode P,
        RisingSunLemmaTasteGate_single_carrier_alignment_decode_encode N]

private theorem RisingSunLemmaTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RisingSunLemmaUp} :
    risingSunLemmaToEventFlow x = risingSunLemmaToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      risingSunLemmaFromEventFlow (risingSunLemmaToEventFlow x) =
        risingSunLemmaFromEventFlow (risingSunLemmaToEventFlow y) :=
    congrArg risingSunLemmaFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RisingSunLemmaTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RisingSunLemmaTasteGate_single_carrier_alignment_round_trip y)))

instance risingSunLemmaBHistCarrier : BHistCarrier RisingSunLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := risingSunLemmaToEventFlow
  fromEventFlow := risingSunLemmaFromEventFlow

instance risingSunLemmaChapterTasteGate : ChapterTasteGate RisingSunLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change risingSunLemmaFromEventFlow (risingSunLemmaToEventFlow x) = some x
    exact RisingSunLemmaTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RisingSunLemmaTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem RisingSunLemmaTasteGate_single_carrier_alignment :
    (∀ h : BHist, risingSunLemmaDecodeBHist (risingSunLemmaEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RisingSunLemmaUp) ∧ Nonempty (ChapterTasteGate RisingSunLemmaUp) ∧
        risingSunLemmaEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RisingSunLemmaTasteGate_single_carrier_alignment_decode_encode,
      ⟨risingSunLemmaBHistCarrier⟩,
      ⟨risingSunLemmaChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.RisingSunLemmaUp
