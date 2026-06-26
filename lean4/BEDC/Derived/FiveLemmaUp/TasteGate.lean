import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiveLemmaUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiveLemmaUp : Type where
  | mk (A B C D E F G H I N : BHist) : FiveLemmaUp
  deriving DecidableEq

def fiveLemmaEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: fiveLemmaEncodeBHist h
  | BHist.e1 h => BMark.b1 :: fiveLemmaEncodeBHist h

def fiveLemmaDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (fiveLemmaDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (fiveLemmaDecodeBHist tail)

private theorem FiveLemmaUpTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist, fiveLemmaDecodeBHist (fiveLemmaEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def fiveLemmaFields : FiveLemmaUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiveLemmaUp.mk A B C D E F G H I N => [A, B, C, D, E, F, G, H, I, N]

def fiveLemmaToEventFlow : FiveLemmaUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (fiveLemmaFields x).map fiveLemmaEncodeBHist

private def fiveLemmaEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => fiveLemmaEventAtDefault index rest

def fiveLemmaFromEventFlow (ef : EventFlow) : Option FiveLemmaUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiveLemmaUp.mk
      (fiveLemmaDecodeBHist (fiveLemmaEventAtDefault 0 ef))
      (fiveLemmaDecodeBHist (fiveLemmaEventAtDefault 1 ef))
      (fiveLemmaDecodeBHist (fiveLemmaEventAtDefault 2 ef))
      (fiveLemmaDecodeBHist (fiveLemmaEventAtDefault 3 ef))
      (fiveLemmaDecodeBHist (fiveLemmaEventAtDefault 4 ef))
      (fiveLemmaDecodeBHist (fiveLemmaEventAtDefault 5 ef))
      (fiveLemmaDecodeBHist (fiveLemmaEventAtDefault 6 ef))
      (fiveLemmaDecodeBHist (fiveLemmaEventAtDefault 7 ef))
      (fiveLemmaDecodeBHist (fiveLemmaEventAtDefault 8 ef))
      (fiveLemmaDecodeBHist (fiveLemmaEventAtDefault 9 ef)))

private theorem FiveLemmaUpTasteGate_single_carrier_alignment_round_trip
    (x : FiveLemmaUp) :
    fiveLemmaFromEventFlow (fiveLemmaToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk A B C D E F G H I N =>
      change
        some
          (FiveLemmaUp.mk
            (fiveLemmaDecodeBHist (fiveLemmaEncodeBHist A))
            (fiveLemmaDecodeBHist (fiveLemmaEncodeBHist B))
            (fiveLemmaDecodeBHist (fiveLemmaEncodeBHist C))
            (fiveLemmaDecodeBHist (fiveLemmaEncodeBHist D))
            (fiveLemmaDecodeBHist (fiveLemmaEncodeBHist E))
            (fiveLemmaDecodeBHist (fiveLemmaEncodeBHist F))
            (fiveLemmaDecodeBHist (fiveLemmaEncodeBHist G))
            (fiveLemmaDecodeBHist (fiveLemmaEncodeBHist H))
            (fiveLemmaDecodeBHist (fiveLemmaEncodeBHist I))
            (fiveLemmaDecodeBHist (fiveLemmaEncodeBHist N))) =
          some (FiveLemmaUp.mk A B C D E F G H I N)
      rw [FiveLemmaUpTasteGate_single_carrier_alignment_decode_encode A,
        FiveLemmaUpTasteGate_single_carrier_alignment_decode_encode B,
        FiveLemmaUpTasteGate_single_carrier_alignment_decode_encode C,
        FiveLemmaUpTasteGate_single_carrier_alignment_decode_encode D,
        FiveLemmaUpTasteGate_single_carrier_alignment_decode_encode E,
        FiveLemmaUpTasteGate_single_carrier_alignment_decode_encode F,
        FiveLemmaUpTasteGate_single_carrier_alignment_decode_encode G,
        FiveLemmaUpTasteGate_single_carrier_alignment_decode_encode H,
        FiveLemmaUpTasteGate_single_carrier_alignment_decode_encode I,
        FiveLemmaUpTasteGate_single_carrier_alignment_decode_encode N]

private theorem FiveLemmaUpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FiveLemmaUp} :
    fiveLemmaToEventFlow x = fiveLemmaToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      fiveLemmaFromEventFlow (fiveLemmaToEventFlow x) =
        fiveLemmaFromEventFlow (fiveLemmaToEventFlow y) :=
    congrArg fiveLemmaFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (FiveLemmaUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (FiveLemmaUpTasteGate_single_carrier_alignment_round_trip y)))

instance fiveLemmaBHistCarrier : BHistCarrier FiveLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := fiveLemmaToEventFlow
  fromEventFlow := fiveLemmaFromEventFlow

instance fiveLemmaChapterTasteGate : ChapterTasteGate FiveLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change fiveLemmaFromEventFlow (fiveLemmaToEventFlow x) = some x
    exact FiveLemmaUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FiveLemmaUpTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def FiveLemmaUpTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate FiveLemmaUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fiveLemmaChapterTasteGate

theorem FiveLemmaUpTasteGate_single_carrier_alignment :
    ChapterTasteGate FiveLemmaUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact fiveLemmaChapterTasteGate

end BEDC.Derived.FiveLemmaUp
