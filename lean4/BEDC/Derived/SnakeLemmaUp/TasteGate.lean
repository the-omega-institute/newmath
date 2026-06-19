import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SnakeLemmaUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SnakeLemmaUp : Type where
  | mk (A R0 R1 V K C E boundary H T P L : BHist) : SnakeLemmaUp
  deriving DecidableEq

def snakeLemmaEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: snakeLemmaEncodeBHist h
  | BHist.e1 h => BMark.b1 :: snakeLemmaEncodeBHist h

def snakeLemmaDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (snakeLemmaDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (snakeLemmaDecodeBHist tail)

private theorem snakeLemma_decode_encode_bhist :
    ∀ h : BHist, snakeLemmaDecodeBHist (snakeLemmaEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def snakeLemmaToEventFlow : SnakeLemmaUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SnakeLemmaUp.mk A R0 R1 V K C E boundary H T P L =>
      [snakeLemmaEncodeBHist A,
        snakeLemmaEncodeBHist R0,
        snakeLemmaEncodeBHist R1,
        snakeLemmaEncodeBHist V,
        snakeLemmaEncodeBHist K,
        snakeLemmaEncodeBHist C,
        snakeLemmaEncodeBHist E,
        snakeLemmaEncodeBHist boundary,
        snakeLemmaEncodeBHist H,
        snakeLemmaEncodeBHist T,
        snakeLemmaEncodeBHist P,
        snakeLemmaEncodeBHist L]

private def snakeLemmaEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => snakeLemmaEventAt index rest

def snakeLemmaFromEventFlow : EventFlow → Option SnakeLemmaUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (SnakeLemmaUp.mk
        (snakeLemmaDecodeBHist (snakeLemmaEventAt 0 ef))
        (snakeLemmaDecodeBHist (snakeLemmaEventAt 1 ef))
        (snakeLemmaDecodeBHist (snakeLemmaEventAt 2 ef))
        (snakeLemmaDecodeBHist (snakeLemmaEventAt 3 ef))
        (snakeLemmaDecodeBHist (snakeLemmaEventAt 4 ef))
        (snakeLemmaDecodeBHist (snakeLemmaEventAt 5 ef))
        (snakeLemmaDecodeBHist (snakeLemmaEventAt 6 ef))
        (snakeLemmaDecodeBHist (snakeLemmaEventAt 7 ef))
        (snakeLemmaDecodeBHist (snakeLemmaEventAt 8 ef))
        (snakeLemmaDecodeBHist (snakeLemmaEventAt 9 ef))
        (snakeLemmaDecodeBHist (snakeLemmaEventAt 10 ef))
        (snakeLemmaDecodeBHist (snakeLemmaEventAt 11 ef)))

private theorem snakeLemma_round_trip :
    ∀ x : SnakeLemmaUp,
      snakeLemmaFromEventFlow (snakeLemmaToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A R0 R1 V K C E boundary H T P L =>
      change
        some
            (SnakeLemmaUp.mk
              (snakeLemmaDecodeBHist (snakeLemmaEncodeBHist A))
              (snakeLemmaDecodeBHist (snakeLemmaEncodeBHist R0))
              (snakeLemmaDecodeBHist (snakeLemmaEncodeBHist R1))
              (snakeLemmaDecodeBHist (snakeLemmaEncodeBHist V))
              (snakeLemmaDecodeBHist (snakeLemmaEncodeBHist K))
              (snakeLemmaDecodeBHist (snakeLemmaEncodeBHist C))
              (snakeLemmaDecodeBHist (snakeLemmaEncodeBHist E))
              (snakeLemmaDecodeBHist (snakeLemmaEncodeBHist boundary))
              (snakeLemmaDecodeBHist (snakeLemmaEncodeBHist H))
              (snakeLemmaDecodeBHist (snakeLemmaEncodeBHist T))
              (snakeLemmaDecodeBHist (snakeLemmaEncodeBHist P))
              (snakeLemmaDecodeBHist (snakeLemmaEncodeBHist L))) =
          some (SnakeLemmaUp.mk A R0 R1 V K C E boundary H T P L)
      rw [snakeLemma_decode_encode_bhist A,
        snakeLemma_decode_encode_bhist R0,
        snakeLemma_decode_encode_bhist R1,
        snakeLemma_decode_encode_bhist V,
        snakeLemma_decode_encode_bhist K,
        snakeLemma_decode_encode_bhist C,
        snakeLemma_decode_encode_bhist E,
        snakeLemma_decode_encode_bhist boundary,
        snakeLemma_decode_encode_bhist H,
        snakeLemma_decode_encode_bhist T,
        snakeLemma_decode_encode_bhist P,
        snakeLemma_decode_encode_bhist L]

private theorem snakeLemmaToEventFlow_injective {x y : SnakeLemmaUp} :
    snakeLemmaToEventFlow x = snakeLemmaToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      snakeLemmaFromEventFlow (snakeLemmaToEventFlow x) =
        snakeLemmaFromEventFlow (snakeLemmaToEventFlow y) :=
    congrArg snakeLemmaFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (snakeLemma_round_trip x).symm
      (Eq.trans hread (snakeLemma_round_trip y)))

instance snakeLemmaBHistCarrier : BHistCarrier SnakeLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := snakeLemmaToEventFlow
  fromEventFlow := snakeLemmaFromEventFlow

instance snakeLemmaChapterTasteGate : ChapterTasteGate SnakeLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change snakeLemmaFromEventFlow (snakeLemmaToEventFlow x) = some x
    exact snakeLemma_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (snakeLemmaToEventFlow_injective heq)

theorem SnakeLemmaTasteGate_single_carrier_alignment :
    (∀ h : BHist, snakeLemmaDecodeBHist (snakeLemmaEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier SnakeLemmaUp) ∧
        Nonempty (ChapterTasteGate SnakeLemmaUp) ∧
          snakeLemmaEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨snakeLemma_decode_encode_bhist,
      ⟨snakeLemmaBHistCarrier⟩,
      ⟨snakeLemmaChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.SnakeLemmaUp.TasteGate
