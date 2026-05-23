import BEDC.Derived.FastSeriesProductUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FastSeriesProductUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FastSeriesProductUp : Type where
  | mk (F G K W M T R E L C P N : BHist) : FastSeriesProductUp
  deriving DecidableEq

def fastSeriesProductEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: fastSeriesProductEncodeBHist h
  | BHist.e1 h => BMark.b1 :: fastSeriesProductEncodeBHist h

def fastSeriesProductDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (fastSeriesProductDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (fastSeriesProductDecodeBHist tail)

private theorem fastSeriesProduct_decode_encode :
    ∀ h : BHist, fastSeriesProductDecodeBHist (fastSeriesProductEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def fastSeriesProductFields : FastSeriesProductUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FastSeriesProductUp.mk F G K W M T R E L C P N =>
      [F, G, K, W, M, T, R, E, L, C, P, N]

def fastSeriesProductToEventFlow : FastSeriesProductUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (fastSeriesProductFields x).map fastSeriesProductEncodeBHist

private def fastSeriesProductDecodePacket
    (F G K W M T R E L C P N : RawEvent) : FastSeriesProductUp :=
  -- BEDC touchpoint anchor: BHist BMark
  FastSeriesProductUp.mk
    (fastSeriesProductDecodeBHist F)
    (fastSeriesProductDecodeBHist G)
    (fastSeriesProductDecodeBHist K)
    (fastSeriesProductDecodeBHist W)
    (fastSeriesProductDecodeBHist M)
    (fastSeriesProductDecodeBHist T)
    (fastSeriesProductDecodeBHist R)
    (fastSeriesProductDecodeBHist E)
    (fastSeriesProductDecodeBHist L)
    (fastSeriesProductDecodeBHist C)
    (fastSeriesProductDecodeBHist P)
    (fastSeriesProductDecodeBHist N)

private def fastSeriesProductRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => fastSeriesProductRawAt n rest

private def fastSeriesProductLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => fastSeriesProductLengthEq n rest

def fastSeriesProductFromEventFlow (flow : EventFlow) : Option FastSeriesProductUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match fastSeriesProductLengthEq 12 flow with
  | true =>
      some
        (fastSeriesProductDecodePacket
          (fastSeriesProductRawAt 0 flow)
          (fastSeriesProductRawAt 1 flow)
          (fastSeriesProductRawAt 2 flow)
          (fastSeriesProductRawAt 3 flow)
          (fastSeriesProductRawAt 4 flow)
          (fastSeriesProductRawAt 5 flow)
          (fastSeriesProductRawAt 6 flow)
          (fastSeriesProductRawAt 7 flow)
          (fastSeriesProductRawAt 8 flow)
          (fastSeriesProductRawAt 9 flow)
          (fastSeriesProductRawAt 10 flow)
          (fastSeriesProductRawAt 11 flow))
  | false => none

private theorem fastSeriesProduct_round_trip :
    ∀ x : FastSeriesProductUp,
      fastSeriesProductFromEventFlow (fastSeriesProductToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F G K W M T R E L C P N =>
      change
        some
          (fastSeriesProductDecodePacket
            (fastSeriesProductEncodeBHist F)
            (fastSeriesProductEncodeBHist G)
            (fastSeriesProductEncodeBHist K)
            (fastSeriesProductEncodeBHist W)
            (fastSeriesProductEncodeBHist M)
            (fastSeriesProductEncodeBHist T)
            (fastSeriesProductEncodeBHist R)
            (fastSeriesProductEncodeBHist E)
            (fastSeriesProductEncodeBHist L)
            (fastSeriesProductEncodeBHist C)
            (fastSeriesProductEncodeBHist P)
            (fastSeriesProductEncodeBHist N)) =
          some (FastSeriesProductUp.mk F G K W M T R E L C P N)
      unfold fastSeriesProductDecodePacket
      rw [fastSeriesProduct_decode_encode F,
        fastSeriesProduct_decode_encode G,
        fastSeriesProduct_decode_encode K,
        fastSeriesProduct_decode_encode W,
        fastSeriesProduct_decode_encode M,
        fastSeriesProduct_decode_encode T,
        fastSeriesProduct_decode_encode R,
        fastSeriesProduct_decode_encode E,
        fastSeriesProduct_decode_encode L,
        fastSeriesProduct_decode_encode C,
        fastSeriesProduct_decode_encode P,
        fastSeriesProduct_decode_encode N]

private theorem fastSeriesProductToEventFlow_injective {x y : FastSeriesProductUp} :
    fastSeriesProductToEventFlow x = fastSeriesProductToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      fastSeriesProductFromEventFlow (fastSeriesProductToEventFlow x) =
        fastSeriesProductFromEventFlow (fastSeriesProductToEventFlow y) :=
    congrArg fastSeriesProductFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (fastSeriesProduct_round_trip x).symm
      (Eq.trans hread (fastSeriesProduct_round_trip y)))

instance fastSeriesProductBHistCarrier : BHistCarrier FastSeriesProductUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := fastSeriesProductToEventFlow
  fromEventFlow := fastSeriesProductFromEventFlow

instance fastSeriesProductChapterTasteGate : ChapterTasteGate FastSeriesProductUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change fastSeriesProductFromEventFlow (fastSeriesProductToEventFlow x) = some x
    exact fastSeriesProduct_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (fastSeriesProductToEventFlow_injective heq)

theorem FastSeriesProductTasteGate_single_carrier_alignment :
    fastSeriesProductFromEventFlow
        (fastSeriesProductToEventFlow
          (FastSeriesProductUp.mk BHist.Empty (BHist.e0 BHist.Empty)
            (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty)) =
      some
        (FastSeriesProductUp.mk BHist.Empty (BHist.e0 BHist.Empty)
          (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) ∧
      fastSeriesProductToEventFlow
        (FastSeriesProductUp.mk BHist.Empty (BHist.e0 BHist.Empty)
          (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        fastSeriesProductToEventFlow
          (FastSeriesProductUp.mk BHist.Empty (BHist.e0 BHist.Empty)
            (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · rfl
  · rfl

end BEDC.Derived.FastSeriesProductUp
