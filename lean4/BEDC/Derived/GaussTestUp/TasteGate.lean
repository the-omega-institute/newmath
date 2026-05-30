import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GaussTestUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive GaussTestUp : Type where
  | mk (S R Q T B C E H K P N : BHist) : GaussTestUp

def gaussTestEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: gaussTestEncodeBHist h
  | BHist.e1 h => BMark.b1 :: gaussTestEncodeBHist h

def gaussTestDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (gaussTestDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (gaussTestDecodeBHist tail)

private theorem GaussTestTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, gaussTestDecodeBHist (gaussTestEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def gaussTestFields : GaussTestUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | GaussTestUp.mk S R Q T B C E H K P N => [S, R, Q, T, B, C, E, H, K, P, N]

def gaussTestToEventFlow : GaussTestUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (gaussTestFields x).map gaussTestEncodeBHist

private def gaussTestRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _ => event
  | Nat.succ _, [] => []
  | Nat.succ index, _ :: rest => gaussTestRawAt index rest

def gaussTestFromEventFlow (flow : EventFlow) : Option GaussTestUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (GaussTestUp.mk
      (gaussTestDecodeBHist (gaussTestRawAt 0 flow))
      (gaussTestDecodeBHist (gaussTestRawAt 1 flow))
      (gaussTestDecodeBHist (gaussTestRawAt 2 flow))
      (gaussTestDecodeBHist (gaussTestRawAt 3 flow))
      (gaussTestDecodeBHist (gaussTestRawAt 4 flow))
      (gaussTestDecodeBHist (gaussTestRawAt 5 flow))
      (gaussTestDecodeBHist (gaussTestRawAt 6 flow))
      (gaussTestDecodeBHist (gaussTestRawAt 7 flow))
      (gaussTestDecodeBHist (gaussTestRawAt 8 flow))
      (gaussTestDecodeBHist (gaussTestRawAt 9 flow))
      (gaussTestDecodeBHist (gaussTestRawAt 10 flow)))

private theorem GaussTestTasteGate_single_carrier_alignment_round_trip
    (x : GaussTestUp) :
    gaussTestFromEventFlow (gaussTestToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S R Q T B C E H K P N =>
      change
        some
          (GaussTestUp.mk
            (gaussTestDecodeBHist (gaussTestEncodeBHist S))
            (gaussTestDecodeBHist (gaussTestEncodeBHist R))
            (gaussTestDecodeBHist (gaussTestEncodeBHist Q))
            (gaussTestDecodeBHist (gaussTestEncodeBHist T))
            (gaussTestDecodeBHist (gaussTestEncodeBHist B))
            (gaussTestDecodeBHist (gaussTestEncodeBHist C))
            (gaussTestDecodeBHist (gaussTestEncodeBHist E))
            (gaussTestDecodeBHist (gaussTestEncodeBHist H))
            (gaussTestDecodeBHist (gaussTestEncodeBHist K))
            (gaussTestDecodeBHist (gaussTestEncodeBHist P))
            (gaussTestDecodeBHist (gaussTestEncodeBHist N))) =
          some (GaussTestUp.mk S R Q T B C E H K P N)
      rw [GaussTestTasteGate_single_carrier_alignment_decode_encode S,
        GaussTestTasteGate_single_carrier_alignment_decode_encode R,
        GaussTestTasteGate_single_carrier_alignment_decode_encode Q,
        GaussTestTasteGate_single_carrier_alignment_decode_encode T,
        GaussTestTasteGate_single_carrier_alignment_decode_encode B,
        GaussTestTasteGate_single_carrier_alignment_decode_encode C,
        GaussTestTasteGate_single_carrier_alignment_decode_encode E,
        GaussTestTasteGate_single_carrier_alignment_decode_encode H,
        GaussTestTasteGate_single_carrier_alignment_decode_encode K,
        GaussTestTasteGate_single_carrier_alignment_decode_encode P,
        GaussTestTasteGate_single_carrier_alignment_decode_encode N]

private theorem GaussTestTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : GaussTestUp} :
    gaussTestToEventFlow x = gaussTestToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      gaussTestFromEventFlow (gaussTestToEventFlow x) =
        gaussTestFromEventFlow (gaussTestToEventFlow y) :=
    congrArg gaussTestFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (GaussTestTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (GaussTestTasteGate_single_carrier_alignment_round_trip y)))

instance gaussTestBHistCarrier : BHistCarrier GaussTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := gaussTestToEventFlow
  fromEventFlow := gaussTestFromEventFlow

instance gaussTestChapterTasteGate : ChapterTasteGate GaussTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change gaussTestFromEventFlow (gaussTestToEventFlow x) = some x
    exact GaussTestTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (GaussTestTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem GaussTestTasteGate_single_carrier_alignment :
    ChapterTasteGate GaussTestUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact gaussTestChapterTasteGate

end BEDC.Derived.GaussTestUp
