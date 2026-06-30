import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RaabeTestUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RaabeTestUp : Type where
  | mk (A Q J M D W T E H C P N : BHist) : RaabeTestUp
  deriving DecidableEq

def raabeTestEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: raabeTestEncodeBHist h
  | BHist.e1 h => BMark.b1 :: raabeTestEncodeBHist h

def raabeTestDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (raabeTestDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (raabeTestDecodeBHist tail)

private theorem RaabeTestTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, raabeTestDecodeBHist (raabeTestEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def raabeTestFields : RaabeTestUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RaabeTestUp.mk A Q J M D W T E H C P N => [A, Q, J, M, D, W, T, E, H, C, P, N]

def raabeTestToEventFlow : RaabeTestUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (raabeTestFields x).map raabeTestEncodeBHist

private def raabeTestRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => raabeTestRawAt index rest

def raabeTestFromEventFlow (flow : EventFlow) : Option RaabeTestUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RaabeTestUp.mk
      (raabeTestDecodeBHist (raabeTestRawAt 0 flow))
      (raabeTestDecodeBHist (raabeTestRawAt 1 flow))
      (raabeTestDecodeBHist (raabeTestRawAt 2 flow))
      (raabeTestDecodeBHist (raabeTestRawAt 3 flow))
      (raabeTestDecodeBHist (raabeTestRawAt 4 flow))
      (raabeTestDecodeBHist (raabeTestRawAt 5 flow))
      (raabeTestDecodeBHist (raabeTestRawAt 6 flow))
      (raabeTestDecodeBHist (raabeTestRawAt 7 flow))
      (raabeTestDecodeBHist (raabeTestRawAt 8 flow))
      (raabeTestDecodeBHist (raabeTestRawAt 9 flow))
      (raabeTestDecodeBHist (raabeTestRawAt 10 flow))
      (raabeTestDecodeBHist (raabeTestRawAt 11 flow)))

private theorem RaabeTestTasteGate_single_carrier_alignment_round_trip
    (x : RaabeTestUp) :
    raabeTestFromEventFlow (raabeTestToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk A Q J M D W T E H C P N =>
      change
        some
          (RaabeTestUp.mk
            (raabeTestDecodeBHist (raabeTestEncodeBHist A))
            (raabeTestDecodeBHist (raabeTestEncodeBHist Q))
            (raabeTestDecodeBHist (raabeTestEncodeBHist J))
            (raabeTestDecodeBHist (raabeTestEncodeBHist M))
            (raabeTestDecodeBHist (raabeTestEncodeBHist D))
            (raabeTestDecodeBHist (raabeTestEncodeBHist W))
            (raabeTestDecodeBHist (raabeTestEncodeBHist T))
            (raabeTestDecodeBHist (raabeTestEncodeBHist E))
            (raabeTestDecodeBHist (raabeTestEncodeBHist H))
            (raabeTestDecodeBHist (raabeTestEncodeBHist C))
            (raabeTestDecodeBHist (raabeTestEncodeBHist P))
            (raabeTestDecodeBHist (raabeTestEncodeBHist N))) =
          some (RaabeTestUp.mk A Q J M D W T E H C P N)
      rw [RaabeTestTasteGate_single_carrier_alignment_decode_encode A,
        RaabeTestTasteGate_single_carrier_alignment_decode_encode Q,
        RaabeTestTasteGate_single_carrier_alignment_decode_encode J,
        RaabeTestTasteGate_single_carrier_alignment_decode_encode M,
        RaabeTestTasteGate_single_carrier_alignment_decode_encode D,
        RaabeTestTasteGate_single_carrier_alignment_decode_encode W,
        RaabeTestTasteGate_single_carrier_alignment_decode_encode T,
        RaabeTestTasteGate_single_carrier_alignment_decode_encode E,
        RaabeTestTasteGate_single_carrier_alignment_decode_encode H,
        RaabeTestTasteGate_single_carrier_alignment_decode_encode C,
        RaabeTestTasteGate_single_carrier_alignment_decode_encode P,
        RaabeTestTasteGate_single_carrier_alignment_decode_encode N]

private theorem RaabeTestTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RaabeTestUp} :
    raabeTestToEventFlow x = raabeTestToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      raabeTestFromEventFlow (raabeTestToEventFlow x) =
        raabeTestFromEventFlow (raabeTestToEventFlow y) :=
    congrArg raabeTestFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RaabeTestTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RaabeTestTasteGate_single_carrier_alignment_round_trip y)))

instance raabeTestBHistCarrier : BHistCarrier RaabeTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := raabeTestToEventFlow
  fromEventFlow := raabeTestFromEventFlow

instance raabeTestChapterTasteGate : ChapterTasteGate RaabeTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change raabeTestFromEventFlow (raabeTestToEventFlow x) = some x
    exact RaabeTestTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RaabeTestTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem RaabeTestTasteGate_single_carrier_alignment :
    (∀ h : BHist, raabeTestDecodeBHist (raabeTestEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RaabeTestUp) ∧
        Nonempty (ChapterTasteGate RaabeTestUp) ∧
          raabeTestEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨RaabeTestTasteGate_single_carrier_alignment_decode_encode,
      Nonempty.intro raabeTestBHistCarrier,
      Nonempty.intro raabeTestChapterTasteGate,
      rfl⟩

end BEDC.Derived.RaabeTestUp
