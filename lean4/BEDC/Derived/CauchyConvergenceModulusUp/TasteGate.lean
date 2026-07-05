import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyConvergenceModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyConvergenceModulusUp : Type where
  | mk
      (source tolerance schedule windows readback limit transport route provenance nameRow :
        BHist) : CauchyConvergenceModulusUp
  deriving DecidableEq

def cauchyConvergenceModulusEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyConvergenceModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyConvergenceModulusEncodeBHist h

def cauchyConvergenceModulusDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyConvergenceModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyConvergenceModulusDecodeBHist tail)

private theorem cauchyConvergenceModulus_decode_encode :
    forall h : BHist,
      cauchyConvergenceModulusDecodeBHist
        (cauchyConvergenceModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyConvergenceModulusFields :
    CauchyConvergenceModulusUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyConvergenceModulusUp.mk
      source tolerance schedule windows readback limit transport route provenance nameRow =>
      [source, tolerance, schedule, windows, readback, limit, transport, route, provenance,
        nameRow]

def cauchyConvergenceModulusToEventFlow :
    CauchyConvergenceModulusUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyConvergenceModulusFields x).map cauchyConvergenceModulusEncodeBHist

private def cauchyConvergenceModulusRawAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyConvergenceModulusRawAt index rest

private def cauchyConvergenceModulusLengthEq : Nat -> EventFlow -> Bool
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => true
  | Nat.zero, _event :: _rest => false
  | Nat.succ _index, [] => false
  | Nat.succ index, _event :: rest => cauchyConvergenceModulusLengthEq index rest

private def cauchyConvergenceModulusDecodePacket
    (source tolerance schedule windows readback limit transport route provenance nameRow :
      RawEvent) : CauchyConvergenceModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  CauchyConvergenceModulusUp.mk
    (cauchyConvergenceModulusDecodeBHist source)
    (cauchyConvergenceModulusDecodeBHist tolerance)
    (cauchyConvergenceModulusDecodeBHist schedule)
    (cauchyConvergenceModulusDecodeBHist windows)
    (cauchyConvergenceModulusDecodeBHist readback)
    (cauchyConvergenceModulusDecodeBHist limit)
    (cauchyConvergenceModulusDecodeBHist transport)
    (cauchyConvergenceModulusDecodeBHist route)
    (cauchyConvergenceModulusDecodeBHist provenance)
    (cauchyConvergenceModulusDecodeBHist nameRow)

def cauchyConvergenceModulusFromEventFlow
    (flow : EventFlow) : Option CauchyConvergenceModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match cauchyConvergenceModulusLengthEq 10 flow with
  | true =>
      some
        (cauchyConvergenceModulusDecodePacket
          (cauchyConvergenceModulusRawAt 0 flow)
          (cauchyConvergenceModulusRawAt 1 flow)
          (cauchyConvergenceModulusRawAt 2 flow)
          (cauchyConvergenceModulusRawAt 3 flow)
          (cauchyConvergenceModulusRawAt 4 flow)
          (cauchyConvergenceModulusRawAt 5 flow)
          (cauchyConvergenceModulusRawAt 6 flow)
          (cauchyConvergenceModulusRawAt 7 flow)
          (cauchyConvergenceModulusRawAt 8 flow)
          (cauchyConvergenceModulusRawAt 9 flow))
  | false => none

private theorem cauchyConvergenceModulus_round_trip :
    forall x : CauchyConvergenceModulusUp,
      cauchyConvergenceModulusFromEventFlow
        (cauchyConvergenceModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source tolerance schedule windows readback limit transport route provenance nameRow =>
      change
        some
          (cauchyConvergenceModulusDecodePacket
            (cauchyConvergenceModulusEncodeBHist source)
            (cauchyConvergenceModulusEncodeBHist tolerance)
            (cauchyConvergenceModulusEncodeBHist schedule)
            (cauchyConvergenceModulusEncodeBHist windows)
            (cauchyConvergenceModulusEncodeBHist readback)
            (cauchyConvergenceModulusEncodeBHist limit)
            (cauchyConvergenceModulusEncodeBHist transport)
            (cauchyConvergenceModulusEncodeBHist route)
            (cauchyConvergenceModulusEncodeBHist provenance)
            (cauchyConvergenceModulusEncodeBHist nameRow)) =
          some
            (CauchyConvergenceModulusUp.mk source tolerance schedule windows readback limit
              transport route provenance nameRow)
      unfold cauchyConvergenceModulusDecodePacket
      rw [cauchyConvergenceModulus_decode_encode source,
        cauchyConvergenceModulus_decode_encode tolerance,
        cauchyConvergenceModulus_decode_encode schedule,
        cauchyConvergenceModulus_decode_encode windows,
        cauchyConvergenceModulus_decode_encode readback,
        cauchyConvergenceModulus_decode_encode limit,
        cauchyConvergenceModulus_decode_encode transport,
        cauchyConvergenceModulus_decode_encode route,
        cauchyConvergenceModulus_decode_encode provenance,
        cauchyConvergenceModulus_decode_encode nameRow]

private theorem cauchyConvergenceModulusToEventFlow_injective
    {x y : CauchyConvergenceModulusUp} :
    cauchyConvergenceModulusToEventFlow x = cauchyConvergenceModulusToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyConvergenceModulusFromEventFlow (cauchyConvergenceModulusToEventFlow x) =
        cauchyConvergenceModulusFromEventFlow (cauchyConvergenceModulusToEventFlow y) :=
    congrArg cauchyConvergenceModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyConvergenceModulus_round_trip x).symm
      (Eq.trans hread (cauchyConvergenceModulus_round_trip y)))

instance cauchyConvergenceModulusBHistCarrier :
    BHistCarrier CauchyConvergenceModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyConvergenceModulusToEventFlow
  fromEventFlow := cauchyConvergenceModulusFromEventFlow

instance cauchyConvergenceModulusChapterTasteGate :
    ChapterTasteGate CauchyConvergenceModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyConvergenceModulusFromEventFlow
        (cauchyConvergenceModulusToEventFlow x) = some x
    exact cauchyConvergenceModulus_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyConvergenceModulusToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyConvergenceModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyConvergenceModulusChapterTasteGate

theorem CauchyConvergenceModulusTasteGate_single_carrier_alignment :
    cauchyConvergenceModulusFromEventFlow
        (cauchyConvergenceModulusToEventFlow
          (CauchyConvergenceModulusUp.mk BHist.Empty (BHist.e0 BHist.Empty)
            (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty)) =
      some
        (CauchyConvergenceModulusUp.mk BHist.Empty (BHist.e0 BHist.Empty)
          (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty) := by
  -- BEDC touchpoint anchor: BHist BMark
  rfl

end BEDC.Derived.CauchyConvergenceModulusUp
