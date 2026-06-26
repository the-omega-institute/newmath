import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealCauchyFilterLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealCauchyFilterLimitUp : Type where
  | mk (F B W R D E H C P N : BHist) : RealCauchyFilterLimitUp
  deriving DecidableEq

def realCauchyFilterLimitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realCauchyFilterLimitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realCauchyFilterLimitEncodeBHist h

def realCauchyFilterLimitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realCauchyFilterLimitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realCauchyFilterLimitDecodeBHist tail)

private theorem realCauchyFilterLimitDecodeEncodeBHist :
    ∀ h : BHist,
      realCauchyFilterLimitDecodeBHist (realCauchyFilterLimitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def realCauchyFilterLimitFields : RealCauchyFilterLimitUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealCauchyFilterLimitUp.mk F B W R D E H C P N => [F, B, W, R, D, E, H, C, P, N]

def realCauchyFilterLimitToEventFlow : RealCauchyFilterLimitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realCauchyFilterLimitFields x).map realCauchyFilterLimitEncodeBHist

private def realCauchyFilterLimitEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      realCauchyFilterLimitEventAtDefault index rest

def realCauchyFilterLimitFromEventFlow (ef : EventFlow) : Option RealCauchyFilterLimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealCauchyFilterLimitUp.mk
      (realCauchyFilterLimitDecodeBHist (realCauchyFilterLimitEventAtDefault 0 ef))
      (realCauchyFilterLimitDecodeBHist (realCauchyFilterLimitEventAtDefault 1 ef))
      (realCauchyFilterLimitDecodeBHist (realCauchyFilterLimitEventAtDefault 2 ef))
      (realCauchyFilterLimitDecodeBHist (realCauchyFilterLimitEventAtDefault 3 ef))
      (realCauchyFilterLimitDecodeBHist (realCauchyFilterLimitEventAtDefault 4 ef))
      (realCauchyFilterLimitDecodeBHist (realCauchyFilterLimitEventAtDefault 5 ef))
      (realCauchyFilterLimitDecodeBHist (realCauchyFilterLimitEventAtDefault 6 ef))
      (realCauchyFilterLimitDecodeBHist (realCauchyFilterLimitEventAtDefault 7 ef))
      (realCauchyFilterLimitDecodeBHist (realCauchyFilterLimitEventAtDefault 8 ef))
      (realCauchyFilterLimitDecodeBHist (realCauchyFilterLimitEventAtDefault 9 ef)))

private theorem realCauchyFilterLimit_round_trip :
    ∀ x : RealCauchyFilterLimitUp,
      realCauchyFilterLimitFromEventFlow (realCauchyFilterLimitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F B W R D E H C P N =>
      change
        some
          (RealCauchyFilterLimitUp.mk
            (realCauchyFilterLimitDecodeBHist (realCauchyFilterLimitEncodeBHist F))
            (realCauchyFilterLimitDecodeBHist (realCauchyFilterLimitEncodeBHist B))
            (realCauchyFilterLimitDecodeBHist (realCauchyFilterLimitEncodeBHist W))
            (realCauchyFilterLimitDecodeBHist (realCauchyFilterLimitEncodeBHist R))
            (realCauchyFilterLimitDecodeBHist (realCauchyFilterLimitEncodeBHist D))
            (realCauchyFilterLimitDecodeBHist (realCauchyFilterLimitEncodeBHist E))
            (realCauchyFilterLimitDecodeBHist (realCauchyFilterLimitEncodeBHist H))
            (realCauchyFilterLimitDecodeBHist (realCauchyFilterLimitEncodeBHist C))
            (realCauchyFilterLimitDecodeBHist (realCauchyFilterLimitEncodeBHist P))
            (realCauchyFilterLimitDecodeBHist (realCauchyFilterLimitEncodeBHist N))) =
          some (RealCauchyFilterLimitUp.mk F B W R D E H C P N)
      rw [realCauchyFilterLimitDecodeEncodeBHist F,
        realCauchyFilterLimitDecodeEncodeBHist B,
        realCauchyFilterLimitDecodeEncodeBHist W,
        realCauchyFilterLimitDecodeEncodeBHist R,
        realCauchyFilterLimitDecodeEncodeBHist D,
        realCauchyFilterLimitDecodeEncodeBHist E,
        realCauchyFilterLimitDecodeEncodeBHist H,
        realCauchyFilterLimitDecodeEncodeBHist C,
        realCauchyFilterLimitDecodeEncodeBHist P,
        realCauchyFilterLimitDecodeEncodeBHist N]

private theorem realCauchyFilterLimitToEventFlow_injective {x y : RealCauchyFilterLimitUp} :
    realCauchyFilterLimitToEventFlow x = realCauchyFilterLimitToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realCauchyFilterLimitFromEventFlow (realCauchyFilterLimitToEventFlow x) =
        realCauchyFilterLimitFromEventFlow (realCauchyFilterLimitToEventFlow y) :=
    congrArg realCauchyFilterLimitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realCauchyFilterLimit_round_trip x).symm
      (Eq.trans hread (realCauchyFilterLimit_round_trip y)))

instance realCauchyFilterLimitBHistCarrier : BHistCarrier RealCauchyFilterLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realCauchyFilterLimitToEventFlow
  fromEventFlow := realCauchyFilterLimitFromEventFlow

instance realCauchyFilterLimitChapterTasteGate : ChapterTasteGate RealCauchyFilterLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realCauchyFilterLimitFromEventFlow (realCauchyFilterLimitToEventFlow x) = some x
    exact realCauchyFilterLimit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realCauchyFilterLimitToEventFlow_injective heq)

theorem RealCauchyFilterLimitTasteGate_single_carrier_alignment :
    ChapterTasteGate RealCauchyFilterLimitUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact realCauchyFilterLimitChapterTasteGate

end BEDC.Derived.RealCauchyFilterLimitUp
