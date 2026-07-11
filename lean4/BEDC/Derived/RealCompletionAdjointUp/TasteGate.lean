import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealCompletionAdjointUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealCompletionAdjointUp : Type where
  | mk (D S Q R E U X K H C P N : BHist) : RealCompletionAdjointUp
  deriving DecidableEq

def realCompletionAdjointEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realCompletionAdjointEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realCompletionAdjointEncodeBHist h

def realCompletionAdjointDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realCompletionAdjointDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realCompletionAdjointDecodeBHist tail)

private theorem RealCompletionAdjointTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, realCompletionAdjointDecodeBHist (realCompletionAdjointEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realCompletionAdjointFields : RealCompletionAdjointUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealCompletionAdjointUp.mk D S Q R E U X K H C P N => [D, S, Q, R, E, U, X, K, H, C, P, N]

def realCompletionAdjointToEventFlow : RealCompletionAdjointUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (realCompletionAdjointFields x).map realCompletionAdjointEncodeBHist

private def realCompletionAdjointEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realCompletionAdjointEventAtDefault index rest

def realCompletionAdjointFromEventFlow (ef : EventFlow) : Option RealCompletionAdjointUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealCompletionAdjointUp.mk
      (realCompletionAdjointDecodeBHist (realCompletionAdjointEventAtDefault 0 ef))
      (realCompletionAdjointDecodeBHist (realCompletionAdjointEventAtDefault 1 ef))
      (realCompletionAdjointDecodeBHist (realCompletionAdjointEventAtDefault 2 ef))
      (realCompletionAdjointDecodeBHist (realCompletionAdjointEventAtDefault 3 ef))
      (realCompletionAdjointDecodeBHist (realCompletionAdjointEventAtDefault 4 ef))
      (realCompletionAdjointDecodeBHist (realCompletionAdjointEventAtDefault 5 ef))
      (realCompletionAdjointDecodeBHist (realCompletionAdjointEventAtDefault 6 ef))
      (realCompletionAdjointDecodeBHist (realCompletionAdjointEventAtDefault 7 ef))
      (realCompletionAdjointDecodeBHist (realCompletionAdjointEventAtDefault 8 ef))
      (realCompletionAdjointDecodeBHist (realCompletionAdjointEventAtDefault 9 ef))
      (realCompletionAdjointDecodeBHist (realCompletionAdjointEventAtDefault 10 ef))
      (realCompletionAdjointDecodeBHist (realCompletionAdjointEventAtDefault 11 ef)))

private theorem RealCompletionAdjointTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RealCompletionAdjointUp,
      realCompletionAdjointFromEventFlow (realCompletionAdjointToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D S Q R E U X K H C P N =>
      change
        some
          (RealCompletionAdjointUp.mk
            (realCompletionAdjointDecodeBHist (realCompletionAdjointEncodeBHist D))
            (realCompletionAdjointDecodeBHist (realCompletionAdjointEncodeBHist S))
            (realCompletionAdjointDecodeBHist (realCompletionAdjointEncodeBHist Q))
            (realCompletionAdjointDecodeBHist (realCompletionAdjointEncodeBHist R))
            (realCompletionAdjointDecodeBHist (realCompletionAdjointEncodeBHist E))
            (realCompletionAdjointDecodeBHist (realCompletionAdjointEncodeBHist U))
            (realCompletionAdjointDecodeBHist (realCompletionAdjointEncodeBHist X))
            (realCompletionAdjointDecodeBHist (realCompletionAdjointEncodeBHist K))
            (realCompletionAdjointDecodeBHist (realCompletionAdjointEncodeBHist H))
            (realCompletionAdjointDecodeBHist (realCompletionAdjointEncodeBHist C))
            (realCompletionAdjointDecodeBHist (realCompletionAdjointEncodeBHist P))
            (realCompletionAdjointDecodeBHist (realCompletionAdjointEncodeBHist N))) =
          some (RealCompletionAdjointUp.mk D S Q R E U X K H C P N)
      rw [RealCompletionAdjointTasteGate_single_carrier_alignment_decode D,
        RealCompletionAdjointTasteGate_single_carrier_alignment_decode S,
        RealCompletionAdjointTasteGate_single_carrier_alignment_decode Q,
        RealCompletionAdjointTasteGate_single_carrier_alignment_decode R,
        RealCompletionAdjointTasteGate_single_carrier_alignment_decode E,
        RealCompletionAdjointTasteGate_single_carrier_alignment_decode U,
        RealCompletionAdjointTasteGate_single_carrier_alignment_decode X,
        RealCompletionAdjointTasteGate_single_carrier_alignment_decode K,
        RealCompletionAdjointTasteGate_single_carrier_alignment_decode H,
        RealCompletionAdjointTasteGate_single_carrier_alignment_decode C,
        RealCompletionAdjointTasteGate_single_carrier_alignment_decode P,
        RealCompletionAdjointTasteGate_single_carrier_alignment_decode N]

private theorem RealCompletionAdjointTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealCompletionAdjointUp} :
    realCompletionAdjointToEventFlow x = realCompletionAdjointToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realCompletionAdjointFromEventFlow (realCompletionAdjointToEventFlow x) =
        realCompletionAdjointFromEventFlow (realCompletionAdjointToEventFlow y) :=
    congrArg realCompletionAdjointFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RealCompletionAdjointTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RealCompletionAdjointTasteGate_single_carrier_alignment_round_trip y)))

instance realCompletionAdjointBHistCarrier : BHistCarrier RealCompletionAdjointUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realCompletionAdjointToEventFlow
  fromEventFlow := realCompletionAdjointFromEventFlow

instance realCompletionAdjointChapterTasteGate : ChapterTasteGate RealCompletionAdjointUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realCompletionAdjointFromEventFlow (realCompletionAdjointToEventFlow x) = some x
    exact RealCompletionAdjointTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealCompletionAdjointTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem RealCompletionAdjointTasteGate_single_carrier_alignment :
    (∀ h : BHist, realCompletionAdjointDecodeBHist (realCompletionAdjointEncodeBHist h) = h) ∧
      (∀ x : RealCompletionAdjointUp,
        realCompletionAdjointFromEventFlow (realCompletionAdjointToEventFlow x) = some x) ∧
        (∀ x y : RealCompletionAdjointUp,
          realCompletionAdjointToEventFlow x = realCompletionAdjointToEventFlow y → x = y) ∧
          realCompletionAdjointEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RealCompletionAdjointTasteGate_single_carrier_alignment_decode,
      RealCompletionAdjointTasteGate_single_carrier_alignment_round_trip,
      fun x y => RealCompletionAdjointTasteGate_single_carrier_alignment_toEventFlow_injective,
      rfl⟩

end BEDC.Derived.RealCompletionAdjointUp
