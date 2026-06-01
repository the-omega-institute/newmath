import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LimitComparisonTestUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LimitComparisonTestUp : Type where
  | mk (S T WS WT QS QT D R E H C P N : BHist) : LimitComparisonTestUp
  deriving DecidableEq

def limitComparisonTestEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: limitComparisonTestEncodeBHist h
  | BHist.e1 h => BMark.b1 :: limitComparisonTestEncodeBHist h

def limitComparisonTestDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (limitComparisonTestDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (limitComparisonTestDecodeBHist tail)

private theorem limitComparisonTestDecode_encode_bhist :
    ∀ h : BHist, limitComparisonTestDecodeBHist (limitComparisonTestEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def limitComparisonTestFields : LimitComparisonTestUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LimitComparisonTestUp.mk S T WS WT QS QT D R E H C P N =>
      [S, T, WS, WT, QS, QT, D, R, E, H, C, P, N]

def limitComparisonTestToEventFlow : LimitComparisonTestUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (limitComparisonTestFields x).map limitComparisonTestEncodeBHist

private def limitComparisonTestEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => limitComparisonTestEventAtDefault index rest

def limitComparisonTestFromEventFlow : EventFlow → Option LimitComparisonTestUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (LimitComparisonTestUp.mk
        (limitComparisonTestDecodeBHist (limitComparisonTestEventAtDefault 0 ef))
        (limitComparisonTestDecodeBHist (limitComparisonTestEventAtDefault 1 ef))
        (limitComparisonTestDecodeBHist (limitComparisonTestEventAtDefault 2 ef))
        (limitComparisonTestDecodeBHist (limitComparisonTestEventAtDefault 3 ef))
        (limitComparisonTestDecodeBHist (limitComparisonTestEventAtDefault 4 ef))
        (limitComparisonTestDecodeBHist (limitComparisonTestEventAtDefault 5 ef))
        (limitComparisonTestDecodeBHist (limitComparisonTestEventAtDefault 6 ef))
        (limitComparisonTestDecodeBHist (limitComparisonTestEventAtDefault 7 ef))
        (limitComparisonTestDecodeBHist (limitComparisonTestEventAtDefault 8 ef))
        (limitComparisonTestDecodeBHist (limitComparisonTestEventAtDefault 9 ef))
        (limitComparisonTestDecodeBHist (limitComparisonTestEventAtDefault 10 ef))
        (limitComparisonTestDecodeBHist (limitComparisonTestEventAtDefault 11 ef))
        (limitComparisonTestDecodeBHist (limitComparisonTestEventAtDefault 12 ef)))

private theorem limitComparisonTest_round_trip :
    ∀ x : LimitComparisonTestUp,
      limitComparisonTestFromEventFlow (limitComparisonTestToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S T WS WT QS QT D R E H C P N =>
      change
        some
          (LimitComparisonTestUp.mk
            (limitComparisonTestDecodeBHist (limitComparisonTestEncodeBHist S))
            (limitComparisonTestDecodeBHist (limitComparisonTestEncodeBHist T))
            (limitComparisonTestDecodeBHist (limitComparisonTestEncodeBHist WS))
            (limitComparisonTestDecodeBHist (limitComparisonTestEncodeBHist WT))
            (limitComparisonTestDecodeBHist (limitComparisonTestEncodeBHist QS))
            (limitComparisonTestDecodeBHist (limitComparisonTestEncodeBHist QT))
            (limitComparisonTestDecodeBHist (limitComparisonTestEncodeBHist D))
            (limitComparisonTestDecodeBHist (limitComparisonTestEncodeBHist R))
            (limitComparisonTestDecodeBHist (limitComparisonTestEncodeBHist E))
            (limitComparisonTestDecodeBHist (limitComparisonTestEncodeBHist H))
            (limitComparisonTestDecodeBHist (limitComparisonTestEncodeBHist C))
            (limitComparisonTestDecodeBHist (limitComparisonTestEncodeBHist P))
            (limitComparisonTestDecodeBHist (limitComparisonTestEncodeBHist N))) =
          some (LimitComparisonTestUp.mk S T WS WT QS QT D R E H C P N)
      rw [limitComparisonTestDecode_encode_bhist S, limitComparisonTestDecode_encode_bhist T,
        limitComparisonTestDecode_encode_bhist WS, limitComparisonTestDecode_encode_bhist WT,
        limitComparisonTestDecode_encode_bhist QS, limitComparisonTestDecode_encode_bhist QT,
        limitComparisonTestDecode_encode_bhist D, limitComparisonTestDecode_encode_bhist R,
        limitComparisonTestDecode_encode_bhist E, limitComparisonTestDecode_encode_bhist H,
        limitComparisonTestDecode_encode_bhist C, limitComparisonTestDecode_encode_bhist P,
        limitComparisonTestDecode_encode_bhist N]

private theorem limitComparisonTestToEventFlow_injective {x y : LimitComparisonTestUp} :
    limitComparisonTestToEventFlow x = limitComparisonTestToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      limitComparisonTestFromEventFlow (limitComparisonTestToEventFlow x) =
        limitComparisonTestFromEventFlow (limitComparisonTestToEventFlow y) :=
    congrArg limitComparisonTestFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (limitComparisonTest_round_trip x).symm
      (Eq.trans hread (limitComparisonTest_round_trip y)))

instance limitComparisonTestBHistCarrier : BHistCarrier LimitComparisonTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := limitComparisonTestToEventFlow
  fromEventFlow := limitComparisonTestFromEventFlow

instance limitComparisonTestChapterTasteGate : ChapterTasteGate LimitComparisonTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change limitComparisonTestFromEventFlow (limitComparisonTestToEventFlow x) = some x
    exact limitComparisonTest_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (limitComparisonTestToEventFlow_injective heq)

theorem LimitComparisonTestTasteGate_single_carrier_alignment :
    (forall h : BHist, limitComparisonTestDecodeBHist (limitComparisonTestEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier LimitComparisonTestUp) ∧
        Nonempty (ChapterTasteGate LimitComparisonTestUp) ∧
          limitComparisonTestEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact limitComparisonTestDecode_encode_bhist
  · constructor
    · exact Nonempty.intro limitComparisonTestBHistCarrier
    · constructor
      · exact Nonempty.intro limitComparisonTestChapterTasteGate
      · rfl

end BEDC.Derived.LimitComparisonTestUp
