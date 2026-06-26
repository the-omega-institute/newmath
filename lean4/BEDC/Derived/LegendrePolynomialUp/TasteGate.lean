import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LegendrePolynomialUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LegendrePolynomialUp : Type where
  | mk (d P0 P1 R N O W Q E H C Pi A : BHist) : LegendrePolynomialUp
  deriving DecidableEq

def LegendrePolynomialUp_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: LegendrePolynomialUp_encodeBHist h
  | BHist.e1 h => BMark.b1 :: LegendrePolynomialUp_encodeBHist h

def LegendrePolynomialUp_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (LegendrePolynomialUp_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (LegendrePolynomialUp_decodeBHist tail)

private theorem LegendrePolynomialUp_decode_encode :
    ∀ h : BHist, LegendrePolynomialUp_decodeBHist (LegendrePolynomialUp_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def LegendrePolynomialUp_toEventFlow : LegendrePolynomialUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LegendrePolynomialUp.mk d P0 P1 R N O W Q E H C Pi A =>
      [LegendrePolynomialUp_encodeBHist d,
        LegendrePolynomialUp_encodeBHist P0,
        LegendrePolynomialUp_encodeBHist P1,
        LegendrePolynomialUp_encodeBHist R,
        LegendrePolynomialUp_encodeBHist N,
        LegendrePolynomialUp_encodeBHist O,
        LegendrePolynomialUp_encodeBHist W,
        LegendrePolynomialUp_encodeBHist Q,
        LegendrePolynomialUp_encodeBHist E,
        LegendrePolynomialUp_encodeBHist H,
        LegendrePolynomialUp_encodeBHist C,
        LegendrePolynomialUp_encodeBHist Pi,
        LegendrePolynomialUp_encodeBHist A]

private def LegendrePolynomialUp_eventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => LegendrePolynomialUp_eventAtDefault index rest

def LegendrePolynomialUp_fromEventFlow (ef : EventFlow) : Option LegendrePolynomialUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LegendrePolynomialUp.mk
      (LegendrePolynomialUp_decodeBHist (LegendrePolynomialUp_eventAtDefault 0 ef))
      (LegendrePolynomialUp_decodeBHist (LegendrePolynomialUp_eventAtDefault 1 ef))
      (LegendrePolynomialUp_decodeBHist (LegendrePolynomialUp_eventAtDefault 2 ef))
      (LegendrePolynomialUp_decodeBHist (LegendrePolynomialUp_eventAtDefault 3 ef))
      (LegendrePolynomialUp_decodeBHist (LegendrePolynomialUp_eventAtDefault 4 ef))
      (LegendrePolynomialUp_decodeBHist (LegendrePolynomialUp_eventAtDefault 5 ef))
      (LegendrePolynomialUp_decodeBHist (LegendrePolynomialUp_eventAtDefault 6 ef))
      (LegendrePolynomialUp_decodeBHist (LegendrePolynomialUp_eventAtDefault 7 ef))
      (LegendrePolynomialUp_decodeBHist (LegendrePolynomialUp_eventAtDefault 8 ef))
      (LegendrePolynomialUp_decodeBHist (LegendrePolynomialUp_eventAtDefault 9 ef))
      (LegendrePolynomialUp_decodeBHist (LegendrePolynomialUp_eventAtDefault 10 ef))
      (LegendrePolynomialUp_decodeBHist (LegendrePolynomialUp_eventAtDefault 11 ef))
      (LegendrePolynomialUp_decodeBHist (LegendrePolynomialUp_eventAtDefault 12 ef)))

private theorem LegendrePolynomialUp_round_trip :
    ∀ x : LegendrePolynomialUp,
      LegendrePolynomialUp_fromEventFlow (LegendrePolynomialUp_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk d P0 P1 R N O W Q E H C Pi A =>
      change
        some
          (LegendrePolynomialUp.mk
            (LegendrePolynomialUp_decodeBHist (LegendrePolynomialUp_encodeBHist d))
            (LegendrePolynomialUp_decodeBHist (LegendrePolynomialUp_encodeBHist P0))
            (LegendrePolynomialUp_decodeBHist (LegendrePolynomialUp_encodeBHist P1))
            (LegendrePolynomialUp_decodeBHist (LegendrePolynomialUp_encodeBHist R))
            (LegendrePolynomialUp_decodeBHist (LegendrePolynomialUp_encodeBHist N))
            (LegendrePolynomialUp_decodeBHist (LegendrePolynomialUp_encodeBHist O))
            (LegendrePolynomialUp_decodeBHist (LegendrePolynomialUp_encodeBHist W))
            (LegendrePolynomialUp_decodeBHist (LegendrePolynomialUp_encodeBHist Q))
            (LegendrePolynomialUp_decodeBHist (LegendrePolynomialUp_encodeBHist E))
            (LegendrePolynomialUp_decodeBHist (LegendrePolynomialUp_encodeBHist H))
            (LegendrePolynomialUp_decodeBHist (LegendrePolynomialUp_encodeBHist C))
            (LegendrePolynomialUp_decodeBHist (LegendrePolynomialUp_encodeBHist Pi))
            (LegendrePolynomialUp_decodeBHist (LegendrePolynomialUp_encodeBHist A))) =
          some (LegendrePolynomialUp.mk d P0 P1 R N O W Q E H C Pi A)
      rw [LegendrePolynomialUp_decode_encode d, LegendrePolynomialUp_decode_encode P0,
        LegendrePolynomialUp_decode_encode P1, LegendrePolynomialUp_decode_encode R,
        LegendrePolynomialUp_decode_encode N, LegendrePolynomialUp_decode_encode O,
        LegendrePolynomialUp_decode_encode W, LegendrePolynomialUp_decode_encode Q,
        LegendrePolynomialUp_decode_encode E, LegendrePolynomialUp_decode_encode H,
        LegendrePolynomialUp_decode_encode C, LegendrePolynomialUp_decode_encode Pi,
        LegendrePolynomialUp_decode_encode A]

private theorem LegendrePolynomialUp_toEventFlow_injective {x y : LegendrePolynomialUp} :
    LegendrePolynomialUp_toEventFlow x = LegendrePolynomialUp_toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      LegendrePolynomialUp_fromEventFlow (LegendrePolynomialUp_toEventFlow x) =
        LegendrePolynomialUp_fromEventFlow (LegendrePolynomialUp_toEventFlow y) :=
    congrArg LegendrePolynomialUp_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LegendrePolynomialUp_round_trip x).symm
      (Eq.trans hread (LegendrePolynomialUp_round_trip y)))

instance legendrePolynomialBHistCarrier : BHistCarrier LegendrePolynomialUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := LegendrePolynomialUp_toEventFlow
  fromEventFlow := LegendrePolynomialUp_fromEventFlow

instance legendrePolynomialChapterTasteGate : ChapterTasteGate LegendrePolynomialUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change LegendrePolynomialUp_fromEventFlow (LegendrePolynomialUp_toEventFlow x) = some x
    exact LegendrePolynomialUp_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LegendrePolynomialUp_toEventFlow_injective heq)

end BEDC.Derived.LegendrePolynomialUp
