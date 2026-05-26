import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchySumUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchySumUp : Type where
  | mk (A B WA WB DA DB D E R H C P N : BHist) : RegularCauchySumUp
  deriving DecidableEq

def regularCauchySumEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchySumEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchySumEncodeBHist h

def regularCauchySumDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchySumDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchySumDecodeBHist tail)

private theorem regularCauchySum_decode_encode :
    ∀ h : BHist, regularCauchySumDecodeBHist (regularCauchySumEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchySumToEventFlow : RegularCauchySumUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchySumUp.mk A B WA WB DA DB D E R H C P N =>
      [[BMark.b0, BMark.b1],
        regularCauchySumEncodeBHist A,
        regularCauchySumEncodeBHist B,
        regularCauchySumEncodeBHist WA,
        regularCauchySumEncodeBHist WB,
        regularCauchySumEncodeBHist DA,
        regularCauchySumEncodeBHist DB,
        regularCauchySumEncodeBHist D,
        regularCauchySumEncodeBHist E,
        regularCauchySumEncodeBHist R,
        regularCauchySumEncodeBHist H,
        regularCauchySumEncodeBHist C,
        regularCauchySumEncodeBHist P,
        regularCauchySumEncodeBHist N]

private def regularCauchySumEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchySumEventAtDefault index rest

def regularCauchySumFromEventFlow (ef : EventFlow) : Option RegularCauchySumUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchySumUp.mk
      (regularCauchySumDecodeBHist (regularCauchySumEventAtDefault 1 ef))
      (regularCauchySumDecodeBHist (regularCauchySumEventAtDefault 2 ef))
      (regularCauchySumDecodeBHist (regularCauchySumEventAtDefault 3 ef))
      (regularCauchySumDecodeBHist (regularCauchySumEventAtDefault 4 ef))
      (regularCauchySumDecodeBHist (regularCauchySumEventAtDefault 5 ef))
      (regularCauchySumDecodeBHist (regularCauchySumEventAtDefault 6 ef))
      (regularCauchySumDecodeBHist (regularCauchySumEventAtDefault 7 ef))
      (regularCauchySumDecodeBHist (regularCauchySumEventAtDefault 8 ef))
      (regularCauchySumDecodeBHist (regularCauchySumEventAtDefault 9 ef))
      (regularCauchySumDecodeBHist (regularCauchySumEventAtDefault 10 ef))
      (regularCauchySumDecodeBHist (regularCauchySumEventAtDefault 11 ef))
      (regularCauchySumDecodeBHist (regularCauchySumEventAtDefault 12 ef))
      (regularCauchySumDecodeBHist (regularCauchySumEventAtDefault 13 ef)))

private theorem regularCauchySum_round_trip :
    ∀ x : RegularCauchySumUp,
      regularCauchySumFromEventFlow (regularCauchySumToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A B WA WB DA DB D E R H C P N =>
      change
        some
          (RegularCauchySumUp.mk
            (regularCauchySumDecodeBHist (regularCauchySumEncodeBHist A))
            (regularCauchySumDecodeBHist (regularCauchySumEncodeBHist B))
            (regularCauchySumDecodeBHist (regularCauchySumEncodeBHist WA))
            (regularCauchySumDecodeBHist (regularCauchySumEncodeBHist WB))
            (regularCauchySumDecodeBHist (regularCauchySumEncodeBHist DA))
            (regularCauchySumDecodeBHist (regularCauchySumEncodeBHist DB))
            (regularCauchySumDecodeBHist (regularCauchySumEncodeBHist D))
            (regularCauchySumDecodeBHist (regularCauchySumEncodeBHist E))
            (regularCauchySumDecodeBHist (regularCauchySumEncodeBHist R))
            (regularCauchySumDecodeBHist (regularCauchySumEncodeBHist H))
            (regularCauchySumDecodeBHist (regularCauchySumEncodeBHist C))
            (regularCauchySumDecodeBHist (regularCauchySumEncodeBHist P))
            (regularCauchySumDecodeBHist (regularCauchySumEncodeBHist N))) =
          some (RegularCauchySumUp.mk A B WA WB DA DB D E R H C P N)
      rw [regularCauchySum_decode_encode A, regularCauchySum_decode_encode B,
        regularCauchySum_decode_encode WA, regularCauchySum_decode_encode WB,
        regularCauchySum_decode_encode DA, regularCauchySum_decode_encode DB,
        regularCauchySum_decode_encode D, regularCauchySum_decode_encode E,
        regularCauchySum_decode_encode R, regularCauchySum_decode_encode H,
        regularCauchySum_decode_encode C, regularCauchySum_decode_encode P,
        regularCauchySum_decode_encode N]

private theorem regularCauchySumToEventFlow_injective {x y : RegularCauchySumUp} :
    regularCauchySumToEventFlow x = regularCauchySumToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x = regularCauchySumFromEventFlow (regularCauchySumToEventFlow x) :=
        (regularCauchySum_round_trip x).symm
      _ = regularCauchySumFromEventFlow (regularCauchySumToEventFlow y) :=
        congrArg regularCauchySumFromEventFlow hxy
      _ = some y := regularCauchySum_round_trip y
  exact Option.some.inj optionEq

instance regularCauchySumBHistCarrier : BHistCarrier RegularCauchySumUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchySumToEventFlow
  fromEventFlow := regularCauchySumFromEventFlow

instance regularCauchySumChapterTasteGate : ChapterTasteGate RegularCauchySumUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchySumFromEventFlow (regularCauchySumToEventFlow x) = some x
    exact regularCauchySum_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchySumToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchySumUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchySumChapterTasteGate

theorem RegularCauchySumTasteGate_single_carrier_alignment :
    (∀ h : BHist, regularCauchySumDecodeBHist (regularCauchySumEncodeBHist h) = h) ∧
      (∀ x : RegularCauchySumUp,
        regularCauchySumFromEventFlow (regularCauchySumToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchySumUp,
          regularCauchySumToEventFlow x = regularCauchySumToEventFlow y → x = y) ∧
          regularCauchySumEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨regularCauchySum_decode_encode, regularCauchySum_round_trip,
      (fun _ _ heq => regularCauchySumToEventFlow_injective heq), rfl⟩

end BEDC.Derived.RegularCauchySumUp
