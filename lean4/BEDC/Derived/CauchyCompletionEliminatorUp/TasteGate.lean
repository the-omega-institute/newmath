import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionEliminatorUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionEliminatorUp : Type where
  | mk (D T M A U H C P N : BHist) : CauchyCompletionEliminatorUp
  deriving DecidableEq

def cauchyCompletionEliminatorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionEliminatorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionEliminatorEncodeBHist h

def cauchyCompletionEliminatorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionEliminatorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionEliminatorDecodeBHist tail)

private theorem cauchyCompletionEliminatorDecode_encode_bhist :
    ∀ h : BHist,
      cauchyCompletionEliminatorDecodeBHist
        (cauchyCompletionEliminatorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCompletionEliminatorFields :
    CauchyCompletionEliminatorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionEliminatorUp.mk D T M A U H C P N =>
      [D, T, M, A, U, H, C, P, N]

def cauchyCompletionEliminatorToEventFlow :
    CauchyCompletionEliminatorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyCompletionEliminatorFields x).map cauchyCompletionEliminatorEncodeBHist

private def cauchyCompletionEliminatorEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyCompletionEliminatorEventAtDefault index rest

def cauchyCompletionEliminatorFromEventFlow
    (ef : EventFlow) : Option CauchyCompletionEliminatorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyCompletionEliminatorUp.mk
      (cauchyCompletionEliminatorDecodeBHist
        (cauchyCompletionEliminatorEventAtDefault 0 ef))
      (cauchyCompletionEliminatorDecodeBHist
        (cauchyCompletionEliminatorEventAtDefault 1 ef))
      (cauchyCompletionEliminatorDecodeBHist
        (cauchyCompletionEliminatorEventAtDefault 2 ef))
      (cauchyCompletionEliminatorDecodeBHist
        (cauchyCompletionEliminatorEventAtDefault 3 ef))
      (cauchyCompletionEliminatorDecodeBHist
        (cauchyCompletionEliminatorEventAtDefault 4 ef))
      (cauchyCompletionEliminatorDecodeBHist
        (cauchyCompletionEliminatorEventAtDefault 5 ef))
      (cauchyCompletionEliminatorDecodeBHist
        (cauchyCompletionEliminatorEventAtDefault 6 ef))
      (cauchyCompletionEliminatorDecodeBHist
        (cauchyCompletionEliminatorEventAtDefault 7 ef))
      (cauchyCompletionEliminatorDecodeBHist
        (cauchyCompletionEliminatorEventAtDefault 8 ef)))

private theorem cauchyCompletionEliminator_round_trip :
    ∀ x : CauchyCompletionEliminatorUp,
      cauchyCompletionEliminatorFromEventFlow
        (cauchyCompletionEliminatorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D T M A U H C P N =>
      change
        some
          (CauchyCompletionEliminatorUp.mk
            (cauchyCompletionEliminatorDecodeBHist
              (cauchyCompletionEliminatorEncodeBHist D))
            (cauchyCompletionEliminatorDecodeBHist
              (cauchyCompletionEliminatorEncodeBHist T))
            (cauchyCompletionEliminatorDecodeBHist
              (cauchyCompletionEliminatorEncodeBHist M))
            (cauchyCompletionEliminatorDecodeBHist
              (cauchyCompletionEliminatorEncodeBHist A))
            (cauchyCompletionEliminatorDecodeBHist
              (cauchyCompletionEliminatorEncodeBHist U))
            (cauchyCompletionEliminatorDecodeBHist
              (cauchyCompletionEliminatorEncodeBHist H))
            (cauchyCompletionEliminatorDecodeBHist
              (cauchyCompletionEliminatorEncodeBHist C))
            (cauchyCompletionEliminatorDecodeBHist
              (cauchyCompletionEliminatorEncodeBHist P))
            (cauchyCompletionEliminatorDecodeBHist
              (cauchyCompletionEliminatorEncodeBHist N))) =
          some (CauchyCompletionEliminatorUp.mk D T M A U H C P N)
      rw [cauchyCompletionEliminatorDecode_encode_bhist D,
        cauchyCompletionEliminatorDecode_encode_bhist T,
        cauchyCompletionEliminatorDecode_encode_bhist M,
        cauchyCompletionEliminatorDecode_encode_bhist A,
        cauchyCompletionEliminatorDecode_encode_bhist U,
        cauchyCompletionEliminatorDecode_encode_bhist H,
        cauchyCompletionEliminatorDecode_encode_bhist C,
        cauchyCompletionEliminatorDecode_encode_bhist P,
        cauchyCompletionEliminatorDecode_encode_bhist N]

private theorem cauchyCompletionEliminatorToEventFlow_injective
    {x y : CauchyCompletionEliminatorUp} :
    cauchyCompletionEliminatorToEventFlow x =
      cauchyCompletionEliminatorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletionEliminatorFromEventFlow (cauchyCompletionEliminatorToEventFlow x) =
        cauchyCompletionEliminatorFromEventFlow (cauchyCompletionEliminatorToEventFlow y) :=
    congrArg cauchyCompletionEliminatorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyCompletionEliminator_round_trip x).symm
      (Eq.trans hread (cauchyCompletionEliminator_round_trip y)))

instance cauchyCompletionEliminatorBHistCarrier :
    BHistCarrier CauchyCompletionEliminatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionEliminatorToEventFlow
  fromEventFlow := cauchyCompletionEliminatorFromEventFlow

instance cauchyCompletionEliminatorChapterTasteGate :
    ChapterTasteGate CauchyCompletionEliminatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompletionEliminatorFromEventFlow
        (cauchyCompletionEliminatorToEventFlow x) = some x
    exact cauchyCompletionEliminator_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyCompletionEliminatorToEventFlow_injective heq)

theorem CauchyCompletionEliminatorTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyCompletionEliminatorDecodeBHist
      (cauchyCompletionEliminatorEncodeBHist h) = h) ∧
      (∀ x : CauchyCompletionEliminatorUp,
        cauchyCompletionEliminatorFromEventFlow
          (cauchyCompletionEliminatorToEventFlow x) = some x) ∧
        (∀ x y : CauchyCompletionEliminatorUp,
          cauchyCompletionEliminatorToEventFlow x =
            cauchyCompletionEliminatorToEventFlow y → x = y) ∧
          cauchyCompletionEliminatorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact cauchyCompletionEliminatorDecode_encode_bhist
  · constructor
    · exact cauchyCompletionEliminator_round_trip
    · constructor
      · intro x y heq
        exact cauchyCompletionEliminatorToEventFlow_injective heq
      · rfl

end BEDC.Derived.CauchyCompletionEliminatorUp.TasteGate
