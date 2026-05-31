import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MonotoneSubsequenceTheoremUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MonotoneSubsequenceTheoremUp : Type where
  | mk (S B Q W D R E H C P N : BHist) : MonotoneSubsequenceTheoremUp
  deriving DecidableEq

def monotoneSubsequenceTheoremEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: monotoneSubsequenceTheoremEncodeBHist h
  | BHist.e1 h => BMark.b1 :: monotoneSubsequenceTheoremEncodeBHist h

def monotoneSubsequenceTheoremDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (monotoneSubsequenceTheoremDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (monotoneSubsequenceTheoremDecodeBHist tail)

private theorem monotoneSubsequenceTheoremDecode_encode_bhist :
    ∀ h : BHist,
      monotoneSubsequenceTheoremDecodeBHist
        (monotoneSubsequenceTheoremEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def monotoneSubsequenceTheoremFields :
    MonotoneSubsequenceTheoremUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MonotoneSubsequenceTheoremUp.mk S B Q W D R E H C P N =>
      [S, B, Q, W, D, R, E, H, C, P, N]

def monotoneSubsequenceTheoremToEventFlow :
    MonotoneSubsequenceTheoremUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (monotoneSubsequenceTheoremFields x).map monotoneSubsequenceTheoremEncodeBHist

private def monotoneSubsequenceTheoremEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => monotoneSubsequenceTheoremEventAtDefault index rest

def monotoneSubsequenceTheoremFromEventFlow
    (ef : EventFlow) : Option MonotoneSubsequenceTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MonotoneSubsequenceTheoremUp.mk
      (monotoneSubsequenceTheoremDecodeBHist
        (monotoneSubsequenceTheoremEventAtDefault 0 ef))
      (monotoneSubsequenceTheoremDecodeBHist
        (monotoneSubsequenceTheoremEventAtDefault 1 ef))
      (monotoneSubsequenceTheoremDecodeBHist
        (monotoneSubsequenceTheoremEventAtDefault 2 ef))
      (monotoneSubsequenceTheoremDecodeBHist
        (monotoneSubsequenceTheoremEventAtDefault 3 ef))
      (monotoneSubsequenceTheoremDecodeBHist
        (monotoneSubsequenceTheoremEventAtDefault 4 ef))
      (monotoneSubsequenceTheoremDecodeBHist
        (monotoneSubsequenceTheoremEventAtDefault 5 ef))
      (monotoneSubsequenceTheoremDecodeBHist
        (monotoneSubsequenceTheoremEventAtDefault 6 ef))
      (monotoneSubsequenceTheoremDecodeBHist
        (monotoneSubsequenceTheoremEventAtDefault 7 ef))
      (monotoneSubsequenceTheoremDecodeBHist
        (monotoneSubsequenceTheoremEventAtDefault 8 ef))
      (monotoneSubsequenceTheoremDecodeBHist
        (monotoneSubsequenceTheoremEventAtDefault 9 ef))
      (monotoneSubsequenceTheoremDecodeBHist
        (monotoneSubsequenceTheoremEventAtDefault 10 ef)))

private theorem monotoneSubsequenceTheorem_round_trip :
    ∀ x : MonotoneSubsequenceTheoremUp,
      monotoneSubsequenceTheoremFromEventFlow
        (monotoneSubsequenceTheoremToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S B Q W D R E H C P N =>
      change
        some
          (MonotoneSubsequenceTheoremUp.mk
            (monotoneSubsequenceTheoremDecodeBHist
              (monotoneSubsequenceTheoremEncodeBHist S))
            (monotoneSubsequenceTheoremDecodeBHist
              (monotoneSubsequenceTheoremEncodeBHist B))
            (monotoneSubsequenceTheoremDecodeBHist
              (monotoneSubsequenceTheoremEncodeBHist Q))
            (monotoneSubsequenceTheoremDecodeBHist
              (monotoneSubsequenceTheoremEncodeBHist W))
            (monotoneSubsequenceTheoremDecodeBHist
              (monotoneSubsequenceTheoremEncodeBHist D))
            (monotoneSubsequenceTheoremDecodeBHist
              (monotoneSubsequenceTheoremEncodeBHist R))
            (monotoneSubsequenceTheoremDecodeBHist
              (monotoneSubsequenceTheoremEncodeBHist E))
            (monotoneSubsequenceTheoremDecodeBHist
              (monotoneSubsequenceTheoremEncodeBHist H))
            (monotoneSubsequenceTheoremDecodeBHist
              (monotoneSubsequenceTheoremEncodeBHist C))
            (monotoneSubsequenceTheoremDecodeBHist
              (monotoneSubsequenceTheoremEncodeBHist P))
            (monotoneSubsequenceTheoremDecodeBHist
              (monotoneSubsequenceTheoremEncodeBHist N))) =
          some (MonotoneSubsequenceTheoremUp.mk S B Q W D R E H C P N)
      rw [monotoneSubsequenceTheoremDecode_encode_bhist S,
        monotoneSubsequenceTheoremDecode_encode_bhist B,
        monotoneSubsequenceTheoremDecode_encode_bhist Q,
        monotoneSubsequenceTheoremDecode_encode_bhist W,
        monotoneSubsequenceTheoremDecode_encode_bhist D,
        monotoneSubsequenceTheoremDecode_encode_bhist R,
        monotoneSubsequenceTheoremDecode_encode_bhist E,
        monotoneSubsequenceTheoremDecode_encode_bhist H,
        monotoneSubsequenceTheoremDecode_encode_bhist C,
        monotoneSubsequenceTheoremDecode_encode_bhist P,
        monotoneSubsequenceTheoremDecode_encode_bhist N]

private theorem monotoneSubsequenceTheoremToEventFlow_injective
    {x y : MonotoneSubsequenceTheoremUp} :
    monotoneSubsequenceTheoremToEventFlow x =
      monotoneSubsequenceTheoremToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      monotoneSubsequenceTheoremFromEventFlow (monotoneSubsequenceTheoremToEventFlow x) =
        monotoneSubsequenceTheoremFromEventFlow (monotoneSubsequenceTheoremToEventFlow y) :=
    congrArg monotoneSubsequenceTheoremFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (monotoneSubsequenceTheorem_round_trip x).symm
      (Eq.trans hread (monotoneSubsequenceTheorem_round_trip y)))

instance monotoneSubsequenceTheoremBHistCarrier :
    BHistCarrier MonotoneSubsequenceTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := monotoneSubsequenceTheoremToEventFlow
  fromEventFlow := monotoneSubsequenceTheoremFromEventFlow

instance monotoneSubsequenceTheoremChapterTasteGate :
    ChapterTasteGate MonotoneSubsequenceTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      monotoneSubsequenceTheoremFromEventFlow
        (monotoneSubsequenceTheoremToEventFlow x) = some x
    exact monotoneSubsequenceTheorem_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (monotoneSubsequenceTheoremToEventFlow_injective heq)

theorem MonotoneSubsequenceTheoremTasteGate_single_carrier_alignment :
    (∀ h : BHist, monotoneSubsequenceTheoremDecodeBHist
      (monotoneSubsequenceTheoremEncodeBHist h) = h) ∧
      (∀ x : MonotoneSubsequenceTheoremUp,
        monotoneSubsequenceTheoremFromEventFlow
          (monotoneSubsequenceTheoremToEventFlow x) = some x) ∧
        (∀ x y : MonotoneSubsequenceTheoremUp,
          monotoneSubsequenceTheoremToEventFlow x =
            monotoneSubsequenceTheoremToEventFlow y → x = y) ∧
          monotoneSubsequenceTheoremEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact monotoneSubsequenceTheoremDecode_encode_bhist
  · constructor
    · exact monotoneSubsequenceTheorem_round_trip
    · constructor
      · intro x y heq
        exact monotoneSubsequenceTheoremToEventFlow_injective heq
      · rfl

end BEDC.Derived.MonotoneSubsequenceTheoremUp.TasteGate
