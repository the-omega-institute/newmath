import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyTailEnvelopeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyTailEnvelopeUp : Type where
  | mk : (S U D W R Q H C P N : BHist) → RegularCauchyTailEnvelopeUp
  deriving DecidableEq

def regularCauchyTailEnvelopeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyTailEnvelopeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyTailEnvelopeEncodeBHist h

def regularCauchyTailEnvelopeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyTailEnvelopeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyTailEnvelopeDecodeBHist tail)

private theorem regularCauchyTailEnvelopeDecode_encode :
    ∀ h : BHist,
      regularCauchyTailEnvelopeDecodeBHist
        (regularCauchyTailEnvelopeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyTailEnvelopeFields :
    RegularCauchyTailEnvelopeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyTailEnvelopeUp.mk S U D W R Q H C P N =>
      [S, U, D, W, R, Q, H, C, P, N]

def regularCauchyTailEnvelopeToEventFlow :
    RegularCauchyTailEnvelopeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyTailEnvelopeFields x).map
      regularCauchyTailEnvelopeEncodeBHist

private def regularCauchyTailEnvelopeEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      regularCauchyTailEnvelopeEventAtDefault index rest

def regularCauchyTailEnvelopeFromEventFlow
    (ef : EventFlow) : Option RegularCauchyTailEnvelopeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyTailEnvelopeUp.mk
      (regularCauchyTailEnvelopeDecodeBHist
        (regularCauchyTailEnvelopeEventAtDefault 0 ef))
      (regularCauchyTailEnvelopeDecodeBHist
        (regularCauchyTailEnvelopeEventAtDefault 1 ef))
      (regularCauchyTailEnvelopeDecodeBHist
        (regularCauchyTailEnvelopeEventAtDefault 2 ef))
      (regularCauchyTailEnvelopeDecodeBHist
        (regularCauchyTailEnvelopeEventAtDefault 3 ef))
      (regularCauchyTailEnvelopeDecodeBHist
        (regularCauchyTailEnvelopeEventAtDefault 4 ef))
      (regularCauchyTailEnvelopeDecodeBHist
        (regularCauchyTailEnvelopeEventAtDefault 5 ef))
      (regularCauchyTailEnvelopeDecodeBHist
        (regularCauchyTailEnvelopeEventAtDefault 6 ef))
      (regularCauchyTailEnvelopeDecodeBHist
        (regularCauchyTailEnvelopeEventAtDefault 7 ef))
      (regularCauchyTailEnvelopeDecodeBHist
        (regularCauchyTailEnvelopeEventAtDefault 8 ef))
      (regularCauchyTailEnvelopeDecodeBHist
        (regularCauchyTailEnvelopeEventAtDefault 9 ef)))

private theorem regularCauchyTailEnvelope_round_trip :
    ∀ x : RegularCauchyTailEnvelopeUp,
      regularCauchyTailEnvelopeFromEventFlow
        (regularCauchyTailEnvelopeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S U D W R Q H C P N =>
      change
        some
          (RegularCauchyTailEnvelopeUp.mk
            (regularCauchyTailEnvelopeDecodeBHist
              (regularCauchyTailEnvelopeEncodeBHist S))
            (regularCauchyTailEnvelopeDecodeBHist
              (regularCauchyTailEnvelopeEncodeBHist U))
            (regularCauchyTailEnvelopeDecodeBHist
              (regularCauchyTailEnvelopeEncodeBHist D))
            (regularCauchyTailEnvelopeDecodeBHist
              (regularCauchyTailEnvelopeEncodeBHist W))
            (regularCauchyTailEnvelopeDecodeBHist
              (regularCauchyTailEnvelopeEncodeBHist R))
            (regularCauchyTailEnvelopeDecodeBHist
              (regularCauchyTailEnvelopeEncodeBHist Q))
            (regularCauchyTailEnvelopeDecodeBHist
              (regularCauchyTailEnvelopeEncodeBHist H))
            (regularCauchyTailEnvelopeDecodeBHist
              (regularCauchyTailEnvelopeEncodeBHist C))
            (regularCauchyTailEnvelopeDecodeBHist
              (regularCauchyTailEnvelopeEncodeBHist P))
            (regularCauchyTailEnvelopeDecodeBHist
              (regularCauchyTailEnvelopeEncodeBHist N))) =
          some (RegularCauchyTailEnvelopeUp.mk S U D W R Q H C P N)
      rw [regularCauchyTailEnvelopeDecode_encode S,
        regularCauchyTailEnvelopeDecode_encode U,
        regularCauchyTailEnvelopeDecode_encode D,
        regularCauchyTailEnvelopeDecode_encode W,
        regularCauchyTailEnvelopeDecode_encode R,
        regularCauchyTailEnvelopeDecode_encode Q,
        regularCauchyTailEnvelopeDecode_encode H,
        regularCauchyTailEnvelopeDecode_encode C,
        regularCauchyTailEnvelopeDecode_encode P,
        regularCauchyTailEnvelopeDecode_encode N]

private theorem regularCauchyTailEnvelopeToEventFlow_injective
    {x y : RegularCauchyTailEnvelopeUp} :
    regularCauchyTailEnvelopeToEventFlow x =
      regularCauchyTailEnvelopeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyTailEnvelopeFromEventFlow
          (regularCauchyTailEnvelopeToEventFlow x) =
        regularCauchyTailEnvelopeFromEventFlow
          (regularCauchyTailEnvelopeToEventFlow y) :=
    congrArg regularCauchyTailEnvelopeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyTailEnvelope_round_trip x).symm
      (Eq.trans hread (regularCauchyTailEnvelope_round_trip y)))

instance regularCauchyTailEnvelopeBHistCarrier :
    BHistCarrier RegularCauchyTailEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyTailEnvelopeToEventFlow
  fromEventFlow := regularCauchyTailEnvelopeFromEventFlow

instance regularCauchyTailEnvelopeChapterTasteGate :
    ChapterTasteGate RegularCauchyTailEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyTailEnvelopeFromEventFlow
        (regularCauchyTailEnvelopeToEventFlow x) = some x
    exact regularCauchyTailEnvelope_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyTailEnvelopeToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyTailEnvelopeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyTailEnvelopeChapterTasteGate

theorem RegularCauchyTailEnvelopeTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyTailEnvelopeDecodeBHist
        (regularCauchyTailEnvelopeEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyTailEnvelopeUp,
        regularCauchyTailEnvelopeFromEventFlow
          (regularCauchyTailEnvelopeToEventFlow x) = some x) ∧
      (∀ x y : RegularCauchyTailEnvelopeUp,
        regularCauchyTailEnvelopeToEventFlow x =
          regularCauchyTailEnvelopeToEventFlow y → x = y) ∧
      regularCauchyTailEnvelopeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨regularCauchyTailEnvelopeDecode_encode,
      regularCauchyTailEnvelope_round_trip,
      fun _ _ heq => regularCauchyTailEnvelopeToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.RegularCauchyTailEnvelopeUp
