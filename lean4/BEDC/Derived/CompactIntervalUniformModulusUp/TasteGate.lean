import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactIntervalUniformModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactIntervalUniformModulusUp : Type where
  | mk (D J E S R U Q H C P N : BHist) : CompactIntervalUniformModulusUp
  deriving DecidableEq

def compactIntervalUniformModulusFields :
    CompactIntervalUniformModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactIntervalUniformModulusUp.mk D J E S R U Q H C P N =>
      [D, J, E, S, R, U, Q, H, C, P, N]

def compactIntervalUniformModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactIntervalUniformModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactIntervalUniformModulusEncodeBHist h

def compactIntervalUniformModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactIntervalUniformModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactIntervalUniformModulusDecodeBHist tail)

private theorem compactIntervalUniformModulus_decode_encode_bhist :
    ∀ h : BHist,
      compactIntervalUniformModulusDecodeBHist
        (compactIntervalUniformModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def compactIntervalUniformModulusToEventFlow :
    CompactIntervalUniformModulusUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (compactIntervalUniformModulusFields x).map compactIntervalUniformModulusEncodeBHist

private def compactIntervalUniformModulusEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      compactIntervalUniformModulusEventAtDefault index rest

def compactIntervalUniformModulusFromEventFlow
    (ef : EventFlow) : Option CompactIntervalUniformModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompactIntervalUniformModulusUp.mk
      (compactIntervalUniformModulusDecodeBHist
        (compactIntervalUniformModulusEventAtDefault 0 ef))
      (compactIntervalUniformModulusDecodeBHist
        (compactIntervalUniformModulusEventAtDefault 1 ef))
      (compactIntervalUniformModulusDecodeBHist
        (compactIntervalUniformModulusEventAtDefault 2 ef))
      (compactIntervalUniformModulusDecodeBHist
        (compactIntervalUniformModulusEventAtDefault 3 ef))
      (compactIntervalUniformModulusDecodeBHist
        (compactIntervalUniformModulusEventAtDefault 4 ef))
      (compactIntervalUniformModulusDecodeBHist
        (compactIntervalUniformModulusEventAtDefault 5 ef))
      (compactIntervalUniformModulusDecodeBHist
        (compactIntervalUniformModulusEventAtDefault 6 ef))
      (compactIntervalUniformModulusDecodeBHist
        (compactIntervalUniformModulusEventAtDefault 7 ef))
      (compactIntervalUniformModulusDecodeBHist
        (compactIntervalUniformModulusEventAtDefault 8 ef))
      (compactIntervalUniformModulusDecodeBHist
        (compactIntervalUniformModulusEventAtDefault 9 ef))
      (compactIntervalUniformModulusDecodeBHist
        (compactIntervalUniformModulusEventAtDefault 10 ef)))

private theorem compactIntervalUniformModulus_round_trip :
    ∀ x : CompactIntervalUniformModulusUp,
      compactIntervalUniformModulusFromEventFlow
        (compactIntervalUniformModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D J E S R U Q H C P N =>
      change
        some
          (CompactIntervalUniformModulusUp.mk
            (compactIntervalUniformModulusDecodeBHist
              (compactIntervalUniformModulusEncodeBHist D))
            (compactIntervalUniformModulusDecodeBHist
              (compactIntervalUniformModulusEncodeBHist J))
            (compactIntervalUniformModulusDecodeBHist
              (compactIntervalUniformModulusEncodeBHist E))
            (compactIntervalUniformModulusDecodeBHist
              (compactIntervalUniformModulusEncodeBHist S))
            (compactIntervalUniformModulusDecodeBHist
              (compactIntervalUniformModulusEncodeBHist R))
            (compactIntervalUniformModulusDecodeBHist
              (compactIntervalUniformModulusEncodeBHist U))
            (compactIntervalUniformModulusDecodeBHist
              (compactIntervalUniformModulusEncodeBHist Q))
            (compactIntervalUniformModulusDecodeBHist
              (compactIntervalUniformModulusEncodeBHist H))
            (compactIntervalUniformModulusDecodeBHist
              (compactIntervalUniformModulusEncodeBHist C))
            (compactIntervalUniformModulusDecodeBHist
              (compactIntervalUniformModulusEncodeBHist P))
            (compactIntervalUniformModulusDecodeBHist
              (compactIntervalUniformModulusEncodeBHist N))) =
          some (CompactIntervalUniformModulusUp.mk D J E S R U Q H C P N)
      rw [compactIntervalUniformModulus_decode_encode_bhist D,
        compactIntervalUniformModulus_decode_encode_bhist J,
        compactIntervalUniformModulus_decode_encode_bhist E,
        compactIntervalUniformModulus_decode_encode_bhist S,
        compactIntervalUniformModulus_decode_encode_bhist R,
        compactIntervalUniformModulus_decode_encode_bhist U,
        compactIntervalUniformModulus_decode_encode_bhist Q,
        compactIntervalUniformModulus_decode_encode_bhist H,
        compactIntervalUniformModulus_decode_encode_bhist C,
        compactIntervalUniformModulus_decode_encode_bhist P,
        compactIntervalUniformModulus_decode_encode_bhist N]

private theorem compactIntervalUniformModulusToEventFlow_injective
    {x y : CompactIntervalUniformModulusUp} :
    compactIntervalUniformModulusToEventFlow x =
      compactIntervalUniformModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactIntervalUniformModulusFromEventFlow
          (compactIntervalUniformModulusToEventFlow x) =
        compactIntervalUniformModulusFromEventFlow
          (compactIntervalUniformModulusToEventFlow y) :=
    congrArg compactIntervalUniformModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (compactIntervalUniformModulus_round_trip x).symm
      (Eq.trans hread (compactIntervalUniformModulus_round_trip y)))

instance compactIntervalUniformModulusBHistCarrier :
    BHistCarrier CompactIntervalUniformModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactIntervalUniformModulusToEventFlow
  fromEventFlow := compactIntervalUniformModulusFromEventFlow

instance compactIntervalUniformModulusChapterTasteGate :
    ChapterTasteGate CompactIntervalUniformModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactIntervalUniformModulusFromEventFlow
          (compactIntervalUniformModulusToEventFlow x) =
        some x
    exact compactIntervalUniformModulus_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactIntervalUniformModulusToEventFlow_injective heq)

instance compactIntervalUniformModulusFieldFaithful :
    FieldFaithful CompactIntervalUniformModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := compactIntervalUniformModulusFields
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y hfields
    cases x with
    | mk D J E S R U Q H C P N =>
      cases y with
      | mk D' J' E' S' R' U' Q' H' C' P' N' =>
          cases hfields
          rfl

def taste_gate : ChapterTasteGate CompactIntervalUniformModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactIntervalUniformModulusChapterTasteGate

theorem CompactIntervalUniformModulusTasteGate_single_carrier_alignment :
    (forall h : BHist,
      compactIntervalUniformModulusDecodeBHist
        (compactIntervalUniformModulusEncodeBHist h) = h) /\
      (forall x : CompactIntervalUniformModulusUp,
        compactIntervalUniformModulusFromEventFlow
          (compactIntervalUniformModulusToEventFlow x) = some x) /\
      (forall x y : CompactIntervalUniformModulusUp,
        compactIntervalUniformModulusToEventFlow x =
          compactIntervalUniformModulusToEventFlow y -> x = y) /\
      compactIntervalUniformModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact compactIntervalUniformModulus_decode_encode_bhist
  · constructor
    · exact compactIntervalUniformModulus_round_trip
    · constructor
      · intro x y heq
        exact compactIntervalUniformModulusToEventFlow_injective heq
      · rfl

end BEDC.Derived.CompactIntervalUniformModulusUp
