import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RationalIntervalSubdivisionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RationalIntervalSubdivisionUp : Type where
  | mk
      (source endpoints mesh width window handoff transport replay provenance name :
        BHist) : RationalIntervalSubdivisionUp
  deriving DecidableEq

def rationalIntervalSubdivisionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: rationalIntervalSubdivisionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: rationalIntervalSubdivisionEncodeBHist h

def rationalIntervalSubdivisionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (rationalIntervalSubdivisionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (rationalIntervalSubdivisionDecodeBHist tail)

private theorem rationalIntervalSubdivisionDecode_encode_bhist :
    ∀ h : BHist,
      rationalIntervalSubdivisionDecodeBHist
        (rationalIntervalSubdivisionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def rationalIntervalSubdivisionToEventFlow : RationalIntervalSubdivisionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RationalIntervalSubdivisionUp.mk source endpoints mesh width window handoff transport replay
      provenance name =>
      [[BMark.b0],
        rationalIntervalSubdivisionEncodeBHist source,
        [BMark.b1, BMark.b0],
        rationalIntervalSubdivisionEncodeBHist endpoints,
        [BMark.b1, BMark.b1, BMark.b0],
        rationalIntervalSubdivisionEncodeBHist mesh,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        rationalIntervalSubdivisionEncodeBHist width,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        rationalIntervalSubdivisionEncodeBHist window,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        rationalIntervalSubdivisionEncodeBHist handoff,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        rationalIntervalSubdivisionEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        rationalIntervalSubdivisionEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        rationalIntervalSubdivisionEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        rationalIntervalSubdivisionEncodeBHist name]

private def rationalIntervalSubdivisionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => rationalIntervalSubdivisionEventAtDefault index rest

def rationalIntervalSubdivisionFromEventFlow
    (ef : EventFlow) : Option RationalIntervalSubdivisionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RationalIntervalSubdivisionUp.mk
      (rationalIntervalSubdivisionDecodeBHist (rationalIntervalSubdivisionEventAtDefault 1 ef))
      (rationalIntervalSubdivisionDecodeBHist (rationalIntervalSubdivisionEventAtDefault 3 ef))
      (rationalIntervalSubdivisionDecodeBHist (rationalIntervalSubdivisionEventAtDefault 5 ef))
      (rationalIntervalSubdivisionDecodeBHist (rationalIntervalSubdivisionEventAtDefault 7 ef))
      (rationalIntervalSubdivisionDecodeBHist (rationalIntervalSubdivisionEventAtDefault 9 ef))
      (rationalIntervalSubdivisionDecodeBHist (rationalIntervalSubdivisionEventAtDefault 11 ef))
      (rationalIntervalSubdivisionDecodeBHist (rationalIntervalSubdivisionEventAtDefault 13 ef))
      (rationalIntervalSubdivisionDecodeBHist (rationalIntervalSubdivisionEventAtDefault 15 ef))
      (rationalIntervalSubdivisionDecodeBHist (rationalIntervalSubdivisionEventAtDefault 17 ef))
      (rationalIntervalSubdivisionDecodeBHist (rationalIntervalSubdivisionEventAtDefault 19 ef)))

private theorem rationalIntervalSubdivision_round_trip :
    ∀ x : RationalIntervalSubdivisionUp,
      rationalIntervalSubdivisionFromEventFlow
        (rationalIntervalSubdivisionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source endpoints mesh width window handoff transport replay provenance name =>
      change
        some
          (RationalIntervalSubdivisionUp.mk
            (rationalIntervalSubdivisionDecodeBHist
              (rationalIntervalSubdivisionEncodeBHist source))
            (rationalIntervalSubdivisionDecodeBHist
              (rationalIntervalSubdivisionEncodeBHist endpoints))
            (rationalIntervalSubdivisionDecodeBHist
              (rationalIntervalSubdivisionEncodeBHist mesh))
            (rationalIntervalSubdivisionDecodeBHist
              (rationalIntervalSubdivisionEncodeBHist width))
            (rationalIntervalSubdivisionDecodeBHist
              (rationalIntervalSubdivisionEncodeBHist window))
            (rationalIntervalSubdivisionDecodeBHist
              (rationalIntervalSubdivisionEncodeBHist handoff))
            (rationalIntervalSubdivisionDecodeBHist
              (rationalIntervalSubdivisionEncodeBHist transport))
            (rationalIntervalSubdivisionDecodeBHist
              (rationalIntervalSubdivisionEncodeBHist replay))
            (rationalIntervalSubdivisionDecodeBHist
              (rationalIntervalSubdivisionEncodeBHist provenance))
            (rationalIntervalSubdivisionDecodeBHist
              (rationalIntervalSubdivisionEncodeBHist name))) =
          some
            (RationalIntervalSubdivisionUp.mk source endpoints mesh width window handoff
              transport replay provenance name)
      rw [rationalIntervalSubdivisionDecode_encode_bhist source,
        rationalIntervalSubdivisionDecode_encode_bhist endpoints,
        rationalIntervalSubdivisionDecode_encode_bhist mesh,
        rationalIntervalSubdivisionDecode_encode_bhist width,
        rationalIntervalSubdivisionDecode_encode_bhist window,
        rationalIntervalSubdivisionDecode_encode_bhist handoff,
        rationalIntervalSubdivisionDecode_encode_bhist transport,
        rationalIntervalSubdivisionDecode_encode_bhist replay,
        rationalIntervalSubdivisionDecode_encode_bhist provenance,
        rationalIntervalSubdivisionDecode_encode_bhist name]

private theorem rationalIntervalSubdivisionToEventFlow_injective
    {x y : RationalIntervalSubdivisionUp} :
    rationalIntervalSubdivisionToEventFlow x = rationalIntervalSubdivisionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      rationalIntervalSubdivisionFromEventFlow (rationalIntervalSubdivisionToEventFlow x) =
        rationalIntervalSubdivisionFromEventFlow (rationalIntervalSubdivisionToEventFlow y) :=
    congrArg rationalIntervalSubdivisionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (rationalIntervalSubdivision_round_trip x).symm
      (Eq.trans hread (rationalIntervalSubdivision_round_trip y)))

instance rationalIntervalSubdivisionBHistCarrier :
    BHistCarrier RationalIntervalSubdivisionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := rationalIntervalSubdivisionToEventFlow
  fromEventFlow := rationalIntervalSubdivisionFromEventFlow

instance rationalIntervalSubdivisionChapterTasteGate :
    ChapterTasteGate RationalIntervalSubdivisionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      rationalIntervalSubdivisionFromEventFlow (rationalIntervalSubdivisionToEventFlow x) =
        some x
    exact rationalIntervalSubdivision_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (rationalIntervalSubdivisionToEventFlow_injective heq)

theorem RationalIntervalSubdivisionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      rationalIntervalSubdivisionDecodeBHist
        (rationalIntervalSubdivisionEncodeBHist h) = h) ∧
      (∀ x : RationalIntervalSubdivisionUp,
        rationalIntervalSubdivisionFromEventFlow
          (rationalIntervalSubdivisionToEventFlow x) = some x) ∧
        (∀ x y : RationalIntervalSubdivisionUp,
          rationalIntervalSubdivisionToEventFlow x =
            rationalIntervalSubdivisionToEventFlow y → x = y) ∧
          rationalIntervalSubdivisionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact rationalIntervalSubdivisionDecode_encode_bhist
  · constructor
    · exact rationalIntervalSubdivision_round_trip
    · constructor
      · intro x y heq
        exact rationalIntervalSubdivisionToEventFlow_injective heq
      · rfl

end BEDC.Derived.RationalIntervalSubdivisionUp
