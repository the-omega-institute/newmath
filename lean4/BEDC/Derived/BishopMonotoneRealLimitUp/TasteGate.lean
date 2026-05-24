import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopMonotoneRealLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopMonotoneRealLimitUp : Type where
  | mk
      (sequence bound monotone located dyadic readback realSeal transport replay provenance
        name : BHist) :
      BishopMonotoneRealLimitUp
  deriving DecidableEq

def bishopMonotoneRealLimitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopMonotoneRealLimitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopMonotoneRealLimitEncodeBHist h

def bishopMonotoneRealLimitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopMonotoneRealLimitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopMonotoneRealLimitDecodeBHist tail)

private theorem bishopMonotoneRealLimit_decode_encode :
    ∀ h : BHist,
      bishopMonotoneRealLimitDecodeBHist (bishopMonotoneRealLimitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopMonotoneRealLimitFields : BishopMonotoneRealLimitUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopMonotoneRealLimitUp.mk sequence bound monotone located dyadic readback realSeal
      transport replay provenance name =>
      [sequence, bound, monotone, located, dyadic, readback, realSeal, transport, replay,
        provenance, name]

def bishopMonotoneRealLimitToEventFlow : BishopMonotoneRealLimitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bishopMonotoneRealLimitFields x).map bishopMonotoneRealLimitEncodeBHist

private def bishopMonotoneRealLimitEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopMonotoneRealLimitEventAtDefault index rest

def bishopMonotoneRealLimitFromEventFlow
    (ef : EventFlow) : Option BishopMonotoneRealLimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopMonotoneRealLimitUp.mk
      (bishopMonotoneRealLimitDecodeBHist (bishopMonotoneRealLimitEventAtDefault 0 ef))
      (bishopMonotoneRealLimitDecodeBHist (bishopMonotoneRealLimitEventAtDefault 1 ef))
      (bishopMonotoneRealLimitDecodeBHist (bishopMonotoneRealLimitEventAtDefault 2 ef))
      (bishopMonotoneRealLimitDecodeBHist (bishopMonotoneRealLimitEventAtDefault 3 ef))
      (bishopMonotoneRealLimitDecodeBHist (bishopMonotoneRealLimitEventAtDefault 4 ef))
      (bishopMonotoneRealLimitDecodeBHist (bishopMonotoneRealLimitEventAtDefault 5 ef))
      (bishopMonotoneRealLimitDecodeBHist (bishopMonotoneRealLimitEventAtDefault 6 ef))
      (bishopMonotoneRealLimitDecodeBHist (bishopMonotoneRealLimitEventAtDefault 7 ef))
      (bishopMonotoneRealLimitDecodeBHist (bishopMonotoneRealLimitEventAtDefault 8 ef))
      (bishopMonotoneRealLimitDecodeBHist (bishopMonotoneRealLimitEventAtDefault 9 ef))
      (bishopMonotoneRealLimitDecodeBHist (bishopMonotoneRealLimitEventAtDefault 10 ef)))

private theorem bishopMonotoneRealLimit_round_trip :
    ∀ x : BishopMonotoneRealLimitUp,
      bishopMonotoneRealLimitFromEventFlow (bishopMonotoneRealLimitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk sequence bound monotone located dyadic readback realSeal transport replay provenance name =>
      change
        some
          (BishopMonotoneRealLimitUp.mk
            (bishopMonotoneRealLimitDecodeBHist
              (bishopMonotoneRealLimitEncodeBHist sequence))
            (bishopMonotoneRealLimitDecodeBHist
              (bishopMonotoneRealLimitEncodeBHist bound))
            (bishopMonotoneRealLimitDecodeBHist
              (bishopMonotoneRealLimitEncodeBHist monotone))
            (bishopMonotoneRealLimitDecodeBHist
              (bishopMonotoneRealLimitEncodeBHist located))
            (bishopMonotoneRealLimitDecodeBHist
              (bishopMonotoneRealLimitEncodeBHist dyadic))
            (bishopMonotoneRealLimitDecodeBHist
              (bishopMonotoneRealLimitEncodeBHist readback))
            (bishopMonotoneRealLimitDecodeBHist
              (bishopMonotoneRealLimitEncodeBHist realSeal))
            (bishopMonotoneRealLimitDecodeBHist
              (bishopMonotoneRealLimitEncodeBHist transport))
            (bishopMonotoneRealLimitDecodeBHist
              (bishopMonotoneRealLimitEncodeBHist replay))
            (bishopMonotoneRealLimitDecodeBHist
              (bishopMonotoneRealLimitEncodeBHist provenance))
            (bishopMonotoneRealLimitDecodeBHist
              (bishopMonotoneRealLimitEncodeBHist name))) =
          some
            (BishopMonotoneRealLimitUp.mk sequence bound monotone located dyadic readback
              realSeal transport replay provenance name)
      rw [bishopMonotoneRealLimit_decode_encode sequence,
        bishopMonotoneRealLimit_decode_encode bound,
        bishopMonotoneRealLimit_decode_encode monotone,
        bishopMonotoneRealLimit_decode_encode located,
        bishopMonotoneRealLimit_decode_encode dyadic,
        bishopMonotoneRealLimit_decode_encode readback,
        bishopMonotoneRealLimit_decode_encode realSeal,
        bishopMonotoneRealLimit_decode_encode transport,
        bishopMonotoneRealLimit_decode_encode replay,
        bishopMonotoneRealLimit_decode_encode provenance,
        bishopMonotoneRealLimit_decode_encode name]

private theorem bishopMonotoneRealLimitToEventFlow_injective
    {x y : BishopMonotoneRealLimitUp} :
    bishopMonotoneRealLimitToEventFlow x = bishopMonotoneRealLimitToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopMonotoneRealLimitFromEventFlow (bishopMonotoneRealLimitToEventFlow x) =
        bishopMonotoneRealLimitFromEventFlow (bishopMonotoneRealLimitToEventFlow y) :=
    congrArg bishopMonotoneRealLimitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bishopMonotoneRealLimit_round_trip x).symm
      (Eq.trans hread (bishopMonotoneRealLimit_round_trip y)))

instance bishopMonotoneRealLimitBHistCarrier :
    BHistCarrier BishopMonotoneRealLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopMonotoneRealLimitToEventFlow
  fromEventFlow := bishopMonotoneRealLimitFromEventFlow

instance bishopMonotoneRealLimitChapterTasteGate :
    ChapterTasteGate BishopMonotoneRealLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopMonotoneRealLimitFromEventFlow (bishopMonotoneRealLimitToEventFlow x) =
      some x
    exact bishopMonotoneRealLimit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bishopMonotoneRealLimitToEventFlow_injective heq)

theorem BishopMonotoneRealLimitTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      bishopMonotoneRealLimitDecodeBHist (bishopMonotoneRealLimitEncodeBHist h) = h) ∧
      (∀ x : BishopMonotoneRealLimitUp,
        bishopMonotoneRealLimitFromEventFlow (bishopMonotoneRealLimitToEventFlow x) =
          some x) ∧
        (∀ x y : BishopMonotoneRealLimitUp,
          bishopMonotoneRealLimitToEventFlow x = bishopMonotoneRealLimitToEventFlow y →
            x = y) ∧
          bishopMonotoneRealLimitEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact bishopMonotoneRealLimit_decode_encode
  · constructor
    · exact bishopMonotoneRealLimit_round_trip
    · constructor
      · intro x y heq
        exact bishopMonotoneRealLimitToEventFlow_injective heq
      · rfl

end BEDC.Derived.BishopMonotoneRealLimitUp
