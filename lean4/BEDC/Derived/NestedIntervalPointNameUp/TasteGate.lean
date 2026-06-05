import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NestedIntervalPointNameUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NestedIntervalPointNameUp : Type where
  | mk
      (interval chain intersection schedule readback realSeal transport replay provenance name :
        BHist) : NestedIntervalPointNameUp
  deriving DecidableEq

def nestedIntervalPointNameEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: nestedIntervalPointNameEncodeBHist h
  | BHist.e1 h => BMark.b1 :: nestedIntervalPointNameEncodeBHist h

def nestedIntervalPointNameDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (nestedIntervalPointNameDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (nestedIntervalPointNameDecodeBHist tail)

private theorem nestedIntervalPointNameDecode_encode_bhist :
    ∀ h : BHist, nestedIntervalPointNameDecodeBHist
      (nestedIntervalPointNameEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def nestedIntervalPointNameToEventFlow : NestedIntervalPointNameUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | NestedIntervalPointNameUp.mk interval chain intersection schedule readback realSeal transport
      replay provenance name =>
      [[BMark.b0],
        nestedIntervalPointNameEncodeBHist interval,
        [BMark.b1, BMark.b0],
        nestedIntervalPointNameEncodeBHist chain,
        [BMark.b1, BMark.b1, BMark.b0],
        nestedIntervalPointNameEncodeBHist intersection,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        nestedIntervalPointNameEncodeBHist schedule,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        nestedIntervalPointNameEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        nestedIntervalPointNameEncodeBHist realSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        nestedIntervalPointNameEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        nestedIntervalPointNameEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        nestedIntervalPointNameEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        nestedIntervalPointNameEncodeBHist name]

private def nestedIntervalPointNameEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => nestedIntervalPointNameEventAtDefault index rest

def nestedIntervalPointNameFromEventFlow
    (ef : EventFlow) : Option NestedIntervalPointNameUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (NestedIntervalPointNameUp.mk
      (nestedIntervalPointNameDecodeBHist (nestedIntervalPointNameEventAtDefault 1 ef))
      (nestedIntervalPointNameDecodeBHist (nestedIntervalPointNameEventAtDefault 3 ef))
      (nestedIntervalPointNameDecodeBHist (nestedIntervalPointNameEventAtDefault 5 ef))
      (nestedIntervalPointNameDecodeBHist (nestedIntervalPointNameEventAtDefault 7 ef))
      (nestedIntervalPointNameDecodeBHist (nestedIntervalPointNameEventAtDefault 9 ef))
      (nestedIntervalPointNameDecodeBHist (nestedIntervalPointNameEventAtDefault 11 ef))
      (nestedIntervalPointNameDecodeBHist (nestedIntervalPointNameEventAtDefault 13 ef))
      (nestedIntervalPointNameDecodeBHist (nestedIntervalPointNameEventAtDefault 15 ef))
      (nestedIntervalPointNameDecodeBHist (nestedIntervalPointNameEventAtDefault 17 ef))
      (nestedIntervalPointNameDecodeBHist (nestedIntervalPointNameEventAtDefault 19 ef)))

private theorem nestedIntervalPointName_round_trip :
    ∀ x : NestedIntervalPointNameUp,
      nestedIntervalPointNameFromEventFlow
        (nestedIntervalPointNameToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk interval chain intersection schedule readback realSeal transport replay provenance name =>
      change
        some
          (NestedIntervalPointNameUp.mk
            (nestedIntervalPointNameDecodeBHist
              (nestedIntervalPointNameEncodeBHist interval))
            (nestedIntervalPointNameDecodeBHist
              (nestedIntervalPointNameEncodeBHist chain))
            (nestedIntervalPointNameDecodeBHist
              (nestedIntervalPointNameEncodeBHist intersection))
            (nestedIntervalPointNameDecodeBHist
              (nestedIntervalPointNameEncodeBHist schedule))
            (nestedIntervalPointNameDecodeBHist
              (nestedIntervalPointNameEncodeBHist readback))
            (nestedIntervalPointNameDecodeBHist
              (nestedIntervalPointNameEncodeBHist realSeal))
            (nestedIntervalPointNameDecodeBHist
              (nestedIntervalPointNameEncodeBHist transport))
            (nestedIntervalPointNameDecodeBHist
              (nestedIntervalPointNameEncodeBHist replay))
            (nestedIntervalPointNameDecodeBHist
              (nestedIntervalPointNameEncodeBHist provenance))
            (nestedIntervalPointNameDecodeBHist
              (nestedIntervalPointNameEncodeBHist name))) =
          some
            (NestedIntervalPointNameUp.mk interval chain intersection schedule  readback realSeal
              transport replay provenance name)
      rw [nestedIntervalPointNameDecode_encode_bhist interval,
        nestedIntervalPointNameDecode_encode_bhist chain,
        nestedIntervalPointNameDecode_encode_bhist intersection,
        nestedIntervalPointNameDecode_encode_bhist schedule,
        nestedIntervalPointNameDecode_encode_bhist readback,
        nestedIntervalPointNameDecode_encode_bhist realSeal,
        nestedIntervalPointNameDecode_encode_bhist transport,
        nestedIntervalPointNameDecode_encode_bhist replay,
        nestedIntervalPointNameDecode_encode_bhist provenance,
        nestedIntervalPointNameDecode_encode_bhist name]

private theorem nestedIntervalPointNameToEventFlow_injective
    {x y : NestedIntervalPointNameUp} :
    nestedIntervalPointNameToEventFlow x = nestedIntervalPointNameToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      nestedIntervalPointNameFromEventFlow (nestedIntervalPointNameToEventFlow x) =
        nestedIntervalPointNameFromEventFlow (nestedIntervalPointNameToEventFlow y) :=
    congrArg nestedIntervalPointNameFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (nestedIntervalPointName_round_trip x).symm
      (Eq.trans hread (nestedIntervalPointName_round_trip y)))

instance nestedIntervalPointNameBHistCarrier :
    BHistCarrier NestedIntervalPointNameUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := nestedIntervalPointNameToEventFlow
  fromEventFlow := nestedIntervalPointNameFromEventFlow

instance nestedIntervalPointNameChapterTasteGate :
    ChapterTasteGate NestedIntervalPointNameUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change nestedIntervalPointNameFromEventFlow (nestedIntervalPointNameToEventFlow x) =
      some x
    exact nestedIntervalPointName_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (nestedIntervalPointNameToEventFlow_injective heq)

theorem NestedIntervalPointNameTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      nestedIntervalPointNameDecodeBHist (nestedIntervalPointNameEncodeBHist h) = h) ∧
      (∀ x : NestedIntervalPointNameUp,
        nestedIntervalPointNameFromEventFlow (nestedIntervalPointNameToEventFlow x) =
          some x) ∧
        (∀ x y : NestedIntervalPointNameUp,
          nestedIntervalPointNameToEventFlow x =
            nestedIntervalPointNameToEventFlow y → x = y) ∧
          nestedIntervalPointNameEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact nestedIntervalPointNameDecode_encode_bhist
  · constructor
    · exact nestedIntervalPointName_round_trip
    · constructor
      · intro x y heq
        exact nestedIntervalPointNameToEventFlow_injective heq
      · rfl

end BEDC.Derived.NestedIntervalPointNameUp
