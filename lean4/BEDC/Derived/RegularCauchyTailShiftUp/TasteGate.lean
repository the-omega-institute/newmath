import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyTailShiftUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyTailShiftUp : Type where
  | mk (W Q D L H C P N : BHist) : RegularCauchyTailShiftUp
  deriving DecidableEq

def regularCauchyTailShiftEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyTailShiftEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyTailShiftEncodeBHist h

def regularCauchyTailShiftDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyTailShiftDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyTailShiftDecodeBHist tail)

private theorem regularCauchyTailShift_decode_encode_bhist :
    ∀ h : BHist,
      regularCauchyTailShiftDecodeBHist (regularCauchyTailShiftEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def regularCauchyTailShiftToEventFlow : RegularCauchyTailShiftUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyTailShiftUp.mk W Q D L H C P N =>
      [[BMark.b0],
        regularCauchyTailShiftEncodeBHist W,
        [BMark.b1, BMark.b0],
        regularCauchyTailShiftEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b0],
        regularCauchyTailShiftEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyTailShiftEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyTailShiftEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyTailShiftEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyTailShiftEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        regularCauchyTailShiftEncodeBHist N]

private def regularCauchyTailShiftEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyTailShiftEventAt index rest

def regularCauchyTailShiftFromEventFlow (ef : EventFlow) : Option RegularCauchyTailShiftUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyTailShiftUp.mk
      (regularCauchyTailShiftDecodeBHist (regularCauchyTailShiftEventAt 1 ef))
      (regularCauchyTailShiftDecodeBHist (regularCauchyTailShiftEventAt 3 ef))
      (regularCauchyTailShiftDecodeBHist (regularCauchyTailShiftEventAt 5 ef))
      (regularCauchyTailShiftDecodeBHist (regularCauchyTailShiftEventAt 7 ef))
      (regularCauchyTailShiftDecodeBHist (regularCauchyTailShiftEventAt 9 ef))
      (regularCauchyTailShiftDecodeBHist (regularCauchyTailShiftEventAt 11 ef))
      (regularCauchyTailShiftDecodeBHist (regularCauchyTailShiftEventAt 13 ef))
      (regularCauchyTailShiftDecodeBHist (regularCauchyTailShiftEventAt 15 ef)))

private theorem regularCauchyTailShift_round_trip :
    ∀ x : RegularCauchyTailShiftUp,
      regularCauchyTailShiftFromEventFlow (regularCauchyTailShiftToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk W Q D L H C P N =>
      change
        some
          (RegularCauchyTailShiftUp.mk
            (regularCauchyTailShiftDecodeBHist (regularCauchyTailShiftEncodeBHist W))
            (regularCauchyTailShiftDecodeBHist (regularCauchyTailShiftEncodeBHist Q))
            (regularCauchyTailShiftDecodeBHist (regularCauchyTailShiftEncodeBHist D))
            (regularCauchyTailShiftDecodeBHist (regularCauchyTailShiftEncodeBHist L))
            (regularCauchyTailShiftDecodeBHist (regularCauchyTailShiftEncodeBHist H))
            (regularCauchyTailShiftDecodeBHist (regularCauchyTailShiftEncodeBHist C))
            (regularCauchyTailShiftDecodeBHist (regularCauchyTailShiftEncodeBHist P))
            (regularCauchyTailShiftDecodeBHist (regularCauchyTailShiftEncodeBHist N))) =
          some (RegularCauchyTailShiftUp.mk W Q D L H C P N)
      rw [regularCauchyTailShift_decode_encode_bhist W,
        regularCauchyTailShift_decode_encode_bhist Q,
        regularCauchyTailShift_decode_encode_bhist D,
        regularCauchyTailShift_decode_encode_bhist L,
        regularCauchyTailShift_decode_encode_bhist H,
        regularCauchyTailShift_decode_encode_bhist C,
        regularCauchyTailShift_decode_encode_bhist P,
        regularCauchyTailShift_decode_encode_bhist N]

private theorem regularCauchyTailShiftToEventFlow_injective {x y : RegularCauchyTailShiftUp} :
    regularCauchyTailShiftToEventFlow x = regularCauchyTailShiftToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyTailShiftFromEventFlow (regularCauchyTailShiftToEventFlow x) =
        regularCauchyTailShiftFromEventFlow (regularCauchyTailShiftToEventFlow y) :=
    congrArg regularCauchyTailShiftFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyTailShift_round_trip x).symm
      (Eq.trans hread (regularCauchyTailShift_round_trip y)))

instance regularCauchyTailShiftBHistCarrier : BHistCarrier RegularCauchyTailShiftUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyTailShiftToEventFlow
  fromEventFlow := regularCauchyTailShiftFromEventFlow

instance regularCauchyTailShiftChapterTasteGate :
    ChapterTasteGate RegularCauchyTailShiftUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyTailShiftFromEventFlow (regularCauchyTailShiftToEventFlow x) = some x
    exact regularCauchyTailShift_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyTailShiftToEventFlow_injective heq)

theorem RegularCauchyTailShiftTasteGate_single_carrier_alignment :
    (∃ carrier : BHistCarrier RegularCauchyTailShiftUp,
        Nonempty (@ChapterTasteGate RegularCauchyTailShiftUp carrier)) ∧
      (∀ h : BHist,
        regularCauchyTailShiftDecodeBHist (regularCauchyTailShiftEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyTailShiftUp,
        regularCauchyTailShiftFromEventFlow (regularCauchyTailShiftToEventFlow x) = some x) ∧
      regularCauchyTailShiftEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨regularCauchyTailShiftBHistCarrier, ⟨regularCauchyTailShiftChapterTasteGate⟩⟩
  · constructor
    · exact regularCauchyTailShift_decode_encode_bhist
    · constructor
      · exact regularCauchyTailShift_round_trip
      · rfl

end BEDC.Derived.RegularCauchyTailShiftUp
