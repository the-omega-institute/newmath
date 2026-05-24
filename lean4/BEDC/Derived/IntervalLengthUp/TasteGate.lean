import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.IntervalLengthUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive IntervalLengthUp : Type where
  | mk (L R O D E H C P N : BHist) : IntervalLengthUp
  deriving DecidableEq

def intervalLengthEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: intervalLengthEncodeBHist h
  | BHist.e1 h => BMark.b1 :: intervalLengthEncodeBHist h

def intervalLengthDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (intervalLengthDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (intervalLengthDecodeBHist tail)

private theorem intervalLength_decode_encode_bhist :
    forall h : BHist, intervalLengthDecodeBHist (intervalLengthEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def intervalLengthFields : IntervalLengthUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | IntervalLengthUp.mk L R O D E H C P N => [L, R, O, D, E, H, C, P, N]

def intervalLengthToEventFlow : IntervalLengthUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (intervalLengthFields x).map intervalLengthEncodeBHist

private def intervalLengthEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => intervalLengthEventAtDefault index rest

def intervalLengthFromEventFlow (ef : EventFlow) : Option IntervalLengthUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (IntervalLengthUp.mk
      (intervalLengthDecodeBHist (intervalLengthEventAtDefault 0 ef))
      (intervalLengthDecodeBHist (intervalLengthEventAtDefault 1 ef))
      (intervalLengthDecodeBHist (intervalLengthEventAtDefault 2 ef))
      (intervalLengthDecodeBHist (intervalLengthEventAtDefault 3 ef))
      (intervalLengthDecodeBHist (intervalLengthEventAtDefault 4 ef))
      (intervalLengthDecodeBHist (intervalLengthEventAtDefault 5 ef))
      (intervalLengthDecodeBHist (intervalLengthEventAtDefault 6 ef))
      (intervalLengthDecodeBHist (intervalLengthEventAtDefault 7 ef))
      (intervalLengthDecodeBHist (intervalLengthEventAtDefault 8 ef)))

private theorem intervalLength_round_trip :
    forall x : IntervalLengthUp, intervalLengthFromEventFlow (intervalLengthToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L R O D E H C P N =>
      change
        some
          (IntervalLengthUp.mk
            (intervalLengthDecodeBHist (intervalLengthEncodeBHist L))
            (intervalLengthDecodeBHist (intervalLengthEncodeBHist R))
            (intervalLengthDecodeBHist (intervalLengthEncodeBHist O))
            (intervalLengthDecodeBHist (intervalLengthEncodeBHist D))
            (intervalLengthDecodeBHist (intervalLengthEncodeBHist E))
            (intervalLengthDecodeBHist (intervalLengthEncodeBHist H))
            (intervalLengthDecodeBHist (intervalLengthEncodeBHist C))
            (intervalLengthDecodeBHist (intervalLengthEncodeBHist P))
            (intervalLengthDecodeBHist (intervalLengthEncodeBHist N))) =
          some (IntervalLengthUp.mk L R O D E H C P N)
      rw [intervalLength_decode_encode_bhist L,
        intervalLength_decode_encode_bhist R,
        intervalLength_decode_encode_bhist O,
        intervalLength_decode_encode_bhist D,
        intervalLength_decode_encode_bhist E,
        intervalLength_decode_encode_bhist H,
        intervalLength_decode_encode_bhist C,
        intervalLength_decode_encode_bhist P,
        intervalLength_decode_encode_bhist N]

private theorem intervalLengthToEventFlow_injective {x y : IntervalLengthUp} :
    intervalLengthToEventFlow x = intervalLengthToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      intervalLengthFromEventFlow (intervalLengthToEventFlow x) =
        intervalLengthFromEventFlow (intervalLengthToEventFlow y) :=
    congrArg intervalLengthFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (intervalLength_round_trip x).symm
      (Eq.trans hread (intervalLength_round_trip y)))

instance intervalLengthBHistCarrier : BHistCarrier IntervalLengthUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := intervalLengthToEventFlow
  fromEventFlow := intervalLengthFromEventFlow

instance intervalLengthChapterTasteGate : ChapterTasteGate IntervalLengthUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change intervalLengthFromEventFlow (intervalLengthToEventFlow x) = some x
    exact intervalLength_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (intervalLengthToEventFlow_injective heq)

def taste_gate : ChapterTasteGate IntervalLengthUp :=
  -- BEDC touchpoint anchor: BHist BMark
  intervalLengthChapterTasteGate

theorem IntervalLengthTasteGate_single_carrier_alignment :
    (forall h : BHist, intervalLengthDecodeBHist (intervalLengthEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier IntervalLengthUp) ∧
        Nonempty (ChapterTasteGate IntervalLengthUp) ∧
          intervalLengthEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨intervalLength_decode_encode_bhist,
      ⟨intervalLengthBHistCarrier⟩,
      ⟨intervalLengthChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.IntervalLengthUp
