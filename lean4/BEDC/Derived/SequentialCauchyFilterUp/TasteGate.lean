import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SequentialCauchyFilterUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SequentialCauchyFilterUp : Type where
  | mk (S B Q D G R E H C P N : BHist) : SequentialCauchyFilterUp
  deriving DecidableEq

def sequentialCauchyFilterFields : SequentialCauchyFilterUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SequentialCauchyFilterUp.mk S B Q D G R E H C P N => [S, B, Q, D, G, R, E, H, C, P, N]

def sequentialCauchyFilterEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sequentialCauchyFilterEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sequentialCauchyFilterEncodeBHist h

def sequentialCauchyFilterDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sequentialCauchyFilterDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sequentialCauchyFilterDecodeBHist tail)

private theorem sequentialCauchyFilter_decode_encode_bhist :
    ∀ h : BHist,
      sequentialCauchyFilterDecodeBHist (sequentialCauchyFilterEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def sequentialCauchyFilterToEventFlow : SequentialCauchyFilterUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (sequentialCauchyFilterFields x).map sequentialCauchyFilterEncodeBHist

private def sequentialCauchyFilterEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => sequentialCauchyFilterEventAtDefault index rest

def sequentialCauchyFilterFromEventFlow
    (ef : EventFlow) : Option SequentialCauchyFilterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SequentialCauchyFilterUp.mk
      (sequentialCauchyFilterDecodeBHist (sequentialCauchyFilterEventAtDefault 0 ef))
      (sequentialCauchyFilterDecodeBHist (sequentialCauchyFilterEventAtDefault 1 ef))
      (sequentialCauchyFilterDecodeBHist (sequentialCauchyFilterEventAtDefault 2 ef))
      (sequentialCauchyFilterDecodeBHist (sequentialCauchyFilterEventAtDefault 3 ef))
      (sequentialCauchyFilterDecodeBHist (sequentialCauchyFilterEventAtDefault 4 ef))
      (sequentialCauchyFilterDecodeBHist (sequentialCauchyFilterEventAtDefault 5 ef))
      (sequentialCauchyFilterDecodeBHist (sequentialCauchyFilterEventAtDefault 6 ef))
      (sequentialCauchyFilterDecodeBHist (sequentialCauchyFilterEventAtDefault 7 ef))
      (sequentialCauchyFilterDecodeBHist (sequentialCauchyFilterEventAtDefault 8 ef))
      (sequentialCauchyFilterDecodeBHist (sequentialCauchyFilterEventAtDefault 9 ef))
      (sequentialCauchyFilterDecodeBHist (sequentialCauchyFilterEventAtDefault 10 ef)))

private theorem sequentialCauchyFilter_round_trip :
    ∀ x : SequentialCauchyFilterUp,
      sequentialCauchyFilterFromEventFlow (sequentialCauchyFilterToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S B Q D G R E H C P N =>
      change
        some
          (SequentialCauchyFilterUp.mk
            (sequentialCauchyFilterDecodeBHist (sequentialCauchyFilterEncodeBHist S))
            (sequentialCauchyFilterDecodeBHist (sequentialCauchyFilterEncodeBHist B))
            (sequentialCauchyFilterDecodeBHist (sequentialCauchyFilterEncodeBHist Q))
            (sequentialCauchyFilterDecodeBHist (sequentialCauchyFilterEncodeBHist D))
            (sequentialCauchyFilterDecodeBHist (sequentialCauchyFilterEncodeBHist G))
            (sequentialCauchyFilterDecodeBHist (sequentialCauchyFilterEncodeBHist R))
            (sequentialCauchyFilterDecodeBHist (sequentialCauchyFilterEncodeBHist E))
            (sequentialCauchyFilterDecodeBHist (sequentialCauchyFilterEncodeBHist H))
            (sequentialCauchyFilterDecodeBHist (sequentialCauchyFilterEncodeBHist C))
            (sequentialCauchyFilterDecodeBHist (sequentialCauchyFilterEncodeBHist P))
            (sequentialCauchyFilterDecodeBHist (sequentialCauchyFilterEncodeBHist N))) =
          some (SequentialCauchyFilterUp.mk S B Q D G R E H C P N)
      rw [sequentialCauchyFilter_decode_encode_bhist S,
        sequentialCauchyFilter_decode_encode_bhist B,
        sequentialCauchyFilter_decode_encode_bhist Q,
        sequentialCauchyFilter_decode_encode_bhist D,
        sequentialCauchyFilter_decode_encode_bhist G,
        sequentialCauchyFilter_decode_encode_bhist R,
        sequentialCauchyFilter_decode_encode_bhist E,
        sequentialCauchyFilter_decode_encode_bhist H,
        sequentialCauchyFilter_decode_encode_bhist C,
        sequentialCauchyFilter_decode_encode_bhist P,
        sequentialCauchyFilter_decode_encode_bhist N]

private theorem sequentialCauchyFilterToEventFlow_injective
    {x y : SequentialCauchyFilterUp} :
    sequentialCauchyFilterToEventFlow x = sequentialCauchyFilterToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sequentialCauchyFilterFromEventFlow (sequentialCauchyFilterToEventFlow x) =
        sequentialCauchyFilterFromEventFlow (sequentialCauchyFilterToEventFlow y) :=
    congrArg sequentialCauchyFilterFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (sequentialCauchyFilter_round_trip x).symm
      (Eq.trans hread (sequentialCauchyFilter_round_trip y)))

instance sequentialCauchyFilterBHistCarrier : BHistCarrier SequentialCauchyFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sequentialCauchyFilterToEventFlow
  fromEventFlow := sequentialCauchyFilterFromEventFlow

instance sequentialCauchyFilterChapterTasteGate :
    ChapterTasteGate SequentialCauchyFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change sequentialCauchyFilterFromEventFlow (sequentialCauchyFilterToEventFlow x) = some x
    exact sequentialCauchyFilter_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (sequentialCauchyFilterToEventFlow_injective heq)

theorem SequentialCauchyFilterTasteGate_single_carrier_alignment :
    (∀ h : BHist, sequentialCauchyFilterDecodeBHist (sequentialCauchyFilterEncodeBHist h) = h) ∧
      (∀ x : SequentialCauchyFilterUp,
        sequentialCauchyFilterFromEventFlow (sequentialCauchyFilterToEventFlow x) = some x) ∧
        (∀ x y : SequentialCauchyFilterUp,
          sequentialCauchyFilterToEventFlow x = sequentialCauchyFilterToEventFlow y → x = y) ∧
          sequentialCauchyFilterEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨sequentialCauchyFilter_decode_encode_bhist,
      sequentialCauchyFilter_round_trip,
      (fun _ _ heq => sequentialCauchyFilterToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.SequentialCauchyFilterUp
