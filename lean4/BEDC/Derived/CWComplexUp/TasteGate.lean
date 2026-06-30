import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CWComplexUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CWComplexUp : Type where
  | mk (T K E A B C H R P N : BHist) : CWComplexUp
  deriving DecidableEq

def cwComplexEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cwComplexEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cwComplexEncodeBHist h

def cwComplexDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cwComplexDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cwComplexDecodeBHist tail)

private theorem CWComplexTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, cwComplexDecodeBHist (cwComplexEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cwComplexToEventFlow : CWComplexUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CWComplexUp.mk T K E A B C H R P N =>
      [[BMark.b0],
        cwComplexEncodeBHist T,
        [BMark.b1, BMark.b0],
        cwComplexEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b0],
        cwComplexEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cwComplexEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cwComplexEncodeBHist B,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cwComplexEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cwComplexEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        cwComplexEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        cwComplexEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        cwComplexEncodeBHist N]

private def cwComplexEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cwComplexEventAtDefault index rest

def cwComplexFromEventFlow (ef : EventFlow) : Option CWComplexUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CWComplexUp.mk
      (cwComplexDecodeBHist (cwComplexEventAtDefault 1 ef))
      (cwComplexDecodeBHist (cwComplexEventAtDefault 3 ef))
      (cwComplexDecodeBHist (cwComplexEventAtDefault 5 ef))
      (cwComplexDecodeBHist (cwComplexEventAtDefault 7 ef))
      (cwComplexDecodeBHist (cwComplexEventAtDefault 9 ef))
      (cwComplexDecodeBHist (cwComplexEventAtDefault 11 ef))
      (cwComplexDecodeBHist (cwComplexEventAtDefault 13 ef))
      (cwComplexDecodeBHist (cwComplexEventAtDefault 15 ef))
      (cwComplexDecodeBHist (cwComplexEventAtDefault 17 ef))
      (cwComplexDecodeBHist (cwComplexEventAtDefault 19 ef)))

private theorem CWComplexTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CWComplexUp, cwComplexFromEventFlow (cwComplexToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T K E A B C H R P N =>
      change
        some
          (CWComplexUp.mk
            (cwComplexDecodeBHist (cwComplexEncodeBHist T))
            (cwComplexDecodeBHist (cwComplexEncodeBHist K))
            (cwComplexDecodeBHist (cwComplexEncodeBHist E))
            (cwComplexDecodeBHist (cwComplexEncodeBHist A))
            (cwComplexDecodeBHist (cwComplexEncodeBHist B))
            (cwComplexDecodeBHist (cwComplexEncodeBHist C))
            (cwComplexDecodeBHist (cwComplexEncodeBHist H))
            (cwComplexDecodeBHist (cwComplexEncodeBHist R))
            (cwComplexDecodeBHist (cwComplexEncodeBHist P))
            (cwComplexDecodeBHist (cwComplexEncodeBHist N))) =
          some (CWComplexUp.mk T K E A B C H R P N)
      rw [CWComplexTasteGate_single_carrier_alignment_decode_encode T,
        CWComplexTasteGate_single_carrier_alignment_decode_encode K,
        CWComplexTasteGate_single_carrier_alignment_decode_encode E,
        CWComplexTasteGate_single_carrier_alignment_decode_encode A,
        CWComplexTasteGate_single_carrier_alignment_decode_encode B,
        CWComplexTasteGate_single_carrier_alignment_decode_encode C,
        CWComplexTasteGate_single_carrier_alignment_decode_encode H,
        CWComplexTasteGate_single_carrier_alignment_decode_encode R,
        CWComplexTasteGate_single_carrier_alignment_decode_encode P,
        CWComplexTasteGate_single_carrier_alignment_decode_encode N]

private theorem CWComplexTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CWComplexUp} :
    cwComplexToEventFlow x = cwComplexToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cwComplexFromEventFlow (cwComplexToEventFlow x) =
        cwComplexFromEventFlow (cwComplexToEventFlow y) :=
    congrArg cwComplexFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CWComplexTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CWComplexTasteGate_single_carrier_alignment_round_trip y)))

instance cwComplexBHistCarrier : BHistCarrier CWComplexUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cwComplexToEventFlow
  fromEventFlow := cwComplexFromEventFlow

instance cwComplexChapterTasteGate : ChapterTasteGate CWComplexUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cwComplexFromEventFlow (cwComplexToEventFlow x) = some x
    exact CWComplexTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CWComplexTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CWComplexTasteGate_single_carrier_alignment :
    (∀ h : BHist, cwComplexDecodeBHist (cwComplexEncodeBHist h) = h) ∧
      (∀ x : CWComplexUp, cwComplexFromEventFlow (cwComplexToEventFlow x) = some x) ∧
        (∀ x y : CWComplexUp, cwComplexToEventFlow x = cwComplexToEventFlow y → x = y) ∧
          cwComplexEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CWComplexTasteGate_single_carrier_alignment_decode_encode,
      CWComplexTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => CWComplexTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CWComplexUp
