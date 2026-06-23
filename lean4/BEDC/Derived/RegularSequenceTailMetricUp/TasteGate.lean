import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularSequenceTailMetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularSequenceTailMetricUp : Type where
  | mk (D W R F M E H C P N : BHist) : RegularSequenceTailMetricUp
  deriving DecidableEq

def regularSequenceTailMetricEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularSequenceTailMetricEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularSequenceTailMetricEncodeBHist h

def regularSequenceTailMetricDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularSequenceTailMetricDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularSequenceTailMetricDecodeBHist tail)

private theorem RegularSequenceTailMetricTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      regularSequenceTailMetricDecodeBHist
        (regularSequenceTailMetricEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularSequenceTailMetricFields : RegularSequenceTailMetricUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularSequenceTailMetricUp.mk D W R F M E H C P N =>
      [D, W, R, F, M, E, H, C, P, N]

def regularSequenceTailMetricToEventFlow :
    RegularSequenceTailMetricUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (regularSequenceTailMetricFields x).map regularSequenceTailMetricEncodeBHist

private def regularSequenceTailMetricEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      regularSequenceTailMetricEventAtDefault index rest

def regularSequenceTailMetricFromEventFlow
    (ef : EventFlow) : Option RegularSequenceTailMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularSequenceTailMetricUp.mk
      (regularSequenceTailMetricDecodeBHist
        (regularSequenceTailMetricEventAtDefault 0 ef))
      (regularSequenceTailMetricDecodeBHist
        (regularSequenceTailMetricEventAtDefault 1 ef))
      (regularSequenceTailMetricDecodeBHist
        (regularSequenceTailMetricEventAtDefault 2 ef))
      (regularSequenceTailMetricDecodeBHist
        (regularSequenceTailMetricEventAtDefault 3 ef))
      (regularSequenceTailMetricDecodeBHist
        (regularSequenceTailMetricEventAtDefault 4 ef))
      (regularSequenceTailMetricDecodeBHist
        (regularSequenceTailMetricEventAtDefault 5 ef))
      (regularSequenceTailMetricDecodeBHist
        (regularSequenceTailMetricEventAtDefault 6 ef))
      (regularSequenceTailMetricDecodeBHist
        (regularSequenceTailMetricEventAtDefault 7 ef))
      (regularSequenceTailMetricDecodeBHist
        (regularSequenceTailMetricEventAtDefault 8 ef))
      (regularSequenceTailMetricDecodeBHist
        (regularSequenceTailMetricEventAtDefault 9 ef)))

private theorem RegularSequenceTailMetricTasteGate_single_carrier_alignment_round_trip
    (x : RegularSequenceTailMetricUp) :
    regularSequenceTailMetricFromEventFlow
      (regularSequenceTailMetricToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk D W R F M E H C P N =>
      change
        some
            (RegularSequenceTailMetricUp.mk
              (regularSequenceTailMetricDecodeBHist
                (regularSequenceTailMetricEncodeBHist D))
              (regularSequenceTailMetricDecodeBHist
                (regularSequenceTailMetricEncodeBHist W))
              (regularSequenceTailMetricDecodeBHist
                (regularSequenceTailMetricEncodeBHist R))
              (regularSequenceTailMetricDecodeBHist
                (regularSequenceTailMetricEncodeBHist F))
              (regularSequenceTailMetricDecodeBHist
                (regularSequenceTailMetricEncodeBHist M))
              (regularSequenceTailMetricDecodeBHist
                (regularSequenceTailMetricEncodeBHist E))
              (regularSequenceTailMetricDecodeBHist
                (regularSequenceTailMetricEncodeBHist H))
              (regularSequenceTailMetricDecodeBHist
                (regularSequenceTailMetricEncodeBHist C))
              (regularSequenceTailMetricDecodeBHist
                (regularSequenceTailMetricEncodeBHist P))
              (regularSequenceTailMetricDecodeBHist
                (regularSequenceTailMetricEncodeBHist N))) =
          some (RegularSequenceTailMetricUp.mk D W R F M E H C P N)
      rw [RegularSequenceTailMetricTasteGate_single_carrier_alignment_decode_encode D,
        RegularSequenceTailMetricTasteGate_single_carrier_alignment_decode_encode W,
        RegularSequenceTailMetricTasteGate_single_carrier_alignment_decode_encode R,
        RegularSequenceTailMetricTasteGate_single_carrier_alignment_decode_encode F,
        RegularSequenceTailMetricTasteGate_single_carrier_alignment_decode_encode M,
        RegularSequenceTailMetricTasteGate_single_carrier_alignment_decode_encode E,
        RegularSequenceTailMetricTasteGate_single_carrier_alignment_decode_encode H,
        RegularSequenceTailMetricTasteGate_single_carrier_alignment_decode_encode C,
        RegularSequenceTailMetricTasteGate_single_carrier_alignment_decode_encode P,
        RegularSequenceTailMetricTasteGate_single_carrier_alignment_decode_encode N]

private theorem RegularSequenceTailMetricTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularSequenceTailMetricUp} :
    regularSequenceTailMetricToEventFlow x =
      regularSequenceTailMetricToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularSequenceTailMetricFromEventFlow
          (regularSequenceTailMetricToEventFlow x) =
        regularSequenceTailMetricFromEventFlow
          (regularSequenceTailMetricToEventFlow y) :=
    congrArg regularSequenceTailMetricFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularSequenceTailMetricTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularSequenceTailMetricTasteGate_single_carrier_alignment_round_trip y)))

instance regularSequenceTailMetricBHistCarrier :
    BHistCarrier RegularSequenceTailMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularSequenceTailMetricToEventFlow
  fromEventFlow := regularSequenceTailMetricFromEventFlow

instance regularSequenceTailMetricChapterTasteGate :
    ChapterTasteGate RegularSequenceTailMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularSequenceTailMetricFromEventFlow
        (regularSequenceTailMetricToEventFlow x) = some x
    exact RegularSequenceTailMetricTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularSequenceTailMetricTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem RegularSequenceTailMetricTasteGate_single_carrier_alignment :
    (∀ h : BHist, regularSequenceTailMetricDecodeBHist
      (regularSequenceTailMetricEncodeBHist h) = h) ∧
      (∀ x : RegularSequenceTailMetricUp,
        regularSequenceTailMetricFromEventFlow
          (regularSequenceTailMetricToEventFlow x) = some x) ∧
        (∀ x y : RegularSequenceTailMetricUp,
          regularSequenceTailMetricToEventFlow x =
            regularSequenceTailMetricToEventFlow y -> x = y) ∧
          regularSequenceTailMetricEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RegularSequenceTailMetricTasteGate_single_carrier_alignment_decode_encode,
      RegularSequenceTailMetricTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RegularSequenceTailMetricTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularSequenceTailMetricUp
