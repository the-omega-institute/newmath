import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CantorIntersectionMetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CantorIntersectionMetricUp : Type where
  | mk
      (completeMetric completionRoute nestedBall cantorHandoff cauchyFilter dyadicLedger
        streamWindows regularReadback realSeal transport replay provenance localName : BHist) :
      CantorIntersectionMetricUp
  deriving DecidableEq

def cantorIntersectionMetricEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cantorIntersectionMetricEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cantorIntersectionMetricEncodeBHist h

def cantorIntersectionMetricDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cantorIntersectionMetricDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cantorIntersectionMetricDecodeBHist tail)

private theorem CantorIntersectionMetricTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cantorIntersectionMetricDecodeBHist (cantorIntersectionMetricEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def CantorIntersectionMetricTasteGate_single_carrier_alignment_fields :
    CantorIntersectionMetricUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CantorIntersectionMetricUp.mk completeMetric completionRoute nestedBall cantorHandoff
      cauchyFilter dyadicLedger streamWindows regularReadback realSeal transport replay
      provenance localName =>
      [completeMetric, completionRoute, nestedBall, cantorHandoff, cauchyFilter, dyadicLedger,
        streamWindows, regularReadback, realSeal, transport, replay, provenance, localName]

def CantorIntersectionMetricTasteGate_single_carrier_alignment_toEventFlow :
    CantorIntersectionMetricUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (CantorIntersectionMetricTasteGate_single_carrier_alignment_fields x).map
      cantorIntersectionMetricEncodeBHist

private def CantorIntersectionMetricTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      CantorIntersectionMetricTasteGate_single_carrier_alignment_eventAtDefault index rest

def CantorIntersectionMetricTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option CantorIntersectionMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (CantorIntersectionMetricUp.mk
        (cantorIntersectionMetricDecodeBHist
          (CantorIntersectionMetricTasteGate_single_carrier_alignment_eventAtDefault 0 ef))
        (cantorIntersectionMetricDecodeBHist
          (CantorIntersectionMetricTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
        (cantorIntersectionMetricDecodeBHist
          (CantorIntersectionMetricTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
        (cantorIntersectionMetricDecodeBHist
          (CantorIntersectionMetricTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
        (cantorIntersectionMetricDecodeBHist
          (CantorIntersectionMetricTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
        (cantorIntersectionMetricDecodeBHist
          (CantorIntersectionMetricTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
        (cantorIntersectionMetricDecodeBHist
          (CantorIntersectionMetricTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
        (cantorIntersectionMetricDecodeBHist
          (CantorIntersectionMetricTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
        (cantorIntersectionMetricDecodeBHist
          (CantorIntersectionMetricTasteGate_single_carrier_alignment_eventAtDefault 8 ef))
        (cantorIntersectionMetricDecodeBHist
          (CantorIntersectionMetricTasteGate_single_carrier_alignment_eventAtDefault 9 ef))
        (cantorIntersectionMetricDecodeBHist
          (CantorIntersectionMetricTasteGate_single_carrier_alignment_eventAtDefault 10 ef))
        (cantorIntersectionMetricDecodeBHist
          (CantorIntersectionMetricTasteGate_single_carrier_alignment_eventAtDefault 11 ef))
        (cantorIntersectionMetricDecodeBHist
          (CantorIntersectionMetricTasteGate_single_carrier_alignment_eventAtDefault 12 ef)))

def CantorIntersectionMetricTasteGate_single_carrier_alignment_carrier :
    BHistCarrier CantorIntersectionMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := CantorIntersectionMetricTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := CantorIntersectionMetricTasteGate_single_carrier_alignment_fromEventFlow

instance CantorIntersectionMetricTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier CantorIntersectionMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  CantorIntersectionMetricTasteGate_single_carrier_alignment_carrier

private theorem CantorIntersectionMetricTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CantorIntersectionMetricUp,
      CantorIntersectionMetricTasteGate_single_carrier_alignment_fromEventFlow
          (CantorIntersectionMetricTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk completeMetric completionRoute nestedBall cantorHandoff cauchyFilter dyadicLedger
      streamWindows regularReadback realSeal transport replay provenance localName =>
      change
        some
            (CantorIntersectionMetricUp.mk
              (cantorIntersectionMetricDecodeBHist
                (cantorIntersectionMetricEncodeBHist completeMetric))
              (cantorIntersectionMetricDecodeBHist
                (cantorIntersectionMetricEncodeBHist completionRoute))
              (cantorIntersectionMetricDecodeBHist
                (cantorIntersectionMetricEncodeBHist nestedBall))
              (cantorIntersectionMetricDecodeBHist
                (cantorIntersectionMetricEncodeBHist cantorHandoff))
              (cantorIntersectionMetricDecodeBHist
                (cantorIntersectionMetricEncodeBHist cauchyFilter))
              (cantorIntersectionMetricDecodeBHist
                (cantorIntersectionMetricEncodeBHist dyadicLedger))
              (cantorIntersectionMetricDecodeBHist
                (cantorIntersectionMetricEncodeBHist streamWindows))
              (cantorIntersectionMetricDecodeBHist
                (cantorIntersectionMetricEncodeBHist regularReadback))
              (cantorIntersectionMetricDecodeBHist
                (cantorIntersectionMetricEncodeBHist realSeal))
              (cantorIntersectionMetricDecodeBHist
                (cantorIntersectionMetricEncodeBHist transport))
              (cantorIntersectionMetricDecodeBHist
                (cantorIntersectionMetricEncodeBHist replay))
              (cantorIntersectionMetricDecodeBHist
                (cantorIntersectionMetricEncodeBHist provenance))
              (cantorIntersectionMetricDecodeBHist
                (cantorIntersectionMetricEncodeBHist localName))) =
          some
            (CantorIntersectionMetricUp.mk completeMetric completionRoute nestedBall
              cantorHandoff cauchyFilter dyadicLedger streamWindows regularReadback realSeal
              transport replay provenance localName)
      rw [CantorIntersectionMetricTasteGate_single_carrier_alignment_decode_encode completeMetric]
      rw [CantorIntersectionMetricTasteGate_single_carrier_alignment_decode_encode completionRoute]
      rw [CantorIntersectionMetricTasteGate_single_carrier_alignment_decode_encode nestedBall]
      rw [CantorIntersectionMetricTasteGate_single_carrier_alignment_decode_encode cantorHandoff]
      rw [CantorIntersectionMetricTasteGate_single_carrier_alignment_decode_encode cauchyFilter]
      rw [CantorIntersectionMetricTasteGate_single_carrier_alignment_decode_encode dyadicLedger]
      rw [CantorIntersectionMetricTasteGate_single_carrier_alignment_decode_encode streamWindows]
      rw [CantorIntersectionMetricTasteGate_single_carrier_alignment_decode_encode regularReadback]
      rw [CantorIntersectionMetricTasteGate_single_carrier_alignment_decode_encode realSeal]
      rw [CantorIntersectionMetricTasteGate_single_carrier_alignment_decode_encode transport]
      rw [CantorIntersectionMetricTasteGate_single_carrier_alignment_decode_encode replay]
      rw [CantorIntersectionMetricTasteGate_single_carrier_alignment_decode_encode provenance]
      rw [CantorIntersectionMetricTasteGate_single_carrier_alignment_decode_encode localName]

private theorem CantorIntersectionMetricTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CantorIntersectionMetricUp} :
    CantorIntersectionMetricTasteGate_single_carrier_alignment_toEventFlow x =
        CantorIntersectionMetricTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          CantorIntersectionMetricTasteGate_single_carrier_alignment_fromEventFlow
            (CantorIntersectionMetricTasteGate_single_carrier_alignment_toEventFlow x) :=
        (CantorIntersectionMetricTasteGate_single_carrier_alignment_round_trip x).symm
      _ =
          CantorIntersectionMetricTasteGate_single_carrier_alignment_fromEventFlow
            (CantorIntersectionMetricTasteGate_single_carrier_alignment_toEventFlow y) :=
        congrArg CantorIntersectionMetricTasteGate_single_carrier_alignment_fromEventFlow hxy
      _ = some y := CantorIntersectionMetricTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

def CantorIntersectionMetricTasteGate_single_carrier_alignment_gate :
    @ChapterTasteGate CantorIntersectionMetricUp
      CantorIntersectionMetricTasteGate_single_carrier_alignment_carrier where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      CantorIntersectionMetricTasteGate_single_carrier_alignment_fromEventFlow
          (CantorIntersectionMetricTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact CantorIntersectionMetricTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CantorIntersectionMetricTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance CantorIntersectionMetricTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate CantorIntersectionMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  CantorIntersectionMetricTasteGate_single_carrier_alignment_gate

theorem CantorIntersectionMetricTasteGate_single_carrier_alignment :
    (forall h : BHist,
      cantorIntersectionMetricDecodeBHist (cantorIntersectionMetricEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CantorIntersectionMetricUp) ∧
      Nonempty (ChapterTasteGate CantorIntersectionMetricUp) ∧
      cantorIntersectionMetricEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CantorIntersectionMetricTasteGate_single_carrier_alignment_decode_encode,
      ⟨⟨CantorIntersectionMetricTasteGate_single_carrier_alignment_carrier⟩,
        ⟨⟨CantorIntersectionMetricTasteGate_single_carrier_alignment_gate⟩, rfl⟩⟩⟩

end BEDC.Derived.CantorIntersectionMetricUp
