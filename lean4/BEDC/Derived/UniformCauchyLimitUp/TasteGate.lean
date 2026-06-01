import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformCauchyLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformCauchyLimitUp : Type where
  | mk
      (continuousFamily modulusFamily convergenceLedger streamWindows regularReadback
        dyadicTolerance realSeal transport replay provenance localName : BHist) :
      UniformCauchyLimitUp
  deriving DecidableEq

def uniformCauchyLimitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformCauchyLimitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformCauchyLimitEncodeBHist h

def uniformCauchyLimitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformCauchyLimitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformCauchyLimitDecodeBHist tail)

private theorem UniformCauchyLimitTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, uniformCauchyLimitDecodeBHist (uniformCauchyLimitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def UniformCauchyLimitTasteGate_single_carrier_alignment_fields :
    UniformCauchyLimitUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformCauchyLimitUp.mk continuousFamily modulusFamily convergenceLedger streamWindows
      regularReadback dyadicTolerance realSeal transport replay provenance localName =>
      [continuousFamily, modulusFamily, convergenceLedger, streamWindows, regularReadback,
        dyadicTolerance, realSeal, transport, replay, provenance, localName]

def UniformCauchyLimitTasteGate_single_carrier_alignment_toEventFlow :
    UniformCauchyLimitUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (UniformCauchyLimitTasteGate_single_carrier_alignment_fields x).map
      uniformCauchyLimitEncodeBHist

private def UniformCauchyLimitTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      UniformCauchyLimitTasteGate_single_carrier_alignment_eventAtDefault index rest

def UniformCauchyLimitTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option UniformCauchyLimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (UniformCauchyLimitUp.mk
        (uniformCauchyLimitDecodeBHist
          (UniformCauchyLimitTasteGate_single_carrier_alignment_eventAtDefault 0 ef))
        (uniformCauchyLimitDecodeBHist
          (UniformCauchyLimitTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
        (uniformCauchyLimitDecodeBHist
          (UniformCauchyLimitTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
        (uniformCauchyLimitDecodeBHist
          (UniformCauchyLimitTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
        (uniformCauchyLimitDecodeBHist
          (UniformCauchyLimitTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
        (uniformCauchyLimitDecodeBHist
          (UniformCauchyLimitTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
        (uniformCauchyLimitDecodeBHist
          (UniformCauchyLimitTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
        (uniformCauchyLimitDecodeBHist
          (UniformCauchyLimitTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
        (uniformCauchyLimitDecodeBHist
          (UniformCauchyLimitTasteGate_single_carrier_alignment_eventAtDefault 8 ef))
        (uniformCauchyLimitDecodeBHist
          (UniformCauchyLimitTasteGate_single_carrier_alignment_eventAtDefault 9 ef))
        (uniformCauchyLimitDecodeBHist
          (UniformCauchyLimitTasteGate_single_carrier_alignment_eventAtDefault 10 ef)))

def UniformCauchyLimitTasteGate_single_carrier_alignment_carrier :
    BHistCarrier UniformCauchyLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := UniformCauchyLimitTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := UniformCauchyLimitTasteGate_single_carrier_alignment_fromEventFlow

instance UniformCauchyLimitTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier UniformCauchyLimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  UniformCauchyLimitTasteGate_single_carrier_alignment_carrier

private theorem UniformCauchyLimitTasteGate_single_carrier_alignment_round_trip :
    ∀ x : UniformCauchyLimitUp,
      UniformCauchyLimitTasteGate_single_carrier_alignment_fromEventFlow
          (UniformCauchyLimitTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk continuousFamily modulusFamily convergenceLedger streamWindows regularReadback
      dyadicTolerance realSeal transport replay provenance localName =>
      change
        some
            (UniformCauchyLimitUp.mk
              (uniformCauchyLimitDecodeBHist (uniformCauchyLimitEncodeBHist continuousFamily))
              (uniformCauchyLimitDecodeBHist (uniformCauchyLimitEncodeBHist modulusFamily))
              (uniformCauchyLimitDecodeBHist
                (uniformCauchyLimitEncodeBHist convergenceLedger))
              (uniformCauchyLimitDecodeBHist (uniformCauchyLimitEncodeBHist streamWindows))
              (uniformCauchyLimitDecodeBHist (uniformCauchyLimitEncodeBHist regularReadback))
              (uniformCauchyLimitDecodeBHist (uniformCauchyLimitEncodeBHist dyadicTolerance))
              (uniformCauchyLimitDecodeBHist (uniformCauchyLimitEncodeBHist realSeal))
              (uniformCauchyLimitDecodeBHist (uniformCauchyLimitEncodeBHist transport))
              (uniformCauchyLimitDecodeBHist (uniformCauchyLimitEncodeBHist replay))
              (uniformCauchyLimitDecodeBHist (uniformCauchyLimitEncodeBHist provenance))
              (uniformCauchyLimitDecodeBHist (uniformCauchyLimitEncodeBHist localName))) =
          some
            (UniformCauchyLimitUp.mk continuousFamily modulusFamily convergenceLedger
              streamWindows regularReadback dyadicTolerance realSeal transport replay provenance
              localName)
      rw [UniformCauchyLimitTasteGate_single_carrier_alignment_decode_encode continuousFamily]
      rw [UniformCauchyLimitTasteGate_single_carrier_alignment_decode_encode modulusFamily]
      rw [UniformCauchyLimitTasteGate_single_carrier_alignment_decode_encode convergenceLedger]
      rw [UniformCauchyLimitTasteGate_single_carrier_alignment_decode_encode streamWindows]
      rw [UniformCauchyLimitTasteGate_single_carrier_alignment_decode_encode regularReadback]
      rw [UniformCauchyLimitTasteGate_single_carrier_alignment_decode_encode dyadicTolerance]
      rw [UniformCauchyLimitTasteGate_single_carrier_alignment_decode_encode realSeal]
      rw [UniformCauchyLimitTasteGate_single_carrier_alignment_decode_encode transport]
      rw [UniformCauchyLimitTasteGate_single_carrier_alignment_decode_encode replay]
      rw [UniformCauchyLimitTasteGate_single_carrier_alignment_decode_encode provenance]
      rw [UniformCauchyLimitTasteGate_single_carrier_alignment_decode_encode localName]

private theorem UniformCauchyLimitTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : UniformCauchyLimitUp} :
    UniformCauchyLimitTasteGate_single_carrier_alignment_toEventFlow x =
        UniformCauchyLimitTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          UniformCauchyLimitTasteGate_single_carrier_alignment_fromEventFlow
            (UniformCauchyLimitTasteGate_single_carrier_alignment_toEventFlow x) :=
        (UniformCauchyLimitTasteGate_single_carrier_alignment_round_trip x).symm
      _ =
          UniformCauchyLimitTasteGate_single_carrier_alignment_fromEventFlow
            (UniformCauchyLimitTasteGate_single_carrier_alignment_toEventFlow y) :=
        congrArg UniformCauchyLimitTasteGate_single_carrier_alignment_fromEventFlow hxy
      _ = some y := UniformCauchyLimitTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

def UniformCauchyLimitTasteGate_single_carrier_alignment_gate :
    @ChapterTasteGate UniformCauchyLimitUp
      UniformCauchyLimitTasteGate_single_carrier_alignment_carrier where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      UniformCauchyLimitTasteGate_single_carrier_alignment_fromEventFlow
          (UniformCauchyLimitTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact UniformCauchyLimitTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (UniformCauchyLimitTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance UniformCauchyLimitTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate UniformCauchyLimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  UniformCauchyLimitTasteGate_single_carrier_alignment_gate

theorem UniformCauchyLimitTasteGate_single_carrier_alignment :
    (forall h : BHist, uniformCauchyLimitDecodeBHist (uniformCauchyLimitEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier UniformCauchyLimitUp) ∧
      Nonempty (ChapterTasteGate UniformCauchyLimitUp) ∧
      uniformCauchyLimitEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨UniformCauchyLimitTasteGate_single_carrier_alignment_decode_encode,
      ⟨⟨UniformCauchyLimitTasteGate_single_carrier_alignment_carrier⟩,
        ⟨⟨UniformCauchyLimitTasteGate_single_carrier_alignment_gate⟩, rfl⟩⟩⟩

end BEDC.Derived.UniformCauchyLimitUp
