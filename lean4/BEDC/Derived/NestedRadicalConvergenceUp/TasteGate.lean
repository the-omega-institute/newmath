import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NestedRadicalConvergenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NestedRadicalConvergenceUp : Type where
  | mk
      (coefficients stages tolerance window tail readback transport replay provenance name :
        BHist) :
      NestedRadicalConvergenceUp
  deriving DecidableEq

def nestedRadicalConvergenceEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: nestedRadicalConvergenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: nestedRadicalConvergenceEncodeBHist h

def nestedRadicalConvergenceDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (nestedRadicalConvergenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (nestedRadicalConvergenceDecodeBHist tail)

private theorem nestedRadicalConvergenceDecode_encode_bhist :
    ∀ h : BHist,
      nestedRadicalConvergenceDecodeBHist
        (nestedRadicalConvergenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def nestedRadicalConvergenceFields : NestedRadicalConvergenceUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NestedRadicalConvergenceUp.mk coefficients stages tolerance window tail readback
      transport replay provenance name =>
      [coefficients, stages, tolerance, window, tail, readback, transport, replay,
        provenance, name]

def nestedRadicalConvergenceToEventFlow : NestedRadicalConvergenceUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | NestedRadicalConvergenceUp.mk coefficients stages tolerance window tail readback
      transport replay provenance name =>
      [nestedRadicalConvergenceEncodeBHist coefficients,
        nestedRadicalConvergenceEncodeBHist stages,
        nestedRadicalConvergenceEncodeBHist tolerance,
        nestedRadicalConvergenceEncodeBHist window,
        nestedRadicalConvergenceEncodeBHist tail,
        nestedRadicalConvergenceEncodeBHist readback,
        nestedRadicalConvergenceEncodeBHist transport,
        nestedRadicalConvergenceEncodeBHist replay,
        nestedRadicalConvergenceEncodeBHist provenance,
        nestedRadicalConvergenceEncodeBHist name]

private def nestedRadicalConvergenceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => nestedRadicalConvergenceEventAtDefault index rest

def nestedRadicalConvergenceFromEventFlow : EventFlow -> Option NestedRadicalConvergenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (NestedRadicalConvergenceUp.mk
          (nestedRadicalConvergenceDecodeBHist
            (nestedRadicalConvergenceEventAtDefault 0 ef))
          (nestedRadicalConvergenceDecodeBHist
            (nestedRadicalConvergenceEventAtDefault 1 ef))
          (nestedRadicalConvergenceDecodeBHist
            (nestedRadicalConvergenceEventAtDefault 2 ef))
          (nestedRadicalConvergenceDecodeBHist
            (nestedRadicalConvergenceEventAtDefault 3 ef))
          (nestedRadicalConvergenceDecodeBHist
            (nestedRadicalConvergenceEventAtDefault 4 ef))
          (nestedRadicalConvergenceDecodeBHist
            (nestedRadicalConvergenceEventAtDefault 5 ef))
          (nestedRadicalConvergenceDecodeBHist
            (nestedRadicalConvergenceEventAtDefault 6 ef))
          (nestedRadicalConvergenceDecodeBHist
            (nestedRadicalConvergenceEventAtDefault 7 ef))
          (nestedRadicalConvergenceDecodeBHist
            (nestedRadicalConvergenceEventAtDefault 8 ef))
          (nestedRadicalConvergenceDecodeBHist
            (nestedRadicalConvergenceEventAtDefault 9 ef)))

private theorem nestedRadicalConvergence_round_trip :
    ∀ x : NestedRadicalConvergenceUp,
      nestedRadicalConvergenceFromEventFlow
        (nestedRadicalConvergenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk coefficients stages tolerance window tail readback transport replay provenance name =>
      change
        some
          (NestedRadicalConvergenceUp.mk
            (nestedRadicalConvergenceDecodeBHist
              (nestedRadicalConvergenceEncodeBHist coefficients))
            (nestedRadicalConvergenceDecodeBHist
              (nestedRadicalConvergenceEncodeBHist stages))
            (nestedRadicalConvergenceDecodeBHist
              (nestedRadicalConvergenceEncodeBHist tolerance))
            (nestedRadicalConvergenceDecodeBHist
              (nestedRadicalConvergenceEncodeBHist window))
            (nestedRadicalConvergenceDecodeBHist
              (nestedRadicalConvergenceEncodeBHist tail))
            (nestedRadicalConvergenceDecodeBHist
              (nestedRadicalConvergenceEncodeBHist readback))
            (nestedRadicalConvergenceDecodeBHist
              (nestedRadicalConvergenceEncodeBHist transport))
            (nestedRadicalConvergenceDecodeBHist
              (nestedRadicalConvergenceEncodeBHist replay))
            (nestedRadicalConvergenceDecodeBHist
              (nestedRadicalConvergenceEncodeBHist provenance))
            (nestedRadicalConvergenceDecodeBHist
              (nestedRadicalConvergenceEncodeBHist name))) =
          some
            (NestedRadicalConvergenceUp.mk coefficients stages tolerance window tail
              readback transport replay provenance name)
      rw [nestedRadicalConvergenceDecode_encode_bhist coefficients,
        nestedRadicalConvergenceDecode_encode_bhist stages,
        nestedRadicalConvergenceDecode_encode_bhist tolerance,
        nestedRadicalConvergenceDecode_encode_bhist window,
        nestedRadicalConvergenceDecode_encode_bhist tail,
        nestedRadicalConvergenceDecode_encode_bhist readback,
        nestedRadicalConvergenceDecode_encode_bhist transport,
        nestedRadicalConvergenceDecode_encode_bhist replay,
        nestedRadicalConvergenceDecode_encode_bhist provenance,
        nestedRadicalConvergenceDecode_encode_bhist name]

private theorem nestedRadicalConvergenceToEventFlow_injective
    {x y : NestedRadicalConvergenceUp} :
    nestedRadicalConvergenceToEventFlow x =
        nestedRadicalConvergenceToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      nestedRadicalConvergenceFromEventFlow (nestedRadicalConvergenceToEventFlow x) =
        nestedRadicalConvergenceFromEventFlow (nestedRadicalConvergenceToEventFlow y) :=
    congrArg nestedRadicalConvergenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (nestedRadicalConvergence_round_trip x).symm
      (Eq.trans hread (nestedRadicalConvergence_round_trip y)))

def nestedRadicalConvergenceBHistCarrier :
    BHistCarrier NestedRadicalConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := nestedRadicalConvergenceToEventFlow
  fromEventFlow := nestedRadicalConvergenceFromEventFlow

instance nestedRadicalConvergenceBHistCarrierInstance :
    BHistCarrier NestedRadicalConvergenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  nestedRadicalConvergenceBHistCarrier

def nestedRadicalConvergenceChapterTasteGate :
    ChapterTasteGate NestedRadicalConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      nestedRadicalConvergenceFromEventFlow
        (nestedRadicalConvergenceToEventFlow x) = some x
    exact nestedRadicalConvergence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (nestedRadicalConvergenceToEventFlow_injective heq)

instance nestedRadicalConvergenceChapterTasteGateInstance :
    ChapterTasteGate NestedRadicalConvergenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  nestedRadicalConvergenceChapterTasteGate

theorem NestedRadicalConvergenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      nestedRadicalConvergenceDecodeBHist (nestedRadicalConvergenceEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier NestedRadicalConvergenceUp) ∧
        Nonempty (ChapterTasteGate NestedRadicalConvergenceUp) ∧
          nestedRadicalConvergenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨nestedRadicalConvergenceDecode_encode_bhist,
      ⟨nestedRadicalConvergenceBHistCarrier⟩,
      ⟨nestedRadicalConvergenceChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.NestedRadicalConvergenceUp
