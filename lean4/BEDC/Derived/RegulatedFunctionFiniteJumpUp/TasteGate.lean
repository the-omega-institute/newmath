import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegulatedFunctionFiniteJumpUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegulatedFunctionFiniteJumpUp : Type where
  | mk (I J W A U H C P N : BHist) : RegulatedFunctionFiniteJumpUp

def regulatedFunctionFiniteJumpEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regulatedFunctionFiniteJumpEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regulatedFunctionFiniteJumpEncodeBHist h

def regulatedFunctionFiniteJumpDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regulatedFunctionFiniteJumpDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regulatedFunctionFiniteJumpDecodeBHist tail)

private theorem RegulatedFunctionFiniteJumpTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      regulatedFunctionFiniteJumpDecodeBHist
        (regulatedFunctionFiniteJumpEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regulatedFunctionFiniteJumpFields :
    RegulatedFunctionFiniteJumpUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegulatedFunctionFiniteJumpUp.mk I J W A U H C P N =>
      [I, J, W, A, U, H, C, P, N]

def regulatedFunctionFiniteJumpToEventFlow :
    RegulatedFunctionFiniteJumpUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (regulatedFunctionFiniteJumpFields x).map regulatedFunctionFiniteJumpEncodeBHist

private def regulatedFunctionFiniteJumpEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regulatedFunctionFiniteJumpEventAtDefault index rest

def regulatedFunctionFiniteJumpFromEventFlow
    (ef : EventFlow) : Option RegulatedFunctionFiniteJumpUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegulatedFunctionFiniteJumpUp.mk
      (regulatedFunctionFiniteJumpDecodeBHist
        (regulatedFunctionFiniteJumpEventAtDefault 0 ef))
      (regulatedFunctionFiniteJumpDecodeBHist
        (regulatedFunctionFiniteJumpEventAtDefault 1 ef))
      (regulatedFunctionFiniteJumpDecodeBHist
        (regulatedFunctionFiniteJumpEventAtDefault 2 ef))
      (regulatedFunctionFiniteJumpDecodeBHist
        (regulatedFunctionFiniteJumpEventAtDefault 3 ef))
      (regulatedFunctionFiniteJumpDecodeBHist
        (regulatedFunctionFiniteJumpEventAtDefault 4 ef))
      (regulatedFunctionFiniteJumpDecodeBHist
        (regulatedFunctionFiniteJumpEventAtDefault 5 ef))
      (regulatedFunctionFiniteJumpDecodeBHist
        (regulatedFunctionFiniteJumpEventAtDefault 6 ef))
      (regulatedFunctionFiniteJumpDecodeBHist
        (regulatedFunctionFiniteJumpEventAtDefault 7 ef))
      (regulatedFunctionFiniteJumpDecodeBHist
        (regulatedFunctionFiniteJumpEventAtDefault 8 ef)))

private theorem RegulatedFunctionFiniteJumpTasteGate_single_carrier_alignment_round_trip
    (x : RegulatedFunctionFiniteJumpUp) :
    regulatedFunctionFiniteJumpFromEventFlow
      (regulatedFunctionFiniteJumpToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I J W A U H C P N =>
      change
        some
          (RegulatedFunctionFiniteJumpUp.mk
            (regulatedFunctionFiniteJumpDecodeBHist
              (regulatedFunctionFiniteJumpEncodeBHist I))
            (regulatedFunctionFiniteJumpDecodeBHist
              (regulatedFunctionFiniteJumpEncodeBHist J))
            (regulatedFunctionFiniteJumpDecodeBHist
              (regulatedFunctionFiniteJumpEncodeBHist W))
            (regulatedFunctionFiniteJumpDecodeBHist
              (regulatedFunctionFiniteJumpEncodeBHist A))
            (regulatedFunctionFiniteJumpDecodeBHist
              (regulatedFunctionFiniteJumpEncodeBHist U))
            (regulatedFunctionFiniteJumpDecodeBHist
              (regulatedFunctionFiniteJumpEncodeBHist H))
            (regulatedFunctionFiniteJumpDecodeBHist
              (regulatedFunctionFiniteJumpEncodeBHist C))
            (regulatedFunctionFiniteJumpDecodeBHist
              (regulatedFunctionFiniteJumpEncodeBHist P))
            (regulatedFunctionFiniteJumpDecodeBHist
              (regulatedFunctionFiniteJumpEncodeBHist N))) =
          some (RegulatedFunctionFiniteJumpUp.mk I J W A U H C P N)
      rw [RegulatedFunctionFiniteJumpTasteGate_single_carrier_alignment_decode I,
        RegulatedFunctionFiniteJumpTasteGate_single_carrier_alignment_decode J,
        RegulatedFunctionFiniteJumpTasteGate_single_carrier_alignment_decode W,
        RegulatedFunctionFiniteJumpTasteGate_single_carrier_alignment_decode A,
        RegulatedFunctionFiniteJumpTasteGate_single_carrier_alignment_decode U,
        RegulatedFunctionFiniteJumpTasteGate_single_carrier_alignment_decode H,
        RegulatedFunctionFiniteJumpTasteGate_single_carrier_alignment_decode C,
        RegulatedFunctionFiniteJumpTasteGate_single_carrier_alignment_decode P,
        RegulatedFunctionFiniteJumpTasteGate_single_carrier_alignment_decode N]

private theorem RegulatedFunctionFiniteJumpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegulatedFunctionFiniteJumpUp} :
    regulatedFunctionFiniteJumpToEventFlow x =
        regulatedFunctionFiniteJumpToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regulatedFunctionFiniteJumpFromEventFlow
          (regulatedFunctionFiniteJumpToEventFlow x) =
        regulatedFunctionFiniteJumpFromEventFlow
          (regulatedFunctionFiniteJumpToEventFlow y) :=
    congrArg regulatedFunctionFiniteJumpFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegulatedFunctionFiniteJumpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegulatedFunctionFiniteJumpTasteGate_single_carrier_alignment_round_trip y)))

instance regulatedFunctionFiniteJumpBHistCarrier :
    BHistCarrier RegulatedFunctionFiniteJumpUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regulatedFunctionFiniteJumpToEventFlow
  fromEventFlow := regulatedFunctionFiniteJumpFromEventFlow

instance regulatedFunctionFiniteJumpChapterTasteGate :
    ChapterTasteGate RegulatedFunctionFiniteJumpUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regulatedFunctionFiniteJumpFromEventFlow
      (regulatedFunctionFiniteJumpToEventFlow x) = some x
    exact RegulatedFunctionFiniteJumpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegulatedFunctionFiniteJumpTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

def taste_gate : ChapterTasteGate RegulatedFunctionFiniteJumpUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regulatedFunctionFiniteJumpChapterTasteGate

theorem RegulatedFunctionFiniteJumpTasteGate_single_carrier_alignment :
    regulatedFunctionFiniteJumpEncodeBHist BHist.Empty = [] ∧
      regulatedFunctionFiniteJumpEncodeBHist (BHist.e1 BHist.Empty) = [BMark.b1] ∧
      (∀ h : BHist,
        regulatedFunctionFiniteJumpDecodeBHist
          (regulatedFunctionFiniteJumpEncodeBHist h) = h) ∧
      (∀ x : RegulatedFunctionFiniteJumpUp,
        regulatedFunctionFiniteJumpFromEventFlow
          (regulatedFunctionFiniteJumpToEventFlow x) = some x) ∧
      (∀ x y : RegulatedFunctionFiniteJumpUp,
        regulatedFunctionFiniteJumpToEventFlow x =
          regulatedFunctionFiniteJumpToEventFlow y → x = y) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨rfl,
      rfl,
      RegulatedFunctionFiniteJumpTasteGate_single_carrier_alignment_decode,
      RegulatedFunctionFiniteJumpTasteGate_single_carrier_alignment_round_trip,
      (by
        intro x y heq
        exact RegulatedFunctionFiniteJumpTasteGate_single_carrier_alignment_toEventFlow_injective
          heq)⟩

end BEDC.Derived.RegulatedFunctionFiniteJumpUp
