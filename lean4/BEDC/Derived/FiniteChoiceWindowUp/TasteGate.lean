import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteChoiceWindowUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteChoiceWindowUp : Type where
  | mk (I A S D R H C P N : BHist) : FiniteChoiceWindowUp
  deriving DecidableEq

def finiteChoiceWindowEncodeBHist : BHist → List BMark
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteChoiceWindowEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteChoiceWindowEncodeBHist h

def finiteChoiceWindowDecodeBHist : List BMark → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteChoiceWindowDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteChoiceWindowDecodeBHist tail)

private theorem FiniteChoiceWindowTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, finiteChoiceWindowDecodeBHist (finiteChoiceWindowEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteChoiceWindowFields : FiniteChoiceWindowUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteChoiceWindowUp.mk I A S D R H C P N => [I, A, S, D, R, H, C, P, N]

def finiteChoiceWindowToEventFlow : FiniteChoiceWindowUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (finiteChoiceWindowFields x).map finiteChoiceWindowEncodeBHist

private def finiteChoiceWindowEventAtDefault : Nat → EventFlow → List BMark
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteChoiceWindowEventAtDefault index rest

def finiteChoiceWindowFromEventFlow (ef : EventFlow) : Option FiniteChoiceWindowUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteChoiceWindowUp.mk
      (finiteChoiceWindowDecodeBHist (finiteChoiceWindowEventAtDefault 0 ef))
      (finiteChoiceWindowDecodeBHist (finiteChoiceWindowEventAtDefault 1 ef))
      (finiteChoiceWindowDecodeBHist (finiteChoiceWindowEventAtDefault 2 ef))
      (finiteChoiceWindowDecodeBHist (finiteChoiceWindowEventAtDefault 3 ef))
      (finiteChoiceWindowDecodeBHist (finiteChoiceWindowEventAtDefault 4 ef))
      (finiteChoiceWindowDecodeBHist (finiteChoiceWindowEventAtDefault 5 ef))
      (finiteChoiceWindowDecodeBHist (finiteChoiceWindowEventAtDefault 6 ef))
      (finiteChoiceWindowDecodeBHist (finiteChoiceWindowEventAtDefault 7 ef))
      (finiteChoiceWindowDecodeBHist (finiteChoiceWindowEventAtDefault 8 ef)))

private theorem FiniteChoiceWindowTasteGate_single_carrier_alignment_round_trip
    (x : FiniteChoiceWindowUp) :
    finiteChoiceWindowFromEventFlow (finiteChoiceWindowToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I A S D R H C P N =>
      change
        some
          (FiniteChoiceWindowUp.mk
            (finiteChoiceWindowDecodeBHist (finiteChoiceWindowEncodeBHist I))
            (finiteChoiceWindowDecodeBHist (finiteChoiceWindowEncodeBHist A))
            (finiteChoiceWindowDecodeBHist (finiteChoiceWindowEncodeBHist S))
            (finiteChoiceWindowDecodeBHist (finiteChoiceWindowEncodeBHist D))
            (finiteChoiceWindowDecodeBHist (finiteChoiceWindowEncodeBHist R))
            (finiteChoiceWindowDecodeBHist (finiteChoiceWindowEncodeBHist H))
            (finiteChoiceWindowDecodeBHist (finiteChoiceWindowEncodeBHist C))
            (finiteChoiceWindowDecodeBHist (finiteChoiceWindowEncodeBHist P))
            (finiteChoiceWindowDecodeBHist (finiteChoiceWindowEncodeBHist N))) =
          some (FiniteChoiceWindowUp.mk I A S D R H C P N)
      rw [FiniteChoiceWindowTasteGate_single_carrier_alignment_decode I,
        FiniteChoiceWindowTasteGate_single_carrier_alignment_decode A,
        FiniteChoiceWindowTasteGate_single_carrier_alignment_decode S,
        FiniteChoiceWindowTasteGate_single_carrier_alignment_decode D,
        FiniteChoiceWindowTasteGate_single_carrier_alignment_decode R,
        FiniteChoiceWindowTasteGate_single_carrier_alignment_decode H,
        FiniteChoiceWindowTasteGate_single_carrier_alignment_decode C,
        FiniteChoiceWindowTasteGate_single_carrier_alignment_decode P,
        FiniteChoiceWindowTasteGate_single_carrier_alignment_decode N]

private theorem FiniteChoiceWindowTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FiniteChoiceWindowUp} :
    finiteChoiceWindowToEventFlow x = finiteChoiceWindowToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteChoiceWindowFromEventFlow (finiteChoiceWindowToEventFlow x) =
        finiteChoiceWindowFromEventFlow (finiteChoiceWindowToEventFlow y) :=
    congrArg finiteChoiceWindowFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FiniteChoiceWindowTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FiniteChoiceWindowTasteGate_single_carrier_alignment_round_trip y)))

instance finiteChoiceWindowBHistCarrier : BHistCarrier FiniteChoiceWindowUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteChoiceWindowToEventFlow
  fromEventFlow := finiteChoiceWindowFromEventFlow

instance finiteChoiceWindowChapterTasteGate : ChapterTasteGate FiniteChoiceWindowUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteChoiceWindowFromEventFlow (finiteChoiceWindowToEventFlow x) = some x
    exact FiniteChoiceWindowTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FiniteChoiceWindowTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem FiniteChoiceWindowTasteGate_single_carrier_alignment :
    (forall h : BHist, finiteChoiceWindowDecodeBHist (finiteChoiceWindowEncodeBHist h) = h) ∧
      (forall x : FiniteChoiceWindowUp,
        finiteChoiceWindowFromEventFlow (finiteChoiceWindowToEventFlow x) = some x) ∧
        Nonempty (BHistCarrier FiniteChoiceWindowUp) ∧
          Nonempty (ChapterTasteGate FiniteChoiceWindowUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact FiniteChoiceWindowTasteGate_single_carrier_alignment_decode
  constructor
  · exact FiniteChoiceWindowTasteGate_single_carrier_alignment_round_trip
  constructor
  · exact ⟨finiteChoiceWindowBHistCarrier⟩
  · exact ⟨finiteChoiceWindowChapterTasteGate⟩

end BEDC.Derived.FiniteChoiceWindowUp
