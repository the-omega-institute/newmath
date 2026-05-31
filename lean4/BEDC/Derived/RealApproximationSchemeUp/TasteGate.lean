import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealApproximationSchemeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealApproximationSchemeUp : Type where
  | mk (S D R Q H C P N : BHist) : RealApproximationSchemeUp
  deriving DecidableEq

def realApproximationSchemeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realApproximationSchemeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realApproximationSchemeEncodeBHist h

def realApproximationSchemeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realApproximationSchemeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realApproximationSchemeDecodeBHist tail)

private theorem RealApproximationSchemeTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      realApproximationSchemeDecodeBHist (realApproximationSchemeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realApproximationSchemeToEventFlow : RealApproximationSchemeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealApproximationSchemeUp.mk S D R Q H C P N =>
      [[BMark.b0],
        realApproximationSchemeEncodeBHist S,
        [BMark.b1, BMark.b0],
        realApproximationSchemeEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b0],
        realApproximationSchemeEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realApproximationSchemeEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realApproximationSchemeEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realApproximationSchemeEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realApproximationSchemeEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        realApproximationSchemeEncodeBHist N]

private def realApproximationSchemeEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realApproximationSchemeEventAtDefault index rest

def realApproximationSchemeFromEventFlow (ef : EventFlow) : Option RealApproximationSchemeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealApproximationSchemeUp.mk
      (realApproximationSchemeDecodeBHist (realApproximationSchemeEventAtDefault 1 ef))
      (realApproximationSchemeDecodeBHist (realApproximationSchemeEventAtDefault 3 ef))
      (realApproximationSchemeDecodeBHist (realApproximationSchemeEventAtDefault 5 ef))
      (realApproximationSchemeDecodeBHist (realApproximationSchemeEventAtDefault 7 ef))
      (realApproximationSchemeDecodeBHist (realApproximationSchemeEventAtDefault 9 ef))
      (realApproximationSchemeDecodeBHist (realApproximationSchemeEventAtDefault 11 ef))
      (realApproximationSchemeDecodeBHist (realApproximationSchemeEventAtDefault 13 ef))
      (realApproximationSchemeDecodeBHist (realApproximationSchemeEventAtDefault 15 ef)))

private theorem RealApproximationSchemeTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RealApproximationSchemeUp,
      realApproximationSchemeFromEventFlow (realApproximationSchemeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S D R Q H C P N =>
      change
        some
          (RealApproximationSchemeUp.mk
            (realApproximationSchemeDecodeBHist (realApproximationSchemeEncodeBHist S))
            (realApproximationSchemeDecodeBHist (realApproximationSchemeEncodeBHist D))
            (realApproximationSchemeDecodeBHist (realApproximationSchemeEncodeBHist R))
            (realApproximationSchemeDecodeBHist (realApproximationSchemeEncodeBHist Q))
            (realApproximationSchemeDecodeBHist (realApproximationSchemeEncodeBHist H))
            (realApproximationSchemeDecodeBHist (realApproximationSchemeEncodeBHist C))
            (realApproximationSchemeDecodeBHist (realApproximationSchemeEncodeBHist P))
            (realApproximationSchemeDecodeBHist (realApproximationSchemeEncodeBHist N))) =
          some (RealApproximationSchemeUp.mk S D R Q H C P N)
      rw [RealApproximationSchemeTasteGate_single_carrier_alignment_decode_encode S,
        RealApproximationSchemeTasteGate_single_carrier_alignment_decode_encode D,
        RealApproximationSchemeTasteGate_single_carrier_alignment_decode_encode R,
        RealApproximationSchemeTasteGate_single_carrier_alignment_decode_encode Q,
        RealApproximationSchemeTasteGate_single_carrier_alignment_decode_encode H,
        RealApproximationSchemeTasteGate_single_carrier_alignment_decode_encode C,
        RealApproximationSchemeTasteGate_single_carrier_alignment_decode_encode P,
        RealApproximationSchemeTasteGate_single_carrier_alignment_decode_encode N]

private theorem RealApproximationSchemeTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealApproximationSchemeUp} :
    realApproximationSchemeToEventFlow x = realApproximationSchemeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realApproximationSchemeFromEventFlow (realApproximationSchemeToEventFlow x) =
        realApproximationSchemeFromEventFlow (realApproximationSchemeToEventFlow y) :=
    congrArg realApproximationSchemeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RealApproximationSchemeTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RealApproximationSchemeTasteGate_single_carrier_alignment_round_trip y)))

instance realApproximationSchemeBHistCarrier : BHistCarrier RealApproximationSchemeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realApproximationSchemeToEventFlow
  fromEventFlow := realApproximationSchemeFromEventFlow

instance realApproximationSchemeChapterTasteGate : ChapterTasteGate RealApproximationSchemeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realApproximationSchemeFromEventFlow (realApproximationSchemeToEventFlow x) = some x
    exact RealApproximationSchemeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealApproximationSchemeTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate RealApproximationSchemeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realApproximationSchemeChapterTasteGate

theorem RealApproximationSchemeTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      realApproximationSchemeDecodeBHist (realApproximationSchemeEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RealApproximationSchemeUp) ∧
        Nonempty (ChapterTasteGate RealApproximationSchemeUp) ∧
          realApproximationSchemeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨RealApproximationSchemeTasteGate_single_carrier_alignment_decode_encode,
      ⟨realApproximationSchemeBHistCarrier⟩,
      ⟨realApproximationSchemeChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.RealApproximationSchemeUp
