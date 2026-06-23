import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealCompletionBoundaryWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealCompletionBoundaryWitnessUp : Type where
  | mk (D S R E L U H C P N : BHist) : RealCompletionBoundaryWitnessUp
  deriving DecidableEq

def realCompletionBoundaryWitnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realCompletionBoundaryWitnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realCompletionBoundaryWitnessEncodeBHist h

def realCompletionBoundaryWitnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realCompletionBoundaryWitnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realCompletionBoundaryWitnessDecodeBHist tail)

private theorem RealCompletionBoundaryWitnessTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      realCompletionBoundaryWitnessDecodeBHist
          (realCompletionBoundaryWitnessEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realCompletionBoundaryWitnessFields :
    RealCompletionBoundaryWitnessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealCompletionBoundaryWitnessUp.mk D S R E L U H C P N =>
      [D, S, R, E, L, U, H, C, P, N]

def realCompletionBoundaryWitnessToEventFlow :
    RealCompletionBoundaryWitnessUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (realCompletionBoundaryWitnessFields x).map
    realCompletionBoundaryWitnessEncodeBHist

private def realCompletionBoundaryWitnessEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realCompletionBoundaryWitnessEventAtDefault index rest

def realCompletionBoundaryWitnessFromEventFlow
    (eventFlow : EventFlow) : Option RealCompletionBoundaryWitnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealCompletionBoundaryWitnessUp.mk
      (realCompletionBoundaryWitnessDecodeBHist
        (realCompletionBoundaryWitnessEventAtDefault 0 eventFlow))
      (realCompletionBoundaryWitnessDecodeBHist
        (realCompletionBoundaryWitnessEventAtDefault 1 eventFlow))
      (realCompletionBoundaryWitnessDecodeBHist
        (realCompletionBoundaryWitnessEventAtDefault 2 eventFlow))
      (realCompletionBoundaryWitnessDecodeBHist
        (realCompletionBoundaryWitnessEventAtDefault 3 eventFlow))
      (realCompletionBoundaryWitnessDecodeBHist
        (realCompletionBoundaryWitnessEventAtDefault 4 eventFlow))
      (realCompletionBoundaryWitnessDecodeBHist
        (realCompletionBoundaryWitnessEventAtDefault 5 eventFlow))
      (realCompletionBoundaryWitnessDecodeBHist
        (realCompletionBoundaryWitnessEventAtDefault 6 eventFlow))
      (realCompletionBoundaryWitnessDecodeBHist
        (realCompletionBoundaryWitnessEventAtDefault 7 eventFlow))
      (realCompletionBoundaryWitnessDecodeBHist
        (realCompletionBoundaryWitnessEventAtDefault 8 eventFlow))
      (realCompletionBoundaryWitnessDecodeBHist
        (realCompletionBoundaryWitnessEventAtDefault 9 eventFlow)))

instance realCompletionBoundaryWitnessBHistCarrier :
    BHistCarrier RealCompletionBoundaryWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realCompletionBoundaryWitnessToEventFlow
  fromEventFlow := realCompletionBoundaryWitnessFromEventFlow

private theorem RealCompletionBoundaryWitnessTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RealCompletionBoundaryWitnessUp,
      realCompletionBoundaryWitnessFromEventFlow
          (realCompletionBoundaryWitnessToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk D S R E L U H C P N =>
      change
        some
            (RealCompletionBoundaryWitnessUp.mk
              (realCompletionBoundaryWitnessDecodeBHist
                (realCompletionBoundaryWitnessEncodeBHist D))
              (realCompletionBoundaryWitnessDecodeBHist
                (realCompletionBoundaryWitnessEncodeBHist S))
              (realCompletionBoundaryWitnessDecodeBHist
                (realCompletionBoundaryWitnessEncodeBHist R))
              (realCompletionBoundaryWitnessDecodeBHist
                (realCompletionBoundaryWitnessEncodeBHist E))
              (realCompletionBoundaryWitnessDecodeBHist
                (realCompletionBoundaryWitnessEncodeBHist L))
              (realCompletionBoundaryWitnessDecodeBHist
                (realCompletionBoundaryWitnessEncodeBHist U))
              (realCompletionBoundaryWitnessDecodeBHist
                (realCompletionBoundaryWitnessEncodeBHist H))
              (realCompletionBoundaryWitnessDecodeBHist
                (realCompletionBoundaryWitnessEncodeBHist C))
              (realCompletionBoundaryWitnessDecodeBHist
                (realCompletionBoundaryWitnessEncodeBHist P))
              (realCompletionBoundaryWitnessDecodeBHist
                (realCompletionBoundaryWitnessEncodeBHist N))) =
          some (RealCompletionBoundaryWitnessUp.mk D S R E L U H C P N)
      rw [RealCompletionBoundaryWitnessTasteGate_single_carrier_alignment_decode D]
      rw [RealCompletionBoundaryWitnessTasteGate_single_carrier_alignment_decode S]
      rw [RealCompletionBoundaryWitnessTasteGate_single_carrier_alignment_decode R]
      rw [RealCompletionBoundaryWitnessTasteGate_single_carrier_alignment_decode E]
      rw [RealCompletionBoundaryWitnessTasteGate_single_carrier_alignment_decode L]
      rw [RealCompletionBoundaryWitnessTasteGate_single_carrier_alignment_decode U]
      rw [RealCompletionBoundaryWitnessTasteGate_single_carrier_alignment_decode H]
      rw [RealCompletionBoundaryWitnessTasteGate_single_carrier_alignment_decode C]
      rw [RealCompletionBoundaryWitnessTasteGate_single_carrier_alignment_decode P]
      rw [RealCompletionBoundaryWitnessTasteGate_single_carrier_alignment_decode N]

private theorem RealCompletionBoundaryWitnessTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealCompletionBoundaryWitnessUp} :
    realCompletionBoundaryWitnessToEventFlow x =
        realCompletionBoundaryWitnessToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realCompletionBoundaryWitnessFromEventFlow
          (realCompletionBoundaryWitnessToEventFlow x) =
        realCompletionBoundaryWitnessFromEventFlow
          (realCompletionBoundaryWitnessToEventFlow y) :=
    congrArg realCompletionBoundaryWitnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RealCompletionBoundaryWitnessTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RealCompletionBoundaryWitnessTasteGate_single_carrier_alignment_round_trip y)))

def realCompletionBoundaryWitnessChapterTasteGate :
    ChapterTasteGate RealCompletionBoundaryWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realCompletionBoundaryWitnessFromEventFlow
          (realCompletionBoundaryWitnessToEventFlow x) =
        some x
    exact RealCompletionBoundaryWitnessTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RealCompletionBoundaryWitnessTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

instance realCompletionBoundaryWitnessChapterTasteGateInstance :
    ChapterTasteGate RealCompletionBoundaryWitnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realCompletionBoundaryWitnessChapterTasteGate

theorem RealCompletionBoundaryWitnessTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      realCompletionBoundaryWitnessDecodeBHist
          (realCompletionBoundaryWitnessEncodeBHist h) =
        h) ∧
      Nonempty (BHistCarrier RealCompletionBoundaryWitnessUp) ∧
        Nonempty (ChapterTasteGate RealCompletionBoundaryWitnessUp) ∧
          realCompletionBoundaryWitnessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RealCompletionBoundaryWitnessTasteGate_single_carrier_alignment_decode,
      ⟨realCompletionBoundaryWitnessBHistCarrier⟩,
      ⟨realCompletionBoundaryWitnessChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.RealCompletionBoundaryWitnessUp
