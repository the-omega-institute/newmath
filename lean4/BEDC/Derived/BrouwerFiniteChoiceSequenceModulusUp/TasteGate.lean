import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BrouwerFiniteChoiceSequenceModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BrouwerFiniteChoiceSequenceModulusUp : Type where
  | mk (B Q W R E M H C P N : BHist) : BrouwerFiniteChoiceSequenceModulusUp
  deriving DecidableEq

def brouwerFiniteChoiceSequenceModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: brouwerFiniteChoiceSequenceModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: brouwerFiniteChoiceSequenceModulusEncodeBHist h

def brouwerFiniteChoiceSequenceModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (brouwerFiniteChoiceSequenceModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (brouwerFiniteChoiceSequenceModulusDecodeBHist tail)

private theorem BrouwerFiniteChoiceSequenceModulusTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      brouwerFiniteChoiceSequenceModulusDecodeBHist
        (brouwerFiniteChoiceSequenceModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def brouwerFiniteChoiceSequenceModulusFields :
    BrouwerFiniteChoiceSequenceModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BrouwerFiniteChoiceSequenceModulusUp.mk B Q W R E M H C P N =>
      [B, Q, W, R, E, M, H, C, P, N]

def brouwerFiniteChoiceSequenceModulusToEventFlow :
    BrouwerFiniteChoiceSequenceModulusUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (brouwerFiniteChoiceSequenceModulusFields x).map
      brouwerFiniteChoiceSequenceModulusEncodeBHist

private def brouwerFiniteChoiceSequenceModulusEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => brouwerFiniteChoiceSequenceModulusEventAtDefault index rest

def brouwerFiniteChoiceSequenceModulusFromEventFlow :
    EventFlow → Option BrouwerFiniteChoiceSequenceModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (BrouwerFiniteChoiceSequenceModulusUp.mk
        (brouwerFiniteChoiceSequenceModulusDecodeBHist
          (brouwerFiniteChoiceSequenceModulusEventAtDefault 0 ef))
        (brouwerFiniteChoiceSequenceModulusDecodeBHist
          (brouwerFiniteChoiceSequenceModulusEventAtDefault 1 ef))
        (brouwerFiniteChoiceSequenceModulusDecodeBHist
          (brouwerFiniteChoiceSequenceModulusEventAtDefault 2 ef))
        (brouwerFiniteChoiceSequenceModulusDecodeBHist
          (brouwerFiniteChoiceSequenceModulusEventAtDefault 3 ef))
        (brouwerFiniteChoiceSequenceModulusDecodeBHist
          (brouwerFiniteChoiceSequenceModulusEventAtDefault 4 ef))
        (brouwerFiniteChoiceSequenceModulusDecodeBHist
          (brouwerFiniteChoiceSequenceModulusEventAtDefault 5 ef))
        (brouwerFiniteChoiceSequenceModulusDecodeBHist
          (brouwerFiniteChoiceSequenceModulusEventAtDefault 6 ef))
        (brouwerFiniteChoiceSequenceModulusDecodeBHist
          (brouwerFiniteChoiceSequenceModulusEventAtDefault 7 ef))
        (brouwerFiniteChoiceSequenceModulusDecodeBHist
          (brouwerFiniteChoiceSequenceModulusEventAtDefault 8 ef))
        (brouwerFiniteChoiceSequenceModulusDecodeBHist
          (brouwerFiniteChoiceSequenceModulusEventAtDefault 9 ef)))

private theorem BrouwerFiniteChoiceSequenceModulusTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BrouwerFiniteChoiceSequenceModulusUp,
      brouwerFiniteChoiceSequenceModulusFromEventFlow
          (brouwerFiniteChoiceSequenceModulusToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B Q W R E M H C P N =>
      change
        some
          (BrouwerFiniteChoiceSequenceModulusUp.mk
            (brouwerFiniteChoiceSequenceModulusDecodeBHist
              (brouwerFiniteChoiceSequenceModulusEncodeBHist B))
            (brouwerFiniteChoiceSequenceModulusDecodeBHist
              (brouwerFiniteChoiceSequenceModulusEncodeBHist Q))
            (brouwerFiniteChoiceSequenceModulusDecodeBHist
              (brouwerFiniteChoiceSequenceModulusEncodeBHist W))
            (brouwerFiniteChoiceSequenceModulusDecodeBHist
              (brouwerFiniteChoiceSequenceModulusEncodeBHist R))
            (brouwerFiniteChoiceSequenceModulusDecodeBHist
              (brouwerFiniteChoiceSequenceModulusEncodeBHist E))
            (brouwerFiniteChoiceSequenceModulusDecodeBHist
              (brouwerFiniteChoiceSequenceModulusEncodeBHist M))
            (brouwerFiniteChoiceSequenceModulusDecodeBHist
              (brouwerFiniteChoiceSequenceModulusEncodeBHist H))
            (brouwerFiniteChoiceSequenceModulusDecodeBHist
              (brouwerFiniteChoiceSequenceModulusEncodeBHist C))
            (brouwerFiniteChoiceSequenceModulusDecodeBHist
              (brouwerFiniteChoiceSequenceModulusEncodeBHist P))
            (brouwerFiniteChoiceSequenceModulusDecodeBHist
              (brouwerFiniteChoiceSequenceModulusEncodeBHist N))) =
          some (BrouwerFiniteChoiceSequenceModulusUp.mk B Q W R E M H C P N)
      rw [BrouwerFiniteChoiceSequenceModulusTasteGate_single_carrier_alignment_decode B,
        BrouwerFiniteChoiceSequenceModulusTasteGate_single_carrier_alignment_decode Q,
        BrouwerFiniteChoiceSequenceModulusTasteGate_single_carrier_alignment_decode W,
        BrouwerFiniteChoiceSequenceModulusTasteGate_single_carrier_alignment_decode R,
        BrouwerFiniteChoiceSequenceModulusTasteGate_single_carrier_alignment_decode E,
        BrouwerFiniteChoiceSequenceModulusTasteGate_single_carrier_alignment_decode M,
        BrouwerFiniteChoiceSequenceModulusTasteGate_single_carrier_alignment_decode H,
        BrouwerFiniteChoiceSequenceModulusTasteGate_single_carrier_alignment_decode C,
        BrouwerFiniteChoiceSequenceModulusTasteGate_single_carrier_alignment_decode P,
        BrouwerFiniteChoiceSequenceModulusTasteGate_single_carrier_alignment_decode N]

private theorem BrouwerFiniteChoiceSequenceModulusTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BrouwerFiniteChoiceSequenceModulusUp} :
    brouwerFiniteChoiceSequenceModulusToEventFlow x =
        brouwerFiniteChoiceSequenceModulusToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      brouwerFiniteChoiceSequenceModulusFromEventFlow
          (brouwerFiniteChoiceSequenceModulusToEventFlow x) =
        brouwerFiniteChoiceSequenceModulusFromEventFlow
          (brouwerFiniteChoiceSequenceModulusToEventFlow y) :=
    congrArg brouwerFiniteChoiceSequenceModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BrouwerFiniteChoiceSequenceModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BrouwerFiniteChoiceSequenceModulusTasteGate_single_carrier_alignment_round_trip y)))

instance brouwerFiniteChoiceSequenceModulusBHistCarrier :
    BHistCarrier BrouwerFiniteChoiceSequenceModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := brouwerFiniteChoiceSequenceModulusToEventFlow
  fromEventFlow := brouwerFiniteChoiceSequenceModulusFromEventFlow

instance brouwerFiniteChoiceSequenceModulusChapterTasteGate :
    ChapterTasteGate BrouwerFiniteChoiceSequenceModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      brouwerFiniteChoiceSequenceModulusFromEventFlow
          (brouwerFiniteChoiceSequenceModulusToEventFlow x) =
        some x
    exact BrouwerFiniteChoiceSequenceModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BrouwerFiniteChoiceSequenceModulusTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

def taste_gate : ChapterTasteGate BrouwerFiniteChoiceSequenceModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  brouwerFiniteChoiceSequenceModulusChapterTasteGate

theorem BrouwerFiniteChoiceSequenceModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      brouwerFiniteChoiceSequenceModulusDecodeBHist
          (brouwerFiniteChoiceSequenceModulusEncodeBHist h) =
        h) ∧
      (∀ x : BrouwerFiniteChoiceSequenceModulusUp,
        brouwerFiniteChoiceSequenceModulusFromEventFlow
            (brouwerFiniteChoiceSequenceModulusToEventFlow x) =
          some x) ∧
        (∀ x y : BrouwerFiniteChoiceSequenceModulusUp,
          brouwerFiniteChoiceSequenceModulusToEventFlow x =
              brouwerFiniteChoiceSequenceModulusToEventFlow y →
            x = y) ∧
          brouwerFiniteChoiceSequenceModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨BrouwerFiniteChoiceSequenceModulusTasteGate_single_carrier_alignment_decode,
      BrouwerFiniteChoiceSequenceModulusTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        BrouwerFiniteChoiceSequenceModulusTasteGate_single_carrier_alignment_toEventFlow_injective
          heq),
      rfl⟩

end BEDC.Derived.BrouwerFiniteChoiceSequenceModulusUp
