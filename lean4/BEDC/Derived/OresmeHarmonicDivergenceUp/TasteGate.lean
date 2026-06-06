import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.OresmeHarmonicDivergenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive OresmeHarmonicDivergenceUp : Type where
  | mk (S B Q D W R E T C P N : BHist) : OresmeHarmonicDivergenceUp
  deriving DecidableEq

def oresmeHarmonicDivergenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: oresmeHarmonicDivergenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: oresmeHarmonicDivergenceEncodeBHist h

def oresmeHarmonicDivergenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (oresmeHarmonicDivergenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (oresmeHarmonicDivergenceDecodeBHist tail)

private theorem OresmeHarmonicDivergenceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      oresmeHarmonicDivergenceDecodeBHist
          (oresmeHarmonicDivergenceEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def oresmeHarmonicDivergenceToEventFlow : OresmeHarmonicDivergenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | OresmeHarmonicDivergenceUp.mk S B Q D W R E T C P N =>
      [oresmeHarmonicDivergenceEncodeBHist S,
        oresmeHarmonicDivergenceEncodeBHist B,
        oresmeHarmonicDivergenceEncodeBHist Q,
        oresmeHarmonicDivergenceEncodeBHist D,
        oresmeHarmonicDivergenceEncodeBHist W,
        oresmeHarmonicDivergenceEncodeBHist R,
        oresmeHarmonicDivergenceEncodeBHist E,
        oresmeHarmonicDivergenceEncodeBHist T,
        oresmeHarmonicDivergenceEncodeBHist C,
        oresmeHarmonicDivergenceEncodeBHist P,
        oresmeHarmonicDivergenceEncodeBHist N]

private def oresmeHarmonicDivergenceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => oresmeHarmonicDivergenceEventAtDefault index rest

def oresmeHarmonicDivergenceFromEventFlow
    (ef : EventFlow) : Option OresmeHarmonicDivergenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (OresmeHarmonicDivergenceUp.mk
      (oresmeHarmonicDivergenceDecodeBHist
        (oresmeHarmonicDivergenceEventAtDefault 0 ef))
      (oresmeHarmonicDivergenceDecodeBHist
        (oresmeHarmonicDivergenceEventAtDefault 1 ef))
      (oresmeHarmonicDivergenceDecodeBHist
        (oresmeHarmonicDivergenceEventAtDefault 2 ef))
      (oresmeHarmonicDivergenceDecodeBHist
        (oresmeHarmonicDivergenceEventAtDefault 3 ef))
      (oresmeHarmonicDivergenceDecodeBHist
        (oresmeHarmonicDivergenceEventAtDefault 4 ef))
      (oresmeHarmonicDivergenceDecodeBHist
        (oresmeHarmonicDivergenceEventAtDefault 5 ef))
      (oresmeHarmonicDivergenceDecodeBHist
        (oresmeHarmonicDivergenceEventAtDefault 6 ef))
      (oresmeHarmonicDivergenceDecodeBHist
        (oresmeHarmonicDivergenceEventAtDefault 7 ef))
      (oresmeHarmonicDivergenceDecodeBHist
        (oresmeHarmonicDivergenceEventAtDefault 8 ef))
      (oresmeHarmonicDivergenceDecodeBHist
        (oresmeHarmonicDivergenceEventAtDefault 9 ef))
      (oresmeHarmonicDivergenceDecodeBHist
        (oresmeHarmonicDivergenceEventAtDefault 10 ef)))

private theorem OresmeHarmonicDivergenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : OresmeHarmonicDivergenceUp,
      oresmeHarmonicDivergenceFromEventFlow
          (oresmeHarmonicDivergenceToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S B Q D W R E T C P N =>
      change
        some
            (OresmeHarmonicDivergenceUp.mk
              (oresmeHarmonicDivergenceDecodeBHist
                (oresmeHarmonicDivergenceEncodeBHist S))
              (oresmeHarmonicDivergenceDecodeBHist
                (oresmeHarmonicDivergenceEncodeBHist B))
              (oresmeHarmonicDivergenceDecodeBHist
                (oresmeHarmonicDivergenceEncodeBHist Q))
              (oresmeHarmonicDivergenceDecodeBHist
                (oresmeHarmonicDivergenceEncodeBHist D))
              (oresmeHarmonicDivergenceDecodeBHist
                (oresmeHarmonicDivergenceEncodeBHist W))
              (oresmeHarmonicDivergenceDecodeBHist
                (oresmeHarmonicDivergenceEncodeBHist R))
              (oresmeHarmonicDivergenceDecodeBHist
                (oresmeHarmonicDivergenceEncodeBHist E))
              (oresmeHarmonicDivergenceDecodeBHist
                (oresmeHarmonicDivergenceEncodeBHist T))
              (oresmeHarmonicDivergenceDecodeBHist
                (oresmeHarmonicDivergenceEncodeBHist C))
              (oresmeHarmonicDivergenceDecodeBHist
                (oresmeHarmonicDivergenceEncodeBHist P))
              (oresmeHarmonicDivergenceDecodeBHist
                (oresmeHarmonicDivergenceEncodeBHist N))) =
          some (OresmeHarmonicDivergenceUp.mk S B Q D W R E T C P N)
      rw [OresmeHarmonicDivergenceTasteGate_single_carrier_alignment_decode S,
        OresmeHarmonicDivergenceTasteGate_single_carrier_alignment_decode B,
        OresmeHarmonicDivergenceTasteGate_single_carrier_alignment_decode Q,
        OresmeHarmonicDivergenceTasteGate_single_carrier_alignment_decode D,
        OresmeHarmonicDivergenceTasteGate_single_carrier_alignment_decode W,
        OresmeHarmonicDivergenceTasteGate_single_carrier_alignment_decode R,
        OresmeHarmonicDivergenceTasteGate_single_carrier_alignment_decode E,
        OresmeHarmonicDivergenceTasteGate_single_carrier_alignment_decode T,
        OresmeHarmonicDivergenceTasteGate_single_carrier_alignment_decode C,
        OresmeHarmonicDivergenceTasteGate_single_carrier_alignment_decode P,
        OresmeHarmonicDivergenceTasteGate_single_carrier_alignment_decode N]

private theorem
    OresmeHarmonicDivergenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : OresmeHarmonicDivergenceUp} :
    oresmeHarmonicDivergenceToEventFlow x = oresmeHarmonicDivergenceToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      oresmeHarmonicDivergenceFromEventFlow (oresmeHarmonicDivergenceToEventFlow x) =
        oresmeHarmonicDivergenceFromEventFlow
          (oresmeHarmonicDivergenceToEventFlow y) :=
    congrArg oresmeHarmonicDivergenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (OresmeHarmonicDivergenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (OresmeHarmonicDivergenceTasteGate_single_carrier_alignment_round_trip y)))

instance oresmeHarmonicDivergenceBHistCarrier :
    BHistCarrier OresmeHarmonicDivergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := oresmeHarmonicDivergenceToEventFlow
  fromEventFlow := oresmeHarmonicDivergenceFromEventFlow

instance oresmeHarmonicDivergenceChapterTasteGate :
    ChapterTasteGate OresmeHarmonicDivergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      oresmeHarmonicDivergenceFromEventFlow
          (oresmeHarmonicDivergenceToEventFlow x) =
        some x
    exact OresmeHarmonicDivergenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (OresmeHarmonicDivergenceTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

def taste_gate : ChapterTasteGate OresmeHarmonicDivergenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  oresmeHarmonicDivergenceChapterTasteGate

theorem OresmeHarmonicDivergenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        oresmeHarmonicDivergenceDecodeBHist
            (oresmeHarmonicDivergenceEncodeBHist h) =
          h) ∧
      (∀ x : OresmeHarmonicDivergenceUp,
        oresmeHarmonicDivergenceFromEventFlow
            (oresmeHarmonicDivergenceToEventFlow x) =
          some x) ∧
        (∀ x y : OresmeHarmonicDivergenceUp,
          oresmeHarmonicDivergenceToEventFlow x =
              oresmeHarmonicDivergenceToEventFlow y →
            x = y) ∧
          oresmeHarmonicDivergenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨OresmeHarmonicDivergenceTasteGate_single_carrier_alignment_decode,
      OresmeHarmonicDivergenceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        OresmeHarmonicDivergenceTasteGate_single_carrier_alignment_toEventFlow_injective
          heq),
      rfl⟩

end BEDC.Derived.OresmeHarmonicDivergenceUp
