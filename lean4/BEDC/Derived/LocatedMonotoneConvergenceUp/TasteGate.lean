import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedMonotoneConvergenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedMonotoneConvergenceUp : Type where
  | mk (M B U W R D E H C P N : BHist) : LocatedMonotoneConvergenceUp
  deriving DecidableEq

def locatedMonotoneConvergenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedMonotoneConvergenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedMonotoneConvergenceEncodeBHist h

def locatedMonotoneConvergenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedMonotoneConvergenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedMonotoneConvergenceDecodeBHist tail)

private theorem LocatedMonotoneConvergenceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      locatedMonotoneConvergenceDecodeBHist
        (locatedMonotoneConvergenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedMonotoneConvergenceFields : LocatedMonotoneConvergenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedMonotoneConvergenceUp.mk M B U W R D E H C P N =>
      [M, B, U, W, R, D, E, H, C, P, N]

def locatedMonotoneConvergenceToEventFlow : LocatedMonotoneConvergenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedMonotoneConvergenceFields x).map locatedMonotoneConvergenceEncodeBHist

private def locatedMonotoneConvergenceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedMonotoneConvergenceEventAtDefault index rest

def locatedMonotoneConvergenceFromEventFlow
    (ef : EventFlow) : Option LocatedMonotoneConvergenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedMonotoneConvergenceUp.mk
      (locatedMonotoneConvergenceDecodeBHist
        (locatedMonotoneConvergenceEventAtDefault 0 ef))
      (locatedMonotoneConvergenceDecodeBHist
        (locatedMonotoneConvergenceEventAtDefault 1 ef))
      (locatedMonotoneConvergenceDecodeBHist
        (locatedMonotoneConvergenceEventAtDefault 2 ef))
      (locatedMonotoneConvergenceDecodeBHist
        (locatedMonotoneConvergenceEventAtDefault 3 ef))
      (locatedMonotoneConvergenceDecodeBHist
        (locatedMonotoneConvergenceEventAtDefault 4 ef))
      (locatedMonotoneConvergenceDecodeBHist
        (locatedMonotoneConvergenceEventAtDefault 5 ef))
      (locatedMonotoneConvergenceDecodeBHist
        (locatedMonotoneConvergenceEventAtDefault 6 ef))
      (locatedMonotoneConvergenceDecodeBHist
        (locatedMonotoneConvergenceEventAtDefault 7 ef))
      (locatedMonotoneConvergenceDecodeBHist
        (locatedMonotoneConvergenceEventAtDefault 8 ef))
      (locatedMonotoneConvergenceDecodeBHist
        (locatedMonotoneConvergenceEventAtDefault 9 ef))
      (locatedMonotoneConvergenceDecodeBHist
        (locatedMonotoneConvergenceEventAtDefault 10 ef)))

private theorem LocatedMonotoneConvergenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LocatedMonotoneConvergenceUp,
      locatedMonotoneConvergenceFromEventFlow
        (locatedMonotoneConvergenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M B U W R D E H C P N =>
      change
        some
          (LocatedMonotoneConvergenceUp.mk
            (locatedMonotoneConvergenceDecodeBHist
              (locatedMonotoneConvergenceEncodeBHist M))
            (locatedMonotoneConvergenceDecodeBHist
              (locatedMonotoneConvergenceEncodeBHist B))
            (locatedMonotoneConvergenceDecodeBHist
              (locatedMonotoneConvergenceEncodeBHist U))
            (locatedMonotoneConvergenceDecodeBHist
              (locatedMonotoneConvergenceEncodeBHist W))
            (locatedMonotoneConvergenceDecodeBHist
              (locatedMonotoneConvergenceEncodeBHist R))
            (locatedMonotoneConvergenceDecodeBHist
              (locatedMonotoneConvergenceEncodeBHist D))
            (locatedMonotoneConvergenceDecodeBHist
              (locatedMonotoneConvergenceEncodeBHist E))
            (locatedMonotoneConvergenceDecodeBHist
              (locatedMonotoneConvergenceEncodeBHist H))
            (locatedMonotoneConvergenceDecodeBHist
              (locatedMonotoneConvergenceEncodeBHist C))
            (locatedMonotoneConvergenceDecodeBHist
              (locatedMonotoneConvergenceEncodeBHist P))
            (locatedMonotoneConvergenceDecodeBHist
              (locatedMonotoneConvergenceEncodeBHist N))) =
          some (LocatedMonotoneConvergenceUp.mk M B U W R D E H C P N)
      rw [LocatedMonotoneConvergenceTasteGate_single_carrier_alignment_decode M,
        LocatedMonotoneConvergenceTasteGate_single_carrier_alignment_decode B,
        LocatedMonotoneConvergenceTasteGate_single_carrier_alignment_decode U,
        LocatedMonotoneConvergenceTasteGate_single_carrier_alignment_decode W,
        LocatedMonotoneConvergenceTasteGate_single_carrier_alignment_decode R,
        LocatedMonotoneConvergenceTasteGate_single_carrier_alignment_decode D,
        LocatedMonotoneConvergenceTasteGate_single_carrier_alignment_decode E,
        LocatedMonotoneConvergenceTasteGate_single_carrier_alignment_decode H,
        LocatedMonotoneConvergenceTasteGate_single_carrier_alignment_decode C,
        LocatedMonotoneConvergenceTasteGate_single_carrier_alignment_decode P,
        LocatedMonotoneConvergenceTasteGate_single_carrier_alignment_decode N]

private theorem LocatedMonotoneConvergenceTasteGate_single_carrier_alignment_injective
    {x y : LocatedMonotoneConvergenceUp} :
    locatedMonotoneConvergenceToEventFlow x =
      locatedMonotoneConvergenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedMonotoneConvergenceFromEventFlow
          (locatedMonotoneConvergenceToEventFlow x) =
        locatedMonotoneConvergenceFromEventFlow
          (locatedMonotoneConvergenceToEventFlow y) :=
    congrArg locatedMonotoneConvergenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LocatedMonotoneConvergenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LocatedMonotoneConvergenceTasteGate_single_carrier_alignment_round_trip y)))

instance locatedMonotoneConvergenceBHistCarrier :
    BHistCarrier LocatedMonotoneConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedMonotoneConvergenceToEventFlow
  fromEventFlow := locatedMonotoneConvergenceFromEventFlow

instance locatedMonotoneConvergenceChapterTasteGate :
    ChapterTasteGate LocatedMonotoneConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      locatedMonotoneConvergenceFromEventFlow
        (locatedMonotoneConvergenceToEventFlow x) = some x
    exact LocatedMonotoneConvergenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LocatedMonotoneConvergenceTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate LocatedMonotoneConvergenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedMonotoneConvergenceChapterTasteGate

theorem LocatedMonotoneConvergenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      locatedMonotoneConvergenceDecodeBHist
        (locatedMonotoneConvergenceEncodeBHist h) = h) ∧
      (∀ x : LocatedMonotoneConvergenceUp,
        locatedMonotoneConvergenceFromEventFlow
          (locatedMonotoneConvergenceToEventFlow x) = some x) ∧
        (∀ x y : LocatedMonotoneConvergenceUp,
          locatedMonotoneConvergenceToEventFlow x =
            locatedMonotoneConvergenceToEventFlow y → x = y) ∧
          locatedMonotoneConvergenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨LocatedMonotoneConvergenceTasteGate_single_carrier_alignment_decode,
      LocatedMonotoneConvergenceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        LocatedMonotoneConvergenceTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.LocatedMonotoneConvergenceUp
