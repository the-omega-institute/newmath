import BEDC.Derived.LesserLimitedOmniscienceUp
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LesserLimitedOmniscienceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def lesserLimitedOmniscienceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: lesserLimitedOmniscienceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: lesserLimitedOmniscienceEncodeBHist h

def lesserLimitedOmniscienceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (lesserLimitedOmniscienceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (lesserLimitedOmniscienceDecodeBHist tail)

private theorem LesserLimitedOmniscienceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      lesserLimitedOmniscienceDecodeBHist (lesserLimitedOmniscienceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def lesserLimitedOmniscienceFields : LesserLimitedOmniscienceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LesserLimitedOmniscienceUp.mk A0 A1 S R D E W H C P N =>
      [A0, A1, S, R, D, E, W, H, C, P, N]

def lesserLimitedOmniscienceToEventFlow : LesserLimitedOmniscienceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (lesserLimitedOmniscienceFields x).map lesserLimitedOmniscienceEncodeBHist

private def lesserLimitedOmniscienceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => lesserLimitedOmniscienceEventAt index rest

def lesserLimitedOmniscienceFromEventFlow :
    EventFlow → Option LesserLimitedOmniscienceUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      some
        (LesserLimitedOmniscienceUp.mk
          (lesserLimitedOmniscienceDecodeBHist (lesserLimitedOmniscienceEventAt 0 flow))
          (lesserLimitedOmniscienceDecodeBHist (lesserLimitedOmniscienceEventAt 1 flow))
          (lesserLimitedOmniscienceDecodeBHist (lesserLimitedOmniscienceEventAt 2 flow))
          (lesserLimitedOmniscienceDecodeBHist (lesserLimitedOmniscienceEventAt 3 flow))
          (lesserLimitedOmniscienceDecodeBHist (lesserLimitedOmniscienceEventAt 4 flow))
          (lesserLimitedOmniscienceDecodeBHist (lesserLimitedOmniscienceEventAt 5 flow))
          (lesserLimitedOmniscienceDecodeBHist (lesserLimitedOmniscienceEventAt 6 flow))
          (lesserLimitedOmniscienceDecodeBHist (lesserLimitedOmniscienceEventAt 7 flow))
          (lesserLimitedOmniscienceDecodeBHist (lesserLimitedOmniscienceEventAt 8 flow))
          (lesserLimitedOmniscienceDecodeBHist (lesserLimitedOmniscienceEventAt 9 flow))
          (lesserLimitedOmniscienceDecodeBHist (lesserLimitedOmniscienceEventAt 10 flow)))

private theorem LesserLimitedOmniscienceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LesserLimitedOmniscienceUp,
      lesserLimitedOmniscienceFromEventFlow (lesserLimitedOmniscienceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A0 A1 S R D E W H C P N =>
      change
        some
          (LesserLimitedOmniscienceUp.mk
            (lesserLimitedOmniscienceDecodeBHist (lesserLimitedOmniscienceEncodeBHist A0))
            (lesserLimitedOmniscienceDecodeBHist (lesserLimitedOmniscienceEncodeBHist A1))
            (lesserLimitedOmniscienceDecodeBHist (lesserLimitedOmniscienceEncodeBHist S))
            (lesserLimitedOmniscienceDecodeBHist (lesserLimitedOmniscienceEncodeBHist R))
            (lesserLimitedOmniscienceDecodeBHist (lesserLimitedOmniscienceEncodeBHist D))
            (lesserLimitedOmniscienceDecodeBHist (lesserLimitedOmniscienceEncodeBHist E))
            (lesserLimitedOmniscienceDecodeBHist (lesserLimitedOmniscienceEncodeBHist W))
            (lesserLimitedOmniscienceDecodeBHist (lesserLimitedOmniscienceEncodeBHist H))
            (lesserLimitedOmniscienceDecodeBHist (lesserLimitedOmniscienceEncodeBHist C))
            (lesserLimitedOmniscienceDecodeBHist (lesserLimitedOmniscienceEncodeBHist P))
            (lesserLimitedOmniscienceDecodeBHist (lesserLimitedOmniscienceEncodeBHist N))) =
          some (LesserLimitedOmniscienceUp.mk A0 A1 S R D E W H C P N)
      rw [LesserLimitedOmniscienceTasteGate_single_carrier_alignment_decode A0,
        LesserLimitedOmniscienceTasteGate_single_carrier_alignment_decode A1,
        LesserLimitedOmniscienceTasteGate_single_carrier_alignment_decode S,
        LesserLimitedOmniscienceTasteGate_single_carrier_alignment_decode R,
        LesserLimitedOmniscienceTasteGate_single_carrier_alignment_decode D,
        LesserLimitedOmniscienceTasteGate_single_carrier_alignment_decode E,
        LesserLimitedOmniscienceTasteGate_single_carrier_alignment_decode W,
        LesserLimitedOmniscienceTasteGate_single_carrier_alignment_decode H,
        LesserLimitedOmniscienceTasteGate_single_carrier_alignment_decode C,
        LesserLimitedOmniscienceTasteGate_single_carrier_alignment_decode P,
        LesserLimitedOmniscienceTasteGate_single_carrier_alignment_decode N]

private theorem LesserLimitedOmniscienceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LesserLimitedOmniscienceUp} :
    lesserLimitedOmniscienceToEventFlow x = lesserLimitedOmniscienceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      lesserLimitedOmniscienceFromEventFlow (lesserLimitedOmniscienceToEventFlow x) =
        lesserLimitedOmniscienceFromEventFlow (lesserLimitedOmniscienceToEventFlow y) :=
    congrArg lesserLimitedOmniscienceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LesserLimitedOmniscienceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LesserLimitedOmniscienceTasteGate_single_carrier_alignment_round_trip y)))

instance lesserLimitedOmniscienceBHistCarrier : BHistCarrier LesserLimitedOmniscienceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := lesserLimitedOmniscienceToEventFlow
  fromEventFlow := lesserLimitedOmniscienceFromEventFlow

instance lesserLimitedOmniscienceChapterTasteGate :
    ChapterTasteGate LesserLimitedOmniscienceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      lesserLimitedOmniscienceFromEventFlow (lesserLimitedOmniscienceToEventFlow x) =
        some x
    exact LesserLimitedOmniscienceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (LesserLimitedOmniscienceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem LesserLimitedOmniscienceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      lesserLimitedOmniscienceDecodeBHist (lesserLimitedOmniscienceEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier LesserLimitedOmniscienceUp) ∧
        Nonempty (ChapterTasteGate LesserLimitedOmniscienceUp) ∧
          lesserLimitedOmniscienceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨LesserLimitedOmniscienceTasteGate_single_carrier_alignment_decode,
      ⟨lesserLimitedOmniscienceBHistCarrier⟩,
      ⟨lesserLimitedOmniscienceChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.LesserLimitedOmniscienceUp
