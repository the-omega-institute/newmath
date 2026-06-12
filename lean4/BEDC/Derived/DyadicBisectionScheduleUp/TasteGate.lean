import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicBisectionScheduleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicBisectionScheduleUp : Type where
  | mk (I B D W R Q H C P N : BHist) : DyadicBisectionScheduleUp
  deriving DecidableEq

def dyadicBisectionScheduleEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicBisectionScheduleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicBisectionScheduleEncodeBHist h

def dyadicBisectionScheduleDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicBisectionScheduleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicBisectionScheduleDecodeBHist tail)

private theorem dyadicBisectionScheduleDecode_encode_bhist :
    ∀ h : BHist,
      dyadicBisectionScheduleDecodeBHist
        (dyadicBisectionScheduleEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicBisectionScheduleFields : DyadicBisectionScheduleUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicBisectionScheduleUp.mk I B D W R Q H C P N => [I, B, D, W, R, Q, H, C, P, N]

def dyadicBisectionScheduleToEventFlow : DyadicBisectionScheduleUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dyadicBisectionScheduleFields x).map dyadicBisectionScheduleEncodeBHist

private def dyadicBisectionScheduleEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dyadicBisectionScheduleEventAt index rest

def dyadicBisectionScheduleFromEventFlow (ef : EventFlow) :
    Option DyadicBisectionScheduleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DyadicBisectionScheduleUp.mk
      (dyadicBisectionScheduleDecodeBHist (dyadicBisectionScheduleEventAt 0 ef))
      (dyadicBisectionScheduleDecodeBHist (dyadicBisectionScheduleEventAt 1 ef))
      (dyadicBisectionScheduleDecodeBHist (dyadicBisectionScheduleEventAt 2 ef))
      (dyadicBisectionScheduleDecodeBHist (dyadicBisectionScheduleEventAt 3 ef))
      (dyadicBisectionScheduleDecodeBHist (dyadicBisectionScheduleEventAt 4 ef))
      (dyadicBisectionScheduleDecodeBHist (dyadicBisectionScheduleEventAt 5 ef))
      (dyadicBisectionScheduleDecodeBHist (dyadicBisectionScheduleEventAt 6 ef))
      (dyadicBisectionScheduleDecodeBHist (dyadicBisectionScheduleEventAt 7 ef))
      (dyadicBisectionScheduleDecodeBHist (dyadicBisectionScheduleEventAt 8 ef))
      (dyadicBisectionScheduleDecodeBHist (dyadicBisectionScheduleEventAt 9 ef)))

private theorem dyadicBisectionSchedule_round_trip (x : DyadicBisectionScheduleUp) :
    dyadicBisectionScheduleFromEventFlow
        (dyadicBisectionScheduleToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I B D W R Q H C P N =>
      change
        some
          (DyadicBisectionScheduleUp.mk
            (dyadicBisectionScheduleDecodeBHist (dyadicBisectionScheduleEncodeBHist I))
            (dyadicBisectionScheduleDecodeBHist (dyadicBisectionScheduleEncodeBHist B))
            (dyadicBisectionScheduleDecodeBHist (dyadicBisectionScheduleEncodeBHist D))
            (dyadicBisectionScheduleDecodeBHist (dyadicBisectionScheduleEncodeBHist W))
            (dyadicBisectionScheduleDecodeBHist (dyadicBisectionScheduleEncodeBHist R))
            (dyadicBisectionScheduleDecodeBHist (dyadicBisectionScheduleEncodeBHist Q))
            (dyadicBisectionScheduleDecodeBHist (dyadicBisectionScheduleEncodeBHist H))
            (dyadicBisectionScheduleDecodeBHist (dyadicBisectionScheduleEncodeBHist C))
            (dyadicBisectionScheduleDecodeBHist (dyadicBisectionScheduleEncodeBHist P))
            (dyadicBisectionScheduleDecodeBHist (dyadicBisectionScheduleEncodeBHist N))) =
          some (DyadicBisectionScheduleUp.mk I B D W R Q H C P N)
      rw [dyadicBisectionScheduleDecode_encode_bhist I,
        dyadicBisectionScheduleDecode_encode_bhist B,
        dyadicBisectionScheduleDecode_encode_bhist D,
        dyadicBisectionScheduleDecode_encode_bhist W,
        dyadicBisectionScheduleDecode_encode_bhist R,
        dyadicBisectionScheduleDecode_encode_bhist Q,
        dyadicBisectionScheduleDecode_encode_bhist H,
        dyadicBisectionScheduleDecode_encode_bhist C,
        dyadicBisectionScheduleDecode_encode_bhist P,
        dyadicBisectionScheduleDecode_encode_bhist N]

private theorem dyadicBisectionScheduleToEventFlow_injective
    {x y : DyadicBisectionScheduleUp} :
    dyadicBisectionScheduleToEventFlow x =
      dyadicBisectionScheduleToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicBisectionScheduleFromEventFlow (dyadicBisectionScheduleToEventFlow x) =
        dyadicBisectionScheduleFromEventFlow (dyadicBisectionScheduleToEventFlow y) :=
    congrArg dyadicBisectionScheduleFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dyadicBisectionSchedule_round_trip x).symm
      (Eq.trans hread (dyadicBisectionSchedule_round_trip y)))

instance dyadicBisectionScheduleBHistCarrier :
    BHistCarrier DyadicBisectionScheduleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicBisectionScheduleToEventFlow
  fromEventFlow := dyadicBisectionScheduleFromEventFlow

instance dyadicBisectionScheduleChapterTasteGate :
    ChapterTasteGate DyadicBisectionScheduleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicBisectionScheduleFromEventFlow
      (dyadicBisectionScheduleToEventFlow x) = some x
    exact dyadicBisectionSchedule_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dyadicBisectionScheduleToEventFlow_injective heq)

def taste_gate : ChapterTasteGate DyadicBisectionScheduleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicBisectionScheduleChapterTasteGate

theorem DyadicBisectionScheduleTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier DyadicBisectionScheduleUp) ∧
      Nonempty (ChapterTasteGate DyadicBisectionScheduleUp) ∧
        (∀ h : BHist,
          dyadicBisectionScheduleDecodeBHist
              (dyadicBisectionScheduleEncodeBHist h) = h) ∧
          (∀ x : DyadicBisectionScheduleUp,
            dyadicBisectionScheduleFromEventFlow
                (dyadicBisectionScheduleToEventFlow x) = some x) ∧
            dyadicBisectionScheduleEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact ⟨dyadicBisectionScheduleBHistCarrier⟩
  · constructor
    · exact ⟨dyadicBisectionScheduleChapterTasteGate⟩
    · constructor
      · exact dyadicBisectionScheduleDecode_encode_bhist
      · constructor
        · exact dyadicBisectionSchedule_round_trip
        · rfl

end BEDC.Derived.DyadicBisectionScheduleUp
