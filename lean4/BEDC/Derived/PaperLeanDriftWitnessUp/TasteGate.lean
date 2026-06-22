import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PaperLeanDriftWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PaperLeanDriftWitnessUp : Type where
  | mk (M A L I R H C P N : BHist) : PaperLeanDriftWitnessUp
  deriving DecidableEq

def PaperLeanDriftWitnessTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 :: PaperLeanDriftWitnessTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h =>
      BMark.b1 :: PaperLeanDriftWitnessTasteGate_single_carrier_alignment_encodeBHist h

def PaperLeanDriftWitnessTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (PaperLeanDriftWitnessTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (PaperLeanDriftWitnessTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem PaperLeanDriftWitnessTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      PaperLeanDriftWitnessTasteGate_single_carrier_alignment_decodeBHist
        (PaperLeanDriftWitnessTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def PaperLeanDriftWitnessTasteGate_single_carrier_alignment_fields :
    PaperLeanDriftWitnessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PaperLeanDriftWitnessUp.mk M A L I R H C P N => [M, A, L, I, R, H, C, P, N]

def PaperLeanDriftWitnessTasteGate_single_carrier_alignment_toEventFlow :
    PaperLeanDriftWitnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (PaperLeanDriftWitnessTasteGate_single_carrier_alignment_fields x).map
        PaperLeanDriftWitnessTasteGate_single_carrier_alignment_encodeBHist

private def PaperLeanDriftWitnessTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      PaperLeanDriftWitnessTasteGate_single_carrier_alignment_eventAt index rest

def PaperLeanDriftWitnessTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option PaperLeanDriftWitnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (PaperLeanDriftWitnessUp.mk
        (PaperLeanDriftWitnessTasteGate_single_carrier_alignment_decodeBHist
          (PaperLeanDriftWitnessTasteGate_single_carrier_alignment_eventAt 0 ef))
        (PaperLeanDriftWitnessTasteGate_single_carrier_alignment_decodeBHist
          (PaperLeanDriftWitnessTasteGate_single_carrier_alignment_eventAt 1 ef))
        (PaperLeanDriftWitnessTasteGate_single_carrier_alignment_decodeBHist
          (PaperLeanDriftWitnessTasteGate_single_carrier_alignment_eventAt 2 ef))
        (PaperLeanDriftWitnessTasteGate_single_carrier_alignment_decodeBHist
          (PaperLeanDriftWitnessTasteGate_single_carrier_alignment_eventAt 3 ef))
        (PaperLeanDriftWitnessTasteGate_single_carrier_alignment_decodeBHist
          (PaperLeanDriftWitnessTasteGate_single_carrier_alignment_eventAt 4 ef))
        (PaperLeanDriftWitnessTasteGate_single_carrier_alignment_decodeBHist
          (PaperLeanDriftWitnessTasteGate_single_carrier_alignment_eventAt 5 ef))
        (PaperLeanDriftWitnessTasteGate_single_carrier_alignment_decodeBHist
          (PaperLeanDriftWitnessTasteGate_single_carrier_alignment_eventAt 6 ef))
        (PaperLeanDriftWitnessTasteGate_single_carrier_alignment_decodeBHist
          (PaperLeanDriftWitnessTasteGate_single_carrier_alignment_eventAt 7 ef))
        (PaperLeanDriftWitnessTasteGate_single_carrier_alignment_decodeBHist
          (PaperLeanDriftWitnessTasteGate_single_carrier_alignment_eventAt 8 ef)))

private theorem PaperLeanDriftWitnessTasteGate_single_carrier_alignment_round_trip
    (x : PaperLeanDriftWitnessUp) :
    PaperLeanDriftWitnessTasteGate_single_carrier_alignment_fromEventFlow
        (PaperLeanDriftWitnessTasteGate_single_carrier_alignment_toEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk M A L I R H C P N =>
      change
        some
          (PaperLeanDriftWitnessUp.mk
            (PaperLeanDriftWitnessTasteGate_single_carrier_alignment_decodeBHist
              (PaperLeanDriftWitnessTasteGate_single_carrier_alignment_encodeBHist M))
            (PaperLeanDriftWitnessTasteGate_single_carrier_alignment_decodeBHist
              (PaperLeanDriftWitnessTasteGate_single_carrier_alignment_encodeBHist A))
            (PaperLeanDriftWitnessTasteGate_single_carrier_alignment_decodeBHist
              (PaperLeanDriftWitnessTasteGate_single_carrier_alignment_encodeBHist L))
            (PaperLeanDriftWitnessTasteGate_single_carrier_alignment_decodeBHist
              (PaperLeanDriftWitnessTasteGate_single_carrier_alignment_encodeBHist I))
            (PaperLeanDriftWitnessTasteGate_single_carrier_alignment_decodeBHist
              (PaperLeanDriftWitnessTasteGate_single_carrier_alignment_encodeBHist R))
            (PaperLeanDriftWitnessTasteGate_single_carrier_alignment_decodeBHist
              (PaperLeanDriftWitnessTasteGate_single_carrier_alignment_encodeBHist H))
            (PaperLeanDriftWitnessTasteGate_single_carrier_alignment_decodeBHist
              (PaperLeanDriftWitnessTasteGate_single_carrier_alignment_encodeBHist C))
            (PaperLeanDriftWitnessTasteGate_single_carrier_alignment_decodeBHist
              (PaperLeanDriftWitnessTasteGate_single_carrier_alignment_encodeBHist P))
            (PaperLeanDriftWitnessTasteGate_single_carrier_alignment_decodeBHist
              (PaperLeanDriftWitnessTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (PaperLeanDriftWitnessUp.mk M A L I R H C P N)
      rw [PaperLeanDriftWitnessTasteGate_single_carrier_alignment_decode_encode M,
        PaperLeanDriftWitnessTasteGate_single_carrier_alignment_decode_encode A,
        PaperLeanDriftWitnessTasteGate_single_carrier_alignment_decode_encode L,
        PaperLeanDriftWitnessTasteGate_single_carrier_alignment_decode_encode I,
        PaperLeanDriftWitnessTasteGate_single_carrier_alignment_decode_encode R,
        PaperLeanDriftWitnessTasteGate_single_carrier_alignment_decode_encode H,
        PaperLeanDriftWitnessTasteGate_single_carrier_alignment_decode_encode C,
        PaperLeanDriftWitnessTasteGate_single_carrier_alignment_decode_encode P,
        PaperLeanDriftWitnessTasteGate_single_carrier_alignment_decode_encode N]

private theorem PaperLeanDriftWitnessTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : PaperLeanDriftWitnessUp} :
    PaperLeanDriftWitnessTasteGate_single_carrier_alignment_toEventFlow x =
        PaperLeanDriftWitnessTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      PaperLeanDriftWitnessTasteGate_single_carrier_alignment_fromEventFlow
          (PaperLeanDriftWitnessTasteGate_single_carrier_alignment_toEventFlow x) =
        PaperLeanDriftWitnessTasteGate_single_carrier_alignment_fromEventFlow
          (PaperLeanDriftWitnessTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg PaperLeanDriftWitnessTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (PaperLeanDriftWitnessTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (PaperLeanDriftWitnessTasteGate_single_carrier_alignment_round_trip y)))

instance paperLeanDriftWitnessBHistCarrier : BHistCarrier PaperLeanDriftWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := PaperLeanDriftWitnessTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := PaperLeanDriftWitnessTasteGate_single_carrier_alignment_fromEventFlow

instance paperLeanDriftWitnessChapterTasteGate :
    ChapterTasteGate PaperLeanDriftWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      PaperLeanDriftWitnessTasteGate_single_carrier_alignment_fromEventFlow
          (PaperLeanDriftWitnessTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact PaperLeanDriftWitnessTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (PaperLeanDriftWitnessTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem PaperLeanDriftWitnessTasteGate_single_carrier_alignment :
    ChapterTasteGate PaperLeanDriftWitnessUp := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro x
    change
      PaperLeanDriftWitnessTasteGate_single_carrier_alignment_fromEventFlow
          (PaperLeanDriftWitnessTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact PaperLeanDriftWitnessTasteGate_single_carrier_alignment_round_trip x
  · intro x y hxy heq
    exact hxy (PaperLeanDriftWitnessTasteGate_single_carrier_alignment_toEventFlow_injective heq)

end BEDC.Derived.PaperLeanDriftWitnessUp
