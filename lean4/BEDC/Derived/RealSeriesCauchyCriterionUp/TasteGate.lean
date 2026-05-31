import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealSeriesCauchyCriterionUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealSeriesCauchyCriterionUp : Type where
  | mk (T S D R M E H C P N : BHist) : RealSeriesCauchyCriterionUp
  deriving DecidableEq

def realSeriesCauchyCriterionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realSeriesCauchyCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realSeriesCauchyCriterionEncodeBHist h

def realSeriesCauchyCriterionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realSeriesCauchyCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realSeriesCauchyCriterionDecodeBHist tail)

private theorem RealSeriesCauchyCriterionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      realSeriesCauchyCriterionDecodeBHist (realSeriesCauchyCriterionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realSeriesCauchyCriterionFields :
    RealSeriesCauchyCriterionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealSeriesCauchyCriterionUp.mk T S D R M E H C P N => [T, S, D, R, M, E, H, C, P, N]

def realSeriesCauchyCriterionToEventFlow :
    RealSeriesCauchyCriterionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realSeriesCauchyCriterionFields x).map realSeriesCauchyCriterionEncodeBHist

private def RealSeriesCauchyCriterionTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      RealSeriesCauchyCriterionTasteGate_single_carrier_alignment_eventAt index rest

def realSeriesCauchyCriterionDecodeFields (ef : EventFlow) : RealSeriesCauchyCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  RealSeriesCauchyCriterionUp.mk
    (realSeriesCauchyCriterionDecodeBHist
      (RealSeriesCauchyCriterionTasteGate_single_carrier_alignment_eventAt 0 ef))
    (realSeriesCauchyCriterionDecodeBHist
      (RealSeriesCauchyCriterionTasteGate_single_carrier_alignment_eventAt 1 ef))
    (realSeriesCauchyCriterionDecodeBHist
      (RealSeriesCauchyCriterionTasteGate_single_carrier_alignment_eventAt 2 ef))
    (realSeriesCauchyCriterionDecodeBHist
      (RealSeriesCauchyCriterionTasteGate_single_carrier_alignment_eventAt 3 ef))
    (realSeriesCauchyCriterionDecodeBHist
      (RealSeriesCauchyCriterionTasteGate_single_carrier_alignment_eventAt 4 ef))
    (realSeriesCauchyCriterionDecodeBHist
      (RealSeriesCauchyCriterionTasteGate_single_carrier_alignment_eventAt 5 ef))
    (realSeriesCauchyCriterionDecodeBHist
      (RealSeriesCauchyCriterionTasteGate_single_carrier_alignment_eventAt 6 ef))
    (realSeriesCauchyCriterionDecodeBHist
      (RealSeriesCauchyCriterionTasteGate_single_carrier_alignment_eventAt 7 ef))
    (realSeriesCauchyCriterionDecodeBHist
      (RealSeriesCauchyCriterionTasteGate_single_carrier_alignment_eventAt 8 ef))
    (realSeriesCauchyCriterionDecodeBHist
      (RealSeriesCauchyCriterionTasteGate_single_carrier_alignment_eventAt 9 ef))

def realSeriesCauchyCriterionFromEventFlow
    (ef : EventFlow) : Option RealSeriesCauchyCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some (realSeriesCauchyCriterionDecodeFields ef)

private theorem RealSeriesCauchyCriterionTasteGate_single_carrier_alignment_round_trip
    (x : RealSeriesCauchyCriterionUp) :
    realSeriesCauchyCriterionFromEventFlow
        (realSeriesCauchyCriterionToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk T S D R M E H C P N =>
      change
        some
          (RealSeriesCauchyCriterionUp.mk
            (realSeriesCauchyCriterionDecodeBHist
              (realSeriesCauchyCriterionEncodeBHist T))
            (realSeriesCauchyCriterionDecodeBHist
              (realSeriesCauchyCriterionEncodeBHist S))
            (realSeriesCauchyCriterionDecodeBHist
              (realSeriesCauchyCriterionEncodeBHist D))
            (realSeriesCauchyCriterionDecodeBHist
              (realSeriesCauchyCriterionEncodeBHist R))
            (realSeriesCauchyCriterionDecodeBHist
              (realSeriesCauchyCriterionEncodeBHist M))
            (realSeriesCauchyCriterionDecodeBHist
              (realSeriesCauchyCriterionEncodeBHist E))
            (realSeriesCauchyCriterionDecodeBHist
              (realSeriesCauchyCriterionEncodeBHist H))
            (realSeriesCauchyCriterionDecodeBHist
              (realSeriesCauchyCriterionEncodeBHist C))
            (realSeriesCauchyCriterionDecodeBHist
              (realSeriesCauchyCriterionEncodeBHist P))
            (realSeriesCauchyCriterionDecodeBHist
              (realSeriesCauchyCriterionEncodeBHist N))) =
          some (RealSeriesCauchyCriterionUp.mk T S D R M E H C P N)
      rw [RealSeriesCauchyCriterionTasteGate_single_carrier_alignment_decode_encode T,
        RealSeriesCauchyCriterionTasteGate_single_carrier_alignment_decode_encode S,
        RealSeriesCauchyCriterionTasteGate_single_carrier_alignment_decode_encode D,
        RealSeriesCauchyCriterionTasteGate_single_carrier_alignment_decode_encode R,
        RealSeriesCauchyCriterionTasteGate_single_carrier_alignment_decode_encode M,
        RealSeriesCauchyCriterionTasteGate_single_carrier_alignment_decode_encode E,
        RealSeriesCauchyCriterionTasteGate_single_carrier_alignment_decode_encode H,
        RealSeriesCauchyCriterionTasteGate_single_carrier_alignment_decode_encode C,
        RealSeriesCauchyCriterionTasteGate_single_carrier_alignment_decode_encode P,
        RealSeriesCauchyCriterionTasteGate_single_carrier_alignment_decode_encode N]

private theorem RealSeriesCauchyCriterionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealSeriesCauchyCriterionUp} :
    realSeriesCauchyCriterionToEventFlow x =
        realSeriesCauchyCriterionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realSeriesCauchyCriterionFromEventFlow (realSeriesCauchyCriterionToEventFlow x) =
        realSeriesCauchyCriterionFromEventFlow (realSeriesCauchyCriterionToEventFlow y) :=
    congrArg realSeriesCauchyCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RealSeriesCauchyCriterionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RealSeriesCauchyCriterionTasteGate_single_carrier_alignment_round_trip y)))

instance realSeriesCauchyCriterionBHistCarrier :
    BHistCarrier RealSeriesCauchyCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realSeriesCauchyCriterionToEventFlow
  fromEventFlow := realSeriesCauchyCriterionFromEventFlow

instance realSeriesCauchyCriterionChapterTasteGate :
    ChapterTasteGate RealSeriesCauchyCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realSeriesCauchyCriterionFromEventFlow
          (realSeriesCauchyCriterionToEventFlow x) =
        some x
    exact RealSeriesCauchyCriterionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RealSeriesCauchyCriterionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate RealSeriesCauchyCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realSeriesCauchyCriterionChapterTasteGate

theorem RealSeriesCauchyCriterionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        realSeriesCauchyCriterionDecodeBHist
          (realSeriesCauchyCriterionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RealSeriesCauchyCriterionUp) ∧
        Nonempty (ChapterTasteGate RealSeriesCauchyCriterionUp) ∧
          realSeriesCauchyCriterionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RealSeriesCauchyCriterionTasteGate_single_carrier_alignment_decode_encode,
      ⟨realSeriesCauchyCriterionBHistCarrier⟩,
      ⟨realSeriesCauchyCriterionChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.RealSeriesCauchyCriterionUp.TasteGate
