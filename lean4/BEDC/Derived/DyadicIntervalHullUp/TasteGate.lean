import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicIntervalHullUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicIntervalHullUp : Type where
  | mk (L U O A B S R E T C P N : BHist) : DyadicIntervalHullUp
  deriving DecidableEq

def DyadicIntervalHullTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 :: DyadicIntervalHullTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h =>
      BMark.b1 :: DyadicIntervalHullTasteGate_single_carrier_alignment_encodeBHist h

def DyadicIntervalHullTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (DyadicIntervalHullTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (DyadicIntervalHullTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem DyadicIntervalHullTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      DyadicIntervalHullTasteGate_single_carrier_alignment_decodeBHist
        (DyadicIntervalHullTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicIntervalHullFields : DyadicIntervalHullUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicIntervalHullUp.mk L U O A B S R E T C P N =>
      [L, U, O, A, B, S, R, E, T, C, P, N]

def dyadicIntervalHullToEventFlow : DyadicIntervalHullUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (dyadicIntervalHullFields x).map
        DyadicIntervalHullTasteGate_single_carrier_alignment_encodeBHist

private def dyadicIntervalHullEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dyadicIntervalHullEventAt index rest

def dyadicIntervalHullFromEventFlow (ef : EventFlow) : Option DyadicIntervalHullUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DyadicIntervalHullUp.mk
      (DyadicIntervalHullTasteGate_single_carrier_alignment_decodeBHist
        (dyadicIntervalHullEventAt 0 ef))
      (DyadicIntervalHullTasteGate_single_carrier_alignment_decodeBHist
        (dyadicIntervalHullEventAt 1 ef))
      (DyadicIntervalHullTasteGate_single_carrier_alignment_decodeBHist
        (dyadicIntervalHullEventAt 2 ef))
      (DyadicIntervalHullTasteGate_single_carrier_alignment_decodeBHist
        (dyadicIntervalHullEventAt 3 ef))
      (DyadicIntervalHullTasteGate_single_carrier_alignment_decodeBHist
        (dyadicIntervalHullEventAt 4 ef))
      (DyadicIntervalHullTasteGate_single_carrier_alignment_decodeBHist
        (dyadicIntervalHullEventAt 5 ef))
      (DyadicIntervalHullTasteGate_single_carrier_alignment_decodeBHist
        (dyadicIntervalHullEventAt 6 ef))
      (DyadicIntervalHullTasteGate_single_carrier_alignment_decodeBHist
        (dyadicIntervalHullEventAt 7 ef))
      (DyadicIntervalHullTasteGate_single_carrier_alignment_decodeBHist
        (dyadicIntervalHullEventAt 8 ef))
      (DyadicIntervalHullTasteGate_single_carrier_alignment_decodeBHist
        (dyadicIntervalHullEventAt 9 ef))
      (DyadicIntervalHullTasteGate_single_carrier_alignment_decodeBHist
        (dyadicIntervalHullEventAt 10 ef))
      (DyadicIntervalHullTasteGate_single_carrier_alignment_decodeBHist
        (dyadicIntervalHullEventAt 11 ef)))

private theorem DyadicIntervalHullTasteGate_single_carrier_alignment_round_trip
    (x : DyadicIntervalHullUp) :
    dyadicIntervalHullFromEventFlow (dyadicIntervalHullToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk L U O A B S R E T C P N =>
      change
        some
          (DyadicIntervalHullUp.mk
            (DyadicIntervalHullTasteGate_single_carrier_alignment_decodeBHist
              (DyadicIntervalHullTasteGate_single_carrier_alignment_encodeBHist L))
            (DyadicIntervalHullTasteGate_single_carrier_alignment_decodeBHist
              (DyadicIntervalHullTasteGate_single_carrier_alignment_encodeBHist U))
            (DyadicIntervalHullTasteGate_single_carrier_alignment_decodeBHist
              (DyadicIntervalHullTasteGate_single_carrier_alignment_encodeBHist O))
            (DyadicIntervalHullTasteGate_single_carrier_alignment_decodeBHist
              (DyadicIntervalHullTasteGate_single_carrier_alignment_encodeBHist A))
            (DyadicIntervalHullTasteGate_single_carrier_alignment_decodeBHist
              (DyadicIntervalHullTasteGate_single_carrier_alignment_encodeBHist B))
            (DyadicIntervalHullTasteGate_single_carrier_alignment_decodeBHist
              (DyadicIntervalHullTasteGate_single_carrier_alignment_encodeBHist S))
            (DyadicIntervalHullTasteGate_single_carrier_alignment_decodeBHist
              (DyadicIntervalHullTasteGate_single_carrier_alignment_encodeBHist R))
            (DyadicIntervalHullTasteGate_single_carrier_alignment_decodeBHist
              (DyadicIntervalHullTasteGate_single_carrier_alignment_encodeBHist E))
            (DyadicIntervalHullTasteGate_single_carrier_alignment_decodeBHist
              (DyadicIntervalHullTasteGate_single_carrier_alignment_encodeBHist T))
            (DyadicIntervalHullTasteGate_single_carrier_alignment_decodeBHist
              (DyadicIntervalHullTasteGate_single_carrier_alignment_encodeBHist C))
            (DyadicIntervalHullTasteGate_single_carrier_alignment_decodeBHist
              (DyadicIntervalHullTasteGate_single_carrier_alignment_encodeBHist P))
            (DyadicIntervalHullTasteGate_single_carrier_alignment_decodeBHist
              (DyadicIntervalHullTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (DyadicIntervalHullUp.mk L U O A B S R E T C P N)
      rw [DyadicIntervalHullTasteGate_single_carrier_alignment_decode_encode L,
        DyadicIntervalHullTasteGate_single_carrier_alignment_decode_encode U,
        DyadicIntervalHullTasteGate_single_carrier_alignment_decode_encode O,
        DyadicIntervalHullTasteGate_single_carrier_alignment_decode_encode A,
        DyadicIntervalHullTasteGate_single_carrier_alignment_decode_encode B,
        DyadicIntervalHullTasteGate_single_carrier_alignment_decode_encode S,
        DyadicIntervalHullTasteGate_single_carrier_alignment_decode_encode R,
        DyadicIntervalHullTasteGate_single_carrier_alignment_decode_encode E,
        DyadicIntervalHullTasteGate_single_carrier_alignment_decode_encode T,
        DyadicIntervalHullTasteGate_single_carrier_alignment_decode_encode C,
        DyadicIntervalHullTasteGate_single_carrier_alignment_decode_encode P,
        DyadicIntervalHullTasteGate_single_carrier_alignment_decode_encode N]

private theorem DyadicIntervalHullTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DyadicIntervalHullUp} :
    dyadicIntervalHullToEventFlow x = dyadicIntervalHullToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicIntervalHullFromEventFlow (dyadicIntervalHullToEventFlow x) =
        dyadicIntervalHullFromEventFlow (dyadicIntervalHullToEventFlow y) :=
    congrArg dyadicIntervalHullFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DyadicIntervalHullTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DyadicIntervalHullTasteGate_single_carrier_alignment_round_trip y)))

instance dyadicIntervalHullBHistCarrier : BHistCarrier DyadicIntervalHullUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicIntervalHullToEventFlow
  fromEventFlow := dyadicIntervalHullFromEventFlow

instance dyadicIntervalHullChapterTasteGate :
    ChapterTasteGate DyadicIntervalHullUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicIntervalHullFromEventFlow (dyadicIntervalHullToEventFlow x) = some x
    exact DyadicIntervalHullTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DyadicIntervalHullTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def DyadicIntervalHullTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate DyadicIntervalHullUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicIntervalHullChapterTasteGate

theorem DyadicIntervalHullTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      DyadicIntervalHullTasteGate_single_carrier_alignment_decodeBHist
        (DyadicIntervalHullTasteGate_single_carrier_alignment_encodeBHist h) = h) ∧
      (∀ x : DyadicIntervalHullUp,
        dyadicIntervalHullFromEventFlow (dyadicIntervalHullToEventFlow x) = some x) ∧
        (∀ x y : DyadicIntervalHullUp,
          dyadicIntervalHullToEventFlow x = dyadicIntervalHullToEventFlow y → x = y) ∧
          DyadicIntervalHullTasteGate_single_carrier_alignment_encodeBHist BHist.Empty =
            ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨DyadicIntervalHullTasteGate_single_carrier_alignment_decode_encode,
      DyadicIntervalHullTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        DyadicIntervalHullTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.DyadicIntervalHullUp
