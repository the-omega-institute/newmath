import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LimsupUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LimsupUp : Type where
  | mk (S U D T H C P N : BHist) : LimsupUp
  deriving DecidableEq

def limsupEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: limsupEncodeBHist h
  | BHist.e1 h => BMark.b1 :: limsupEncodeBHist h

def limsupDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (limsupDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (limsupDecodeBHist tail)

private theorem LimsupTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, limsupDecodeBHist (limsupEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def limsupFields : LimsupUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LimsupUp.mk S U D T H C P N => [S, U, D, T, H, C, P, N]

def limsupToEventFlow : LimsupUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map limsupEncodeBHist (limsupFields x)

private def limsupRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => limsupRawAt index rest

def limsupFromEventFlow (flow : EventFlow) : Option LimsupUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LimsupUp.mk
      (limsupDecodeBHist (limsupRawAt 0 flow))
      (limsupDecodeBHist (limsupRawAt 1 flow))
      (limsupDecodeBHist (limsupRawAt 2 flow))
      (limsupDecodeBHist (limsupRawAt 3 flow))
      (limsupDecodeBHist (limsupRawAt 4 flow))
      (limsupDecodeBHist (limsupRawAt 5 flow))
      (limsupDecodeBHist (limsupRawAt 6 flow))
      (limsupDecodeBHist (limsupRawAt 7 flow)))

private theorem LimsupTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LimsupUp, limsupFromEventFlow (limsupToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S U D T H C P N =>
      change
        some
          (LimsupUp.mk
            (limsupDecodeBHist (limsupEncodeBHist S))
            (limsupDecodeBHist (limsupEncodeBHist U))
            (limsupDecodeBHist (limsupEncodeBHist D))
            (limsupDecodeBHist (limsupEncodeBHist T))
            (limsupDecodeBHist (limsupEncodeBHist H))
            (limsupDecodeBHist (limsupEncodeBHist C))
            (limsupDecodeBHist (limsupEncodeBHist P))
            (limsupDecodeBHist (limsupEncodeBHist N))) =
          some (LimsupUp.mk S U D T H C P N)
      rw [LimsupTasteGate_single_carrier_alignment_decode S,
        LimsupTasteGate_single_carrier_alignment_decode U,
        LimsupTasteGate_single_carrier_alignment_decode D,
        LimsupTasteGate_single_carrier_alignment_decode T,
        LimsupTasteGate_single_carrier_alignment_decode H,
        LimsupTasteGate_single_carrier_alignment_decode C,
        LimsupTasteGate_single_carrier_alignment_decode P,
        LimsupTasteGate_single_carrier_alignment_decode N]

private theorem limsupToEventFlow_injective {x y : LimsupUp} :
    limsupToEventFlow x = limsupToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      limsupFromEventFlow (limsupToEventFlow x) =
        limsupFromEventFlow (limsupToEventFlow y) :=
    congrArg limsupFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LimsupTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (LimsupTasteGate_single_carrier_alignment_round_trip y)))

instance limsupBHistCarrier : BHistCarrier LimsupUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := limsupToEventFlow
  fromEventFlow := limsupFromEventFlow

instance limsupChapterTasteGate : ChapterTasteGate LimsupUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change limsupFromEventFlow (limsupToEventFlow x) = some x
    exact LimsupTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (limsupToEventFlow_injective heq)

def taste_gate : ChapterTasteGate LimsupUp :=
  -- BEDC touchpoint anchor: BHist BMark
  limsupChapterTasteGate

theorem LimsupTasteGate_single_carrier_alignment :
    (∀ h : BHist, limsupDecodeBHist (limsupEncodeBHist h) = h) ∧
      (∀ x : LimsupUp, limsupFromEventFlow (limsupToEventFlow x) = some x) ∧
        (∀ x y : LimsupUp, limsupToEventFlow x = limsupToEventFlow y → x = y) ∧
          limsupEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨LimsupTasteGate_single_carrier_alignment_decode,
      LimsupTasteGate_single_carrier_alignment_round_trip,
      by
        intro x y heq
        exact limsupToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.LimsupUp
