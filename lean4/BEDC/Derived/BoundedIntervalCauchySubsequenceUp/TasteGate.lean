import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BoundedIntervalCauchySubsequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BoundedIntervalCauchySubsequenceUp : Type where
  | mk (I S W D T Q E R H C P N : BHist) : BoundedIntervalCauchySubsequenceUp
  deriving DecidableEq

def boundedIntervalCauchySubsequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: boundedIntervalCauchySubsequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: boundedIntervalCauchySubsequenceEncodeBHist h

def boundedIntervalCauchySubsequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (boundedIntervalCauchySubsequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (boundedIntervalCauchySubsequenceDecodeBHist tail)

private theorem boundedIntervalCauchySubsequence_decode_encode :
    ∀ h : BHist,
      boundedIntervalCauchySubsequenceDecodeBHist
          (boundedIntervalCauchySubsequenceEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def boundedIntervalCauchySubsequenceFields :
    BoundedIntervalCauchySubsequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BoundedIntervalCauchySubsequenceUp.mk I S W D T Q E R H C P N =>
      [I, S, W, D, T, Q, E, R, H, C, P, N]

def boundedIntervalCauchySubsequenceToEventFlow :
    BoundedIntervalCauchySubsequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (boundedIntervalCauchySubsequenceFields x).map
        boundedIntervalCauchySubsequenceEncodeBHist

private def boundedIntervalCauchySubsequenceRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => boundedIntervalCauchySubsequenceRawAt index rest

private def boundedIntervalCauchySubsequenceLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ index, _event :: rest => boundedIntervalCauchySubsequenceLengthEq index rest

def boundedIntervalCauchySubsequenceFromEventFlow :
    EventFlow → Option BoundedIntervalCauchySubsequenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match boundedIntervalCauchySubsequenceLengthEq 12 flow with
      | true =>
          some
            (BoundedIntervalCauchySubsequenceUp.mk
              (boundedIntervalCauchySubsequenceDecodeBHist
                (boundedIntervalCauchySubsequenceRawAt 0 flow))
              (boundedIntervalCauchySubsequenceDecodeBHist
                (boundedIntervalCauchySubsequenceRawAt 1 flow))
              (boundedIntervalCauchySubsequenceDecodeBHist
                (boundedIntervalCauchySubsequenceRawAt 2 flow))
              (boundedIntervalCauchySubsequenceDecodeBHist
                (boundedIntervalCauchySubsequenceRawAt 3 flow))
              (boundedIntervalCauchySubsequenceDecodeBHist
                (boundedIntervalCauchySubsequenceRawAt 4 flow))
              (boundedIntervalCauchySubsequenceDecodeBHist
                (boundedIntervalCauchySubsequenceRawAt 5 flow))
              (boundedIntervalCauchySubsequenceDecodeBHist
                (boundedIntervalCauchySubsequenceRawAt 6 flow))
              (boundedIntervalCauchySubsequenceDecodeBHist
                (boundedIntervalCauchySubsequenceRawAt 7 flow))
              (boundedIntervalCauchySubsequenceDecodeBHist
                (boundedIntervalCauchySubsequenceRawAt 8 flow))
              (boundedIntervalCauchySubsequenceDecodeBHist
                (boundedIntervalCauchySubsequenceRawAt 9 flow))
              (boundedIntervalCauchySubsequenceDecodeBHist
                (boundedIntervalCauchySubsequenceRawAt 10 flow))
              (boundedIntervalCauchySubsequenceDecodeBHist
                (boundedIntervalCauchySubsequenceRawAt 11 flow)))
      | false => none

private theorem boundedIntervalCauchySubsequence_round_trip :
    ∀ x : BoundedIntervalCauchySubsequenceUp,
      boundedIntervalCauchySubsequenceFromEventFlow
          (boundedIntervalCauchySubsequenceToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I S W D T Q E R H C P N =>
      change
        some
          (BoundedIntervalCauchySubsequenceUp.mk
            (boundedIntervalCauchySubsequenceDecodeBHist
              (boundedIntervalCauchySubsequenceEncodeBHist I))
            (boundedIntervalCauchySubsequenceDecodeBHist
              (boundedIntervalCauchySubsequenceEncodeBHist S))
            (boundedIntervalCauchySubsequenceDecodeBHist
              (boundedIntervalCauchySubsequenceEncodeBHist W))
            (boundedIntervalCauchySubsequenceDecodeBHist
              (boundedIntervalCauchySubsequenceEncodeBHist D))
            (boundedIntervalCauchySubsequenceDecodeBHist
              (boundedIntervalCauchySubsequenceEncodeBHist T))
            (boundedIntervalCauchySubsequenceDecodeBHist
              (boundedIntervalCauchySubsequenceEncodeBHist Q))
            (boundedIntervalCauchySubsequenceDecodeBHist
              (boundedIntervalCauchySubsequenceEncodeBHist E))
            (boundedIntervalCauchySubsequenceDecodeBHist
              (boundedIntervalCauchySubsequenceEncodeBHist R))
            (boundedIntervalCauchySubsequenceDecodeBHist
              (boundedIntervalCauchySubsequenceEncodeBHist H))
            (boundedIntervalCauchySubsequenceDecodeBHist
              (boundedIntervalCauchySubsequenceEncodeBHist C))
            (boundedIntervalCauchySubsequenceDecodeBHist
              (boundedIntervalCauchySubsequenceEncodeBHist P))
            (boundedIntervalCauchySubsequenceDecodeBHist
              (boundedIntervalCauchySubsequenceEncodeBHist N))) =
          some (BoundedIntervalCauchySubsequenceUp.mk I S W D T Q E R H C P N)
      rw [boundedIntervalCauchySubsequence_decode_encode I,
        boundedIntervalCauchySubsequence_decode_encode S,
        boundedIntervalCauchySubsequence_decode_encode W,
        boundedIntervalCauchySubsequence_decode_encode D,
        boundedIntervalCauchySubsequence_decode_encode T,
        boundedIntervalCauchySubsequence_decode_encode Q,
        boundedIntervalCauchySubsequence_decode_encode E,
        boundedIntervalCauchySubsequence_decode_encode R,
        boundedIntervalCauchySubsequence_decode_encode H,
        boundedIntervalCauchySubsequence_decode_encode C,
        boundedIntervalCauchySubsequence_decode_encode P,
        boundedIntervalCauchySubsequence_decode_encode N]

private theorem boundedIntervalCauchySubsequenceToEventFlow_injective
    {x y : BoundedIntervalCauchySubsequenceUp} :
    boundedIntervalCauchySubsequenceToEventFlow x =
        boundedIntervalCauchySubsequenceToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      boundedIntervalCauchySubsequenceFromEventFlow
          (boundedIntervalCauchySubsequenceToEventFlow x) =
        boundedIntervalCauchySubsequenceFromEventFlow
          (boundedIntervalCauchySubsequenceToEventFlow y) :=
    congrArg boundedIntervalCauchySubsequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (boundedIntervalCauchySubsequence_round_trip x).symm
      (Eq.trans hread (boundedIntervalCauchySubsequence_round_trip y)))

instance boundedIntervalCauchySubsequenceBHistCarrier :
    BHistCarrier BoundedIntervalCauchySubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := boundedIntervalCauchySubsequenceToEventFlow
  fromEventFlow := boundedIntervalCauchySubsequenceFromEventFlow

instance boundedIntervalCauchySubsequenceChapterTasteGate :
    ChapterTasteGate BoundedIntervalCauchySubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      boundedIntervalCauchySubsequenceFromEventFlow
          (boundedIntervalCauchySubsequenceToEventFlow x) =
        some x
    exact boundedIntervalCauchySubsequence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (boundedIntervalCauchySubsequenceToEventFlow_injective heq)

namespace TasteGate

theorem BoundedIntervalCauchySubsequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        boundedIntervalCauchySubsequenceDecodeBHist
            (boundedIntervalCauchySubsequenceEncodeBHist h) =
          h) ∧
      Nonempty (BHistCarrier BoundedIntervalCauchySubsequenceUp) ∧
        Nonempty (ChapterTasteGate BoundedIntervalCauchySubsequenceUp) ∧
          boundedIntervalCauchySubsequenceEncodeBHist BHist.Empty =
            ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨boundedIntervalCauchySubsequence_decode_encode,
      Nonempty.intro boundedIntervalCauchySubsequenceBHistCarrier,
      Nonempty.intro boundedIntervalCauchySubsequenceChapterTasteGate,
      rfl⟩

end TasteGate

end BEDC.Derived.BoundedIntervalCauchySubsequenceUp
