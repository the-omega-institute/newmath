import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
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

private theorem BoundedIntervalCauchySubsequenceTasteGate_single_carrier_alignment_decode :
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
    BoundedIntervalCauchySubsequenceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (boundedIntervalCauchySubsequenceFields x).map
      boundedIntervalCauchySubsequenceEncodeBHist

private def boundedIntervalCauchySubsequenceEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      boundedIntervalCauchySubsequenceEventAtDefault index rest

def boundedIntervalCauchySubsequenceFromEventFlow
    (ef : EventFlow) : Option BoundedIntervalCauchySubsequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BoundedIntervalCauchySubsequenceUp.mk
      (boundedIntervalCauchySubsequenceDecodeBHist
        (boundedIntervalCauchySubsequenceEventAtDefault 0 ef))
      (boundedIntervalCauchySubsequenceDecodeBHist
        (boundedIntervalCauchySubsequenceEventAtDefault 1 ef))
      (boundedIntervalCauchySubsequenceDecodeBHist
        (boundedIntervalCauchySubsequenceEventAtDefault 2 ef))
      (boundedIntervalCauchySubsequenceDecodeBHist
        (boundedIntervalCauchySubsequenceEventAtDefault 3 ef))
      (boundedIntervalCauchySubsequenceDecodeBHist
        (boundedIntervalCauchySubsequenceEventAtDefault 4 ef))
      (boundedIntervalCauchySubsequenceDecodeBHist
        (boundedIntervalCauchySubsequenceEventAtDefault 5 ef))
      (boundedIntervalCauchySubsequenceDecodeBHist
        (boundedIntervalCauchySubsequenceEventAtDefault 6 ef))
      (boundedIntervalCauchySubsequenceDecodeBHist
        (boundedIntervalCauchySubsequenceEventAtDefault 7 ef))
      (boundedIntervalCauchySubsequenceDecodeBHist
        (boundedIntervalCauchySubsequenceEventAtDefault 8 ef))
      (boundedIntervalCauchySubsequenceDecodeBHist
        (boundedIntervalCauchySubsequenceEventAtDefault 9 ef))
      (boundedIntervalCauchySubsequenceDecodeBHist
        (boundedIntervalCauchySubsequenceEventAtDefault 10 ef))
      (boundedIntervalCauchySubsequenceDecodeBHist
        (boundedIntervalCauchySubsequenceEventAtDefault 11 ef)))

private theorem BoundedIntervalCauchySubsequenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BoundedIntervalCauchySubsequenceUp,
      boundedIntervalCauchySubsequenceFromEventFlow
          (boundedIntervalCauchySubsequenceToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
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
      rw [BoundedIntervalCauchySubsequenceTasteGate_single_carrier_alignment_decode I,
        BoundedIntervalCauchySubsequenceTasteGate_single_carrier_alignment_decode S,
        BoundedIntervalCauchySubsequenceTasteGate_single_carrier_alignment_decode W,
        BoundedIntervalCauchySubsequenceTasteGate_single_carrier_alignment_decode D,
        BoundedIntervalCauchySubsequenceTasteGate_single_carrier_alignment_decode T,
        BoundedIntervalCauchySubsequenceTasteGate_single_carrier_alignment_decode Q,
        BoundedIntervalCauchySubsequenceTasteGate_single_carrier_alignment_decode E,
        BoundedIntervalCauchySubsequenceTasteGate_single_carrier_alignment_decode R,
        BoundedIntervalCauchySubsequenceTasteGate_single_carrier_alignment_decode H,
        BoundedIntervalCauchySubsequenceTasteGate_single_carrier_alignment_decode C,
        BoundedIntervalCauchySubsequenceTasteGate_single_carrier_alignment_decode P,
        BoundedIntervalCauchySubsequenceTasteGate_single_carrier_alignment_decode N]

private theorem BoundedIntervalCauchySubsequenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BoundedIntervalCauchySubsequenceUp} :
    boundedIntervalCauchySubsequenceToEventFlow x =
      boundedIntervalCauchySubsequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      boundedIntervalCauchySubsequenceFromEventFlow
          (boundedIntervalCauchySubsequenceToEventFlow x) =
        boundedIntervalCauchySubsequenceFromEventFlow
          (boundedIntervalCauchySubsequenceToEventFlow y) :=
    congrArg boundedIntervalCauchySubsequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BoundedIntervalCauchySubsequenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BoundedIntervalCauchySubsequenceTasteGate_single_carrier_alignment_round_trip y)))

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
    exact BoundedIntervalCauchySubsequenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BoundedIntervalCauchySubsequenceTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

theorem BoundedIntervalCauchySubsequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      boundedIntervalCauchySubsequenceDecodeBHist
        (boundedIntervalCauchySubsequenceEncodeBHist h) = h) ∧
      (∀ x : BoundedIntervalCauchySubsequenceUp,
        boundedIntervalCauchySubsequenceFromEventFlow
          (boundedIntervalCauchySubsequenceToEventFlow x) = some x) ∧
      (∀ x y : BoundedIntervalCauchySubsequenceUp,
        boundedIntervalCauchySubsequenceToEventFlow x =
          boundedIntervalCauchySubsequenceToEventFlow y → x = y) ∧
      boundedIntervalCauchySubsequenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨BoundedIntervalCauchySubsequenceTasteGate_single_carrier_alignment_decode,
      BoundedIntervalCauchySubsequenceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        BoundedIntervalCauchySubsequenceTasteGate_single_carrier_alignment_toEventFlow_injective
          heq),
      rfl⟩

end BEDC.Derived.BoundedIntervalCauchySubsequenceUp
