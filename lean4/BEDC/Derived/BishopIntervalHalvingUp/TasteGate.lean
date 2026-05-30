import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopIntervalHalvingUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopIntervalHalvingUp : Type where
  | mk (I M B D W R E H C P N : BHist) : BishopIntervalHalvingUp
  deriving DecidableEq

def bishopIntervalHalvingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopIntervalHalvingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopIntervalHalvingEncodeBHist h

def bishopIntervalHalvingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopIntervalHalvingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopIntervalHalvingDecodeBHist tail)

private theorem BishopIntervalHalvingTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      bishopIntervalHalvingDecodeBHist (bishopIntervalHalvingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopIntervalHalvingFields : BishopIntervalHalvingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopIntervalHalvingUp.mk I M B D W R E H C P N =>
      [I, M, B, D, W, R, E, H, C, P, N]

def bishopIntervalHalvingToEventFlow : BishopIntervalHalvingUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (bishopIntervalHalvingFields x).map bishopIntervalHalvingEncodeBHist

private def BishopIntervalHalvingTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      BishopIntervalHalvingTasteGate_single_carrier_alignment_eventAt index rest

def bishopIntervalHalvingFromEventFlow (ef : EventFlow) : Option BishopIntervalHalvingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopIntervalHalvingUp.mk
      (bishopIntervalHalvingDecodeBHist
        (BishopIntervalHalvingTasteGate_single_carrier_alignment_eventAt 0 ef))
      (bishopIntervalHalvingDecodeBHist
        (BishopIntervalHalvingTasteGate_single_carrier_alignment_eventAt 1 ef))
      (bishopIntervalHalvingDecodeBHist
        (BishopIntervalHalvingTasteGate_single_carrier_alignment_eventAt 2 ef))
      (bishopIntervalHalvingDecodeBHist
        (BishopIntervalHalvingTasteGate_single_carrier_alignment_eventAt 3 ef))
      (bishopIntervalHalvingDecodeBHist
        (BishopIntervalHalvingTasteGate_single_carrier_alignment_eventAt 4 ef))
      (bishopIntervalHalvingDecodeBHist
        (BishopIntervalHalvingTasteGate_single_carrier_alignment_eventAt 5 ef))
      (bishopIntervalHalvingDecodeBHist
        (BishopIntervalHalvingTasteGate_single_carrier_alignment_eventAt 6 ef))
      (bishopIntervalHalvingDecodeBHist
        (BishopIntervalHalvingTasteGate_single_carrier_alignment_eventAt 7 ef))
      (bishopIntervalHalvingDecodeBHist
        (BishopIntervalHalvingTasteGate_single_carrier_alignment_eventAt 8 ef))
      (bishopIntervalHalvingDecodeBHist
        (BishopIntervalHalvingTasteGate_single_carrier_alignment_eventAt 9 ef))
      (bishopIntervalHalvingDecodeBHist
        (BishopIntervalHalvingTasteGate_single_carrier_alignment_eventAt 10 ef)))

private theorem BishopIntervalHalvingTasteGate_single_carrier_alignment_round_trip
    (x : BishopIntervalHalvingUp) :
    bishopIntervalHalvingFromEventFlow (bishopIntervalHalvingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I M B D W R E H C P N =>
      change
        some
            (BishopIntervalHalvingUp.mk
              (bishopIntervalHalvingDecodeBHist (bishopIntervalHalvingEncodeBHist I))
              (bishopIntervalHalvingDecodeBHist (bishopIntervalHalvingEncodeBHist M))
              (bishopIntervalHalvingDecodeBHist (bishopIntervalHalvingEncodeBHist B))
              (bishopIntervalHalvingDecodeBHist (bishopIntervalHalvingEncodeBHist D))
              (bishopIntervalHalvingDecodeBHist (bishopIntervalHalvingEncodeBHist W))
              (bishopIntervalHalvingDecodeBHist (bishopIntervalHalvingEncodeBHist R))
              (bishopIntervalHalvingDecodeBHist (bishopIntervalHalvingEncodeBHist E))
              (bishopIntervalHalvingDecodeBHist (bishopIntervalHalvingEncodeBHist H))
              (bishopIntervalHalvingDecodeBHist (bishopIntervalHalvingEncodeBHist C))
              (bishopIntervalHalvingDecodeBHist (bishopIntervalHalvingEncodeBHist P))
              (bishopIntervalHalvingDecodeBHist (bishopIntervalHalvingEncodeBHist N))) =
          some (BishopIntervalHalvingUp.mk I M B D W R E H C P N)
      rw [BishopIntervalHalvingTasteGate_single_carrier_alignment_decode I,
        BishopIntervalHalvingTasteGate_single_carrier_alignment_decode M,
        BishopIntervalHalvingTasteGate_single_carrier_alignment_decode B,
        BishopIntervalHalvingTasteGate_single_carrier_alignment_decode D,
        BishopIntervalHalvingTasteGate_single_carrier_alignment_decode W,
        BishopIntervalHalvingTasteGate_single_carrier_alignment_decode R,
        BishopIntervalHalvingTasteGate_single_carrier_alignment_decode E,
        BishopIntervalHalvingTasteGate_single_carrier_alignment_decode H,
        BishopIntervalHalvingTasteGate_single_carrier_alignment_decode C,
        BishopIntervalHalvingTasteGate_single_carrier_alignment_decode P,
        BishopIntervalHalvingTasteGate_single_carrier_alignment_decode N]

private theorem BishopIntervalHalvingTasteGate_single_carrier_alignment_injective
    {x y : BishopIntervalHalvingUp} :
    bishopIntervalHalvingToEventFlow x = bishopIntervalHalvingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopIntervalHalvingFromEventFlow (bishopIntervalHalvingToEventFlow x) =
        bishopIntervalHalvingFromEventFlow (bishopIntervalHalvingToEventFlow y) :=
    congrArg bishopIntervalHalvingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopIntervalHalvingTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopIntervalHalvingTasteGate_single_carrier_alignment_round_trip y)))

instance bishopIntervalHalvingBHistCarrier : BHistCarrier BishopIntervalHalvingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopIntervalHalvingToEventFlow
  fromEventFlow := bishopIntervalHalvingFromEventFlow

instance bishopIntervalHalvingChapterTasteGate :
    ChapterTasteGate BishopIntervalHalvingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopIntervalHalvingFromEventFlow (bishopIntervalHalvingToEventFlow x) = some x
    exact BishopIntervalHalvingTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BishopIntervalHalvingTasteGate_single_carrier_alignment_injective heq)

theorem BishopIntervalHalvingTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      bishopIntervalHalvingDecodeBHist (bishopIntervalHalvingEncodeBHist h) = h) ∧
      (∀ x : BishopIntervalHalvingUp,
        bishopIntervalHalvingFromEventFlow (bishopIntervalHalvingToEventFlow x) =
          some x) ∧
        (∀ x y : BishopIntervalHalvingUp,
          bishopIntervalHalvingToEventFlow x = bishopIntervalHalvingToEventFlow y →
            x = y) ∧
          bishopIntervalHalvingEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨BishopIntervalHalvingTasteGate_single_carrier_alignment_decode,
      BishopIntervalHalvingTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => BishopIntervalHalvingTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.BishopIntervalHalvingUp.TasteGate
