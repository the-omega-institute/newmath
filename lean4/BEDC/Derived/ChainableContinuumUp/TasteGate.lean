import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ChainableContinuumUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ChainableContinuumUp : Type where
  | mk (K C L M T R H P N : BHist) : ChainableContinuumUp
  deriving DecidableEq

private def ChainableContinuumTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 ::
      ChainableContinuumTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 ::
      ChainableContinuumTasteGate_single_carrier_alignment_encodeBHist h

private def ChainableContinuumTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (ChainableContinuumTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (ChainableContinuumTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem ChainableContinuumTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      ChainableContinuumTasteGate_single_carrier_alignment_decodeBHist
        (ChainableContinuumTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def ChainableContinuumTasteGate_single_carrier_alignment_fields :
    ChainableContinuumUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ChainableContinuumUp.mk K C L M T R H P N => [K, C, L, M, T, R, H, P, N]

def chainableContinuumToEventFlow : ChainableContinuumUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (ChainableContinuumTasteGate_single_carrier_alignment_fields x).map
        ChainableContinuumTasteGate_single_carrier_alignment_encodeBHist

private def ChainableContinuumTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      ChainableContinuumTasteGate_single_carrier_alignment_eventAt index rest

def chainableContinuumFromEventFlow :
    EventFlow → Option ChainableContinuumUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (ChainableContinuumUp.mk
        (ChainableContinuumTasteGate_single_carrier_alignment_decodeBHist
          (ChainableContinuumTasteGate_single_carrier_alignment_eventAt 0 ef))
        (ChainableContinuumTasteGate_single_carrier_alignment_decodeBHist
          (ChainableContinuumTasteGate_single_carrier_alignment_eventAt 1 ef))
        (ChainableContinuumTasteGate_single_carrier_alignment_decodeBHist
          (ChainableContinuumTasteGate_single_carrier_alignment_eventAt 2 ef))
        (ChainableContinuumTasteGate_single_carrier_alignment_decodeBHist
          (ChainableContinuumTasteGate_single_carrier_alignment_eventAt 3 ef))
        (ChainableContinuumTasteGate_single_carrier_alignment_decodeBHist
          (ChainableContinuumTasteGate_single_carrier_alignment_eventAt 4 ef))
        (ChainableContinuumTasteGate_single_carrier_alignment_decodeBHist
          (ChainableContinuumTasteGate_single_carrier_alignment_eventAt 5 ef))
        (ChainableContinuumTasteGate_single_carrier_alignment_decodeBHist
          (ChainableContinuumTasteGate_single_carrier_alignment_eventAt 6 ef))
        (ChainableContinuumTasteGate_single_carrier_alignment_decodeBHist
          (ChainableContinuumTasteGate_single_carrier_alignment_eventAt 7 ef))
        (ChainableContinuumTasteGate_single_carrier_alignment_decodeBHist
          (ChainableContinuumTasteGate_single_carrier_alignment_eventAt 8 ef)))

private theorem ChainableContinuumTasteGate_single_carrier_alignment_round_trip
    (x : ChainableContinuumUp) :
    chainableContinuumFromEventFlow (chainableContinuumToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk K C L M T R H P N =>
      change
        some
          (ChainableContinuumUp.mk
            (ChainableContinuumTasteGate_single_carrier_alignment_decodeBHist
              (ChainableContinuumTasteGate_single_carrier_alignment_encodeBHist K))
            (ChainableContinuumTasteGate_single_carrier_alignment_decodeBHist
              (ChainableContinuumTasteGate_single_carrier_alignment_encodeBHist C))
            (ChainableContinuumTasteGate_single_carrier_alignment_decodeBHist
              (ChainableContinuumTasteGate_single_carrier_alignment_encodeBHist L))
            (ChainableContinuumTasteGate_single_carrier_alignment_decodeBHist
              (ChainableContinuumTasteGate_single_carrier_alignment_encodeBHist M))
            (ChainableContinuumTasteGate_single_carrier_alignment_decodeBHist
              (ChainableContinuumTasteGate_single_carrier_alignment_encodeBHist T))
            (ChainableContinuumTasteGate_single_carrier_alignment_decodeBHist
              (ChainableContinuumTasteGate_single_carrier_alignment_encodeBHist R))
            (ChainableContinuumTasteGate_single_carrier_alignment_decodeBHist
              (ChainableContinuumTasteGate_single_carrier_alignment_encodeBHist H))
            (ChainableContinuumTasteGate_single_carrier_alignment_decodeBHist
              (ChainableContinuumTasteGate_single_carrier_alignment_encodeBHist P))
            (ChainableContinuumTasteGate_single_carrier_alignment_decodeBHist
              (ChainableContinuumTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (ChainableContinuumUp.mk K C L M T R H P N)
      rw [ChainableContinuumTasteGate_single_carrier_alignment_decode_encode K,
        ChainableContinuumTasteGate_single_carrier_alignment_decode_encode C,
        ChainableContinuumTasteGate_single_carrier_alignment_decode_encode L,
        ChainableContinuumTasteGate_single_carrier_alignment_decode_encode M,
        ChainableContinuumTasteGate_single_carrier_alignment_decode_encode T,
        ChainableContinuumTasteGate_single_carrier_alignment_decode_encode R,
        ChainableContinuumTasteGate_single_carrier_alignment_decode_encode H,
        ChainableContinuumTasteGate_single_carrier_alignment_decode_encode P,
        ChainableContinuumTasteGate_single_carrier_alignment_decode_encode N]

private theorem ChainableContinuumTasteGate_single_carrier_alignment_injective
    {x y : ChainableContinuumUp} :
    chainableContinuumToEventFlow x = chainableContinuumToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      chainableContinuumFromEventFlow (chainableContinuumToEventFlow x) =
        chainableContinuumFromEventFlow (chainableContinuumToEventFlow y) :=
    congrArg chainableContinuumFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ChainableContinuumTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ChainableContinuumTasteGate_single_carrier_alignment_round_trip y)))

instance ChainableContinuumTasteGate_single_carrier_alignment_bhistCarrier :
    BHistCarrier ChainableContinuumUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := chainableContinuumToEventFlow
  fromEventFlow := chainableContinuumFromEventFlow

instance ChainableContinuumTasteGate_single_carrier_alignment_chapterTasteGate :
    ChapterTasteGate ChainableContinuumUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change chainableContinuumFromEventFlow (chainableContinuumToEventFlow x) = some x
    exact ChainableContinuumTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ChainableContinuumTasteGate_single_carrier_alignment_injective heq)

theorem ChainableContinuumTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ChainableContinuumUp) ∧
      Nonempty (BHistCarrier ChainableContinuumUp) ∧
        (∀ x : ChainableContinuumUp,
          chainableContinuumFromEventFlow (chainableContinuumToEventFlow x) = some x) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨ChainableContinuumTasteGate_single_carrier_alignment_chapterTasteGate⟩,
      ⟨ChainableContinuumTasteGate_single_carrier_alignment_bhistCarrier⟩,
      ChainableContinuumTasteGate_single_carrier_alignment_round_trip⟩

end BEDC.Derived.ChainableContinuumUp
