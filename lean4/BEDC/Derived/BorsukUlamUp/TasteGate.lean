import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BorsukUlamUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BorsukUlamUp : Type where
  | mk (S A F D C R H K P N : BHist) : BorsukUlamUp
  deriving DecidableEq

def BorsukUlamTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: BorsukUlamTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: BorsukUlamTasteGate_single_carrier_alignment_encodeBHist h

def BorsukUlamTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (BorsukUlamTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (BorsukUlamTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem BorsukUlamTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      BorsukUlamTasteGate_single_carrier_alignment_decodeBHist
          (BorsukUlamTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def BorsukUlamTasteGate_single_carrier_alignment_fields :
    BorsukUlamUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BorsukUlamUp.mk S A F D C R H K P N => [S, A, F, D, C, R, H, K, P, N]

def BorsukUlamTasteGate_single_carrier_alignment_toEventFlow :
    BorsukUlamUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (BorsukUlamTasteGate_single_carrier_alignment_fields x).map
        BorsukUlamTasteGate_single_carrier_alignment_encodeBHist

private def BorsukUlamTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      BorsukUlamTasteGate_single_carrier_alignment_eventAt index rest

def BorsukUlamTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option BorsukUlamUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (BorsukUlamUp.mk
        (BorsukUlamTasteGate_single_carrier_alignment_decodeBHist
          (BorsukUlamTasteGate_single_carrier_alignment_eventAt 0 ef))
        (BorsukUlamTasteGate_single_carrier_alignment_decodeBHist
          (BorsukUlamTasteGate_single_carrier_alignment_eventAt 1 ef))
        (BorsukUlamTasteGate_single_carrier_alignment_decodeBHist
          (BorsukUlamTasteGate_single_carrier_alignment_eventAt 2 ef))
        (BorsukUlamTasteGate_single_carrier_alignment_decodeBHist
          (BorsukUlamTasteGate_single_carrier_alignment_eventAt 3 ef))
        (BorsukUlamTasteGate_single_carrier_alignment_decodeBHist
          (BorsukUlamTasteGate_single_carrier_alignment_eventAt 4 ef))
        (BorsukUlamTasteGate_single_carrier_alignment_decodeBHist
          (BorsukUlamTasteGate_single_carrier_alignment_eventAt 5 ef))
        (BorsukUlamTasteGate_single_carrier_alignment_decodeBHist
          (BorsukUlamTasteGate_single_carrier_alignment_eventAt 6 ef))
        (BorsukUlamTasteGate_single_carrier_alignment_decodeBHist
          (BorsukUlamTasteGate_single_carrier_alignment_eventAt 7 ef))
        (BorsukUlamTasteGate_single_carrier_alignment_decodeBHist
          (BorsukUlamTasteGate_single_carrier_alignment_eventAt 8 ef))
        (BorsukUlamTasteGate_single_carrier_alignment_decodeBHist
          (BorsukUlamTasteGate_single_carrier_alignment_eventAt 9 ef)))

private theorem BorsukUlamTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BorsukUlamUp,
      BorsukUlamTasteGate_single_carrier_alignment_fromEventFlow
          (BorsukUlamTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S A F D C R H K P N =>
      change
        some
          (BorsukUlamUp.mk
            (BorsukUlamTasteGate_single_carrier_alignment_decodeBHist
              (BorsukUlamTasteGate_single_carrier_alignment_encodeBHist S))
            (BorsukUlamTasteGate_single_carrier_alignment_decodeBHist
              (BorsukUlamTasteGate_single_carrier_alignment_encodeBHist A))
            (BorsukUlamTasteGate_single_carrier_alignment_decodeBHist
              (BorsukUlamTasteGate_single_carrier_alignment_encodeBHist F))
            (BorsukUlamTasteGate_single_carrier_alignment_decodeBHist
              (BorsukUlamTasteGate_single_carrier_alignment_encodeBHist D))
            (BorsukUlamTasteGate_single_carrier_alignment_decodeBHist
              (BorsukUlamTasteGate_single_carrier_alignment_encodeBHist C))
            (BorsukUlamTasteGate_single_carrier_alignment_decodeBHist
              (BorsukUlamTasteGate_single_carrier_alignment_encodeBHist R))
            (BorsukUlamTasteGate_single_carrier_alignment_decodeBHist
              (BorsukUlamTasteGate_single_carrier_alignment_encodeBHist H))
            (BorsukUlamTasteGate_single_carrier_alignment_decodeBHist
              (BorsukUlamTasteGate_single_carrier_alignment_encodeBHist K))
            (BorsukUlamTasteGate_single_carrier_alignment_decodeBHist
              (BorsukUlamTasteGate_single_carrier_alignment_encodeBHist P))
            (BorsukUlamTasteGate_single_carrier_alignment_decodeBHist
              (BorsukUlamTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (BorsukUlamUp.mk S A F D C R H K P N)
      rw [BorsukUlamTasteGate_single_carrier_alignment_decode_encode S,
        BorsukUlamTasteGate_single_carrier_alignment_decode_encode A,
        BorsukUlamTasteGate_single_carrier_alignment_decode_encode F,
        BorsukUlamTasteGate_single_carrier_alignment_decode_encode D,
        BorsukUlamTasteGate_single_carrier_alignment_decode_encode C,
        BorsukUlamTasteGate_single_carrier_alignment_decode_encode R,
        BorsukUlamTasteGate_single_carrier_alignment_decode_encode H,
        BorsukUlamTasteGate_single_carrier_alignment_decode_encode K,
        BorsukUlamTasteGate_single_carrier_alignment_decode_encode P,
        BorsukUlamTasteGate_single_carrier_alignment_decode_encode N]

private theorem BorsukUlamTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BorsukUlamUp} :
    BorsukUlamTasteGate_single_carrier_alignment_toEventFlow x =
        BorsukUlamTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      BorsukUlamTasteGate_single_carrier_alignment_fromEventFlow
          (BorsukUlamTasteGate_single_carrier_alignment_toEventFlow x) =
        BorsukUlamTasteGate_single_carrier_alignment_fromEventFlow
          (BorsukUlamTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg BorsukUlamTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BorsukUlamTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BorsukUlamTasteGate_single_carrier_alignment_round_trip y)))

instance BorsukUlamTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier BorsukUlamUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := BorsukUlamTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := BorsukUlamTasteGate_single_carrier_alignment_fromEventFlow

instance BorsukUlamTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate BorsukUlamUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      BorsukUlamTasteGate_single_carrier_alignment_fromEventFlow
          (BorsukUlamTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact BorsukUlamTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BorsukUlamTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem BorsukUlamTasteGate_single_carrier_alignment :
    ChapterTasteGate BorsukUlamUp := by
  -- BEDC touchpoint anchor: BHist BMark
  exact BorsukUlamTasteGate_single_carrier_alignment_ChapterTasteGate

end BEDC.Derived.BorsukUlamUp
