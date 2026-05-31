import BEDC.Derived.CauchyCompletionLiftUp
import BEDC.FKernel.Cont
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionLiftUp

open BEDC.Derived
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def CauchyCompletionLiftTasteGate_single_carrier_alignment_encode_bhist :
    BHist → RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 :: CauchyCompletionLiftTasteGate_single_carrier_alignment_encode_bhist h
  | BHist.e1 h =>
      BMark.b1 :: CauchyCompletionLiftTasteGate_single_carrier_alignment_encode_bhist h

def CauchyCompletionLiftTasteGate_single_carrier_alignment_decode_bhist :
    RawEvent → BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (CauchyCompletionLiftTasteGate_single_carrier_alignment_decode_bhist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (CauchyCompletionLiftTasteGate_single_carrier_alignment_decode_bhist tail)

private theorem CauchyCompletionLiftTasteGate_single_carrier_alignment_decode_encode_bhist :
    ∀ h : BHist,
      CauchyCompletionLiftTasteGate_single_carrier_alignment_decode_bhist
          (CauchyCompletionLiftTasteGate_single_carrier_alignment_encode_bhist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def CauchyCompletionLiftTasteGate_single_carrier_alignment_fields :
    BEDC.Derived.CauchyCompletionLiftUp → List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | BEDC.Derived.CauchyCompletionLiftUp.carrier S T F U E K R H C P N =>
      [S, T, F, U, E, K, R, H, C, P, N]

def CauchyCompletionLiftTasteGate_single_carrier_alignment_to_event_flow :
    BEDC.Derived.CauchyCompletionLiftUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | BEDC.Derived.CauchyCompletionLiftUp.carrier S T F U E K R H C P N =>
      [CauchyCompletionLiftTasteGate_single_carrier_alignment_encode_bhist S,
        CauchyCompletionLiftTasteGate_single_carrier_alignment_encode_bhist T,
        CauchyCompletionLiftTasteGate_single_carrier_alignment_encode_bhist F,
        CauchyCompletionLiftTasteGate_single_carrier_alignment_encode_bhist U,
        CauchyCompletionLiftTasteGate_single_carrier_alignment_encode_bhist E,
        CauchyCompletionLiftTasteGate_single_carrier_alignment_encode_bhist K,
        CauchyCompletionLiftTasteGate_single_carrier_alignment_encode_bhist R,
        CauchyCompletionLiftTasteGate_single_carrier_alignment_encode_bhist H,
        CauchyCompletionLiftTasteGate_single_carrier_alignment_encode_bhist C,
        CauchyCompletionLiftTasteGate_single_carrier_alignment_encode_bhist P,
        CauchyCompletionLiftTasteGate_single_carrier_alignment_encode_bhist N]

private def CauchyCompletionLiftTasteGate_single_carrier_alignment_event_at :
    Nat → EventFlow → RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      CauchyCompletionLiftTasteGate_single_carrier_alignment_event_at index rest

def CauchyCompletionLiftTasteGate_single_carrier_alignment_from_event_flow :
    EventFlow → Option BEDC.Derived.CauchyCompletionLiftUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (BEDC.Derived.CauchyCompletionLiftUp.carrier
        (CauchyCompletionLiftTasteGate_single_carrier_alignment_decode_bhist
          (CauchyCompletionLiftTasteGate_single_carrier_alignment_event_at 0 ef))
        (CauchyCompletionLiftTasteGate_single_carrier_alignment_decode_bhist
          (CauchyCompletionLiftTasteGate_single_carrier_alignment_event_at 1 ef))
        (CauchyCompletionLiftTasteGate_single_carrier_alignment_decode_bhist
          (CauchyCompletionLiftTasteGate_single_carrier_alignment_event_at 2 ef))
        (CauchyCompletionLiftTasteGate_single_carrier_alignment_decode_bhist
          (CauchyCompletionLiftTasteGate_single_carrier_alignment_event_at 3 ef))
        (CauchyCompletionLiftTasteGate_single_carrier_alignment_decode_bhist
          (CauchyCompletionLiftTasteGate_single_carrier_alignment_event_at 4 ef))
        (CauchyCompletionLiftTasteGate_single_carrier_alignment_decode_bhist
          (CauchyCompletionLiftTasteGate_single_carrier_alignment_event_at 5 ef))
        (CauchyCompletionLiftTasteGate_single_carrier_alignment_decode_bhist
          (CauchyCompletionLiftTasteGate_single_carrier_alignment_event_at 6 ef))
        (CauchyCompletionLiftTasteGate_single_carrier_alignment_decode_bhist
          (CauchyCompletionLiftTasteGate_single_carrier_alignment_event_at 7 ef))
        (CauchyCompletionLiftTasteGate_single_carrier_alignment_decode_bhist
          (CauchyCompletionLiftTasteGate_single_carrier_alignment_event_at 8 ef))
        (CauchyCompletionLiftTasteGate_single_carrier_alignment_decode_bhist
          (CauchyCompletionLiftTasteGate_single_carrier_alignment_event_at 9 ef))
        (CauchyCompletionLiftTasteGate_single_carrier_alignment_decode_bhist
          (CauchyCompletionLiftTasteGate_single_carrier_alignment_event_at 10 ef)))

private theorem CauchyCompletionLiftTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BEDC.Derived.CauchyCompletionLiftUp,
      CauchyCompletionLiftTasteGate_single_carrier_alignment_from_event_flow
          (CauchyCompletionLiftTasteGate_single_carrier_alignment_to_event_flow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | carrier S T F U E K R H C P N =>
      change
        some
            (BEDC.Derived.CauchyCompletionLiftUp.carrier
              (CauchyCompletionLiftTasteGate_single_carrier_alignment_decode_bhist
                (CauchyCompletionLiftTasteGate_single_carrier_alignment_encode_bhist S))
              (CauchyCompletionLiftTasteGate_single_carrier_alignment_decode_bhist
                (CauchyCompletionLiftTasteGate_single_carrier_alignment_encode_bhist T))
              (CauchyCompletionLiftTasteGate_single_carrier_alignment_decode_bhist
                (CauchyCompletionLiftTasteGate_single_carrier_alignment_encode_bhist F))
              (CauchyCompletionLiftTasteGate_single_carrier_alignment_decode_bhist
                (CauchyCompletionLiftTasteGate_single_carrier_alignment_encode_bhist U))
              (CauchyCompletionLiftTasteGate_single_carrier_alignment_decode_bhist
                (CauchyCompletionLiftTasteGate_single_carrier_alignment_encode_bhist E))
              (CauchyCompletionLiftTasteGate_single_carrier_alignment_decode_bhist
                (CauchyCompletionLiftTasteGate_single_carrier_alignment_encode_bhist K))
              (CauchyCompletionLiftTasteGate_single_carrier_alignment_decode_bhist
                (CauchyCompletionLiftTasteGate_single_carrier_alignment_encode_bhist R))
              (CauchyCompletionLiftTasteGate_single_carrier_alignment_decode_bhist
                (CauchyCompletionLiftTasteGate_single_carrier_alignment_encode_bhist H))
              (CauchyCompletionLiftTasteGate_single_carrier_alignment_decode_bhist
                (CauchyCompletionLiftTasteGate_single_carrier_alignment_encode_bhist C))
              (CauchyCompletionLiftTasteGate_single_carrier_alignment_decode_bhist
                (CauchyCompletionLiftTasteGate_single_carrier_alignment_encode_bhist P))
              (CauchyCompletionLiftTasteGate_single_carrier_alignment_decode_bhist
                (CauchyCompletionLiftTasteGate_single_carrier_alignment_encode_bhist N))) =
          some (BEDC.Derived.CauchyCompletionLiftUp.carrier S T F U E K R H C P N)
      rw [CauchyCompletionLiftTasteGate_single_carrier_alignment_decode_encode_bhist S,
        CauchyCompletionLiftTasteGate_single_carrier_alignment_decode_encode_bhist T,
        CauchyCompletionLiftTasteGate_single_carrier_alignment_decode_encode_bhist F,
        CauchyCompletionLiftTasteGate_single_carrier_alignment_decode_encode_bhist U,
        CauchyCompletionLiftTasteGate_single_carrier_alignment_decode_encode_bhist E,
        CauchyCompletionLiftTasteGate_single_carrier_alignment_decode_encode_bhist K,
        CauchyCompletionLiftTasteGate_single_carrier_alignment_decode_encode_bhist R,
        CauchyCompletionLiftTasteGate_single_carrier_alignment_decode_encode_bhist H,
        CauchyCompletionLiftTasteGate_single_carrier_alignment_decode_encode_bhist C,
        CauchyCompletionLiftTasteGate_single_carrier_alignment_decode_encode_bhist P,
        CauchyCompletionLiftTasteGate_single_carrier_alignment_decode_encode_bhist N]

private theorem CauchyCompletionLiftTasteGate_single_carrier_alignment_to_event_flow_injective
    {x y : BEDC.Derived.CauchyCompletionLiftUp} :
    CauchyCompletionLiftTasteGate_single_carrier_alignment_to_event_flow x =
        CauchyCompletionLiftTasteGate_single_carrier_alignment_to_event_flow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have hsome : some x = some y := by
    calc
      some x =
          CauchyCompletionLiftTasteGate_single_carrier_alignment_from_event_flow
            (CauchyCompletionLiftTasteGate_single_carrier_alignment_to_event_flow x) :=
        (CauchyCompletionLiftTasteGate_single_carrier_alignment_round_trip x).symm
      _ =
          CauchyCompletionLiftTasteGate_single_carrier_alignment_from_event_flow
            (CauchyCompletionLiftTasteGate_single_carrier_alignment_to_event_flow y) :=
        congrArg CauchyCompletionLiftTasteGate_single_carrier_alignment_from_event_flow hxy
      _ = some y := CauchyCompletionLiftTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj hsome

instance cauchyCompletionLiftBHistCarrier :
    BHistCarrier BEDC.Derived.CauchyCompletionLiftUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := CauchyCompletionLiftTasteGate_single_carrier_alignment_to_event_flow
  fromEventFlow := CauchyCompletionLiftTasteGate_single_carrier_alignment_from_event_flow

instance cauchyCompletionLiftChapterTasteGate :
    ChapterTasteGate BEDC.Derived.CauchyCompletionLiftUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      CauchyCompletionLiftTasteGate_single_carrier_alignment_from_event_flow
          (CauchyCompletionLiftTasteGate_single_carrier_alignment_to_event_flow x) =
        some x
    exact CauchyCompletionLiftTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyCompletionLiftTasteGate_single_carrier_alignment_to_event_flow_injective heq)

theorem CauchyCompletionLiftTasteGate_single_carrier_alignment :
    ∀ x : BEDC.Derived.CauchyCompletionLiftUp,
      ∃ S T F U E K R H C P N emptyRow : BHist,
        x = BEDC.Derived.CauchyCompletionLiftUp.carrier S T F U E K R H C P N ∧
          emptyRow = BHist.Empty ∧
            CauchyCompletionLiftTasteGate_single_carrier_alignment_fields x =
              [S, T, F, U, E, K, R, H, C, P, N] ∧
              hsame emptyRow emptyRow := by
  -- BEDC touchpoint anchor: BHist hsame BMark
  intro x
  cases x with
  | carrier S T F U E K R H C P N =>
      exact ⟨S, T, F, U, E, K, R, H, C, P, N, BHist.Empty, rfl, rfl, rfl, rfl⟩

end BEDC.Derived.CauchyCompletionLiftUp
