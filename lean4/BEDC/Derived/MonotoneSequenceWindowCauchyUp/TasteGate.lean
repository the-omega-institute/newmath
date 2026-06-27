import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MonotoneSequenceWindowCauchyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MonotoneSequenceWindowCauchyUp : Type where
  | mk (M W R T H C P N L : BHist) : MonotoneSequenceWindowCauchyUp
  deriving DecidableEq

def monotoneSequenceWindowCauchyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: monotoneSequenceWindowCauchyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: monotoneSequenceWindowCauchyEncodeBHist h

def monotoneSequenceWindowCauchyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (monotoneSequenceWindowCauchyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (monotoneSequenceWindowCauchyDecodeBHist tail)

private theorem MonotoneSequenceWindowCauchyTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      monotoneSequenceWindowCauchyDecodeBHist
        (monotoneSequenceWindowCauchyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def monotoneSequenceWindowCauchyFields :
    MonotoneSequenceWindowCauchyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MonotoneSequenceWindowCauchyUp.mk M W R T H C P N L =>
      [M, W, R, T, H, C, P, N, L]

def monotoneSequenceWindowCauchyToEventFlow :
    MonotoneSequenceWindowCauchyUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (monotoneSequenceWindowCauchyFields x).map
      monotoneSequenceWindowCauchyEncodeBHist

private def monotoneSequenceWindowCauchyEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      monotoneSequenceWindowCauchyEventAtDefault index rest

def monotoneSequenceWindowCauchyFromEventFlow :
    EventFlow → Option MonotoneSequenceWindowCauchyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (MonotoneSequenceWindowCauchyUp.mk
        (monotoneSequenceWindowCauchyDecodeBHist
          (monotoneSequenceWindowCauchyEventAtDefault 0 ef))
        (monotoneSequenceWindowCauchyDecodeBHist
          (monotoneSequenceWindowCauchyEventAtDefault 1 ef))
        (monotoneSequenceWindowCauchyDecodeBHist
          (monotoneSequenceWindowCauchyEventAtDefault 2 ef))
        (monotoneSequenceWindowCauchyDecodeBHist
          (monotoneSequenceWindowCauchyEventAtDefault 3 ef))
        (monotoneSequenceWindowCauchyDecodeBHist
          (monotoneSequenceWindowCauchyEventAtDefault 4 ef))
        (monotoneSequenceWindowCauchyDecodeBHist
          (monotoneSequenceWindowCauchyEventAtDefault 5 ef))
        (monotoneSequenceWindowCauchyDecodeBHist
          (monotoneSequenceWindowCauchyEventAtDefault 6 ef))
        (monotoneSequenceWindowCauchyDecodeBHist
          (monotoneSequenceWindowCauchyEventAtDefault 7 ef))
        (monotoneSequenceWindowCauchyDecodeBHist
          (monotoneSequenceWindowCauchyEventAtDefault 8 ef)))

private theorem MonotoneSequenceWindowCauchyTasteGate_single_carrier_alignment_round_trip :
    ∀ x : MonotoneSequenceWindowCauchyUp,
      monotoneSequenceWindowCauchyFromEventFlow
        (monotoneSequenceWindowCauchyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M W R T H C P N L =>
      change
        some
          (MonotoneSequenceWindowCauchyUp.mk
            (monotoneSequenceWindowCauchyDecodeBHist
              (monotoneSequenceWindowCauchyEncodeBHist M))
            (monotoneSequenceWindowCauchyDecodeBHist
              (monotoneSequenceWindowCauchyEncodeBHist W))
            (monotoneSequenceWindowCauchyDecodeBHist
              (monotoneSequenceWindowCauchyEncodeBHist R))
            (monotoneSequenceWindowCauchyDecodeBHist
              (monotoneSequenceWindowCauchyEncodeBHist T))
            (monotoneSequenceWindowCauchyDecodeBHist
              (monotoneSequenceWindowCauchyEncodeBHist H))
            (monotoneSequenceWindowCauchyDecodeBHist
              (monotoneSequenceWindowCauchyEncodeBHist C))
            (monotoneSequenceWindowCauchyDecodeBHist
              (monotoneSequenceWindowCauchyEncodeBHist P))
            (monotoneSequenceWindowCauchyDecodeBHist
              (monotoneSequenceWindowCauchyEncodeBHist N))
            (monotoneSequenceWindowCauchyDecodeBHist
              (monotoneSequenceWindowCauchyEncodeBHist L))) =
          some (MonotoneSequenceWindowCauchyUp.mk M W R T H C P N L)
      rw [MonotoneSequenceWindowCauchyTasteGate_single_carrier_alignment_decode_encode M,
        MonotoneSequenceWindowCauchyTasteGate_single_carrier_alignment_decode_encode W,
        MonotoneSequenceWindowCauchyTasteGate_single_carrier_alignment_decode_encode R,
        MonotoneSequenceWindowCauchyTasteGate_single_carrier_alignment_decode_encode T,
        MonotoneSequenceWindowCauchyTasteGate_single_carrier_alignment_decode_encode H,
        MonotoneSequenceWindowCauchyTasteGate_single_carrier_alignment_decode_encode C,
        MonotoneSequenceWindowCauchyTasteGate_single_carrier_alignment_decode_encode P,
        MonotoneSequenceWindowCauchyTasteGate_single_carrier_alignment_decode_encode N,
        MonotoneSequenceWindowCauchyTasteGate_single_carrier_alignment_decode_encode L]

private theorem MonotoneSequenceWindowCauchyTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MonotoneSequenceWindowCauchyUp} :
    monotoneSequenceWindowCauchyToEventFlow x =
      monotoneSequenceWindowCauchyToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      monotoneSequenceWindowCauchyFromEventFlow
          (monotoneSequenceWindowCauchyToEventFlow x) =
        monotoneSequenceWindowCauchyFromEventFlow
          (monotoneSequenceWindowCauchyToEventFlow y) :=
    congrArg monotoneSequenceWindowCauchyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (MonotoneSequenceWindowCauchyTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (MonotoneSequenceWindowCauchyTasteGate_single_carrier_alignment_round_trip y)))

instance monotoneSequenceWindowCauchyBHistCarrier :
    BHistCarrier MonotoneSequenceWindowCauchyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := monotoneSequenceWindowCauchyToEventFlow
  fromEventFlow := monotoneSequenceWindowCauchyFromEventFlow

instance monotoneSequenceWindowCauchyChapterTasteGate :
    ChapterTasteGate MonotoneSequenceWindowCauchyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      monotoneSequenceWindowCauchyFromEventFlow
        (monotoneSequenceWindowCauchyToEventFlow x) = some x
    exact MonotoneSequenceWindowCauchyTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (MonotoneSequenceWindowCauchyTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

theorem MonotoneSequenceWindowCauchyTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      monotoneSequenceWindowCauchyDecodeBHist
        (monotoneSequenceWindowCauchyEncodeBHist h) = h) ∧
      monotoneSequenceWindowCauchyFields
        (MonotoneSequenceWindowCauchyUp.mk BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact MonotoneSequenceWindowCauchyTasteGate_single_carrier_alignment_decode_encode
  · rfl

end BEDC.Derived.MonotoneSequenceWindowCauchyUp
