import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.VanDerCorputDifferenceEstimateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive VanDerCorputDifferenceEstimateUp : Type where
  | mk (A W S D Gamma M R E H C P N : BHist) : VanDerCorputDifferenceEstimateUp
  deriving DecidableEq

def vanDerCorputDifferenceEstimateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: vanDerCorputDifferenceEstimateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: vanDerCorputDifferenceEstimateEncodeBHist h

def vanDerCorputDifferenceEstimateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (vanDerCorputDifferenceEstimateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (vanDerCorputDifferenceEstimateDecodeBHist tail)

private theorem VanDerCorputDifferenceEstimateTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      vanDerCorputDifferenceEstimateDecodeBHist
        (vanDerCorputDifferenceEstimateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def vanDerCorputDifferenceEstimateFields :
    VanDerCorputDifferenceEstimateUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | VanDerCorputDifferenceEstimateUp.mk A W S D Gamma M R E H C P N =>
      [A, W, S, D, Gamma, M, R, E, H, C, P, N]

def vanDerCorputDifferenceEstimateToEventFlow :
    VanDerCorputDifferenceEstimateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (vanDerCorputDifferenceEstimateFields x).map
        vanDerCorputDifferenceEstimateEncodeBHist

private def vanDerCorputDifferenceEstimateEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      vanDerCorputDifferenceEstimateEventAtDefault index rest

def vanDerCorputDifferenceEstimateFromEventFlow :
    EventFlow → Option VanDerCorputDifferenceEstimateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (VanDerCorputDifferenceEstimateUp.mk
        (vanDerCorputDifferenceEstimateDecodeBHist
          (vanDerCorputDifferenceEstimateEventAtDefault 0 ef))
        (vanDerCorputDifferenceEstimateDecodeBHist
          (vanDerCorputDifferenceEstimateEventAtDefault 1 ef))
        (vanDerCorputDifferenceEstimateDecodeBHist
          (vanDerCorputDifferenceEstimateEventAtDefault 2 ef))
        (vanDerCorputDifferenceEstimateDecodeBHist
          (vanDerCorputDifferenceEstimateEventAtDefault 3 ef))
        (vanDerCorputDifferenceEstimateDecodeBHist
          (vanDerCorputDifferenceEstimateEventAtDefault 4 ef))
        (vanDerCorputDifferenceEstimateDecodeBHist
          (vanDerCorputDifferenceEstimateEventAtDefault 5 ef))
        (vanDerCorputDifferenceEstimateDecodeBHist
          (vanDerCorputDifferenceEstimateEventAtDefault 6 ef))
        (vanDerCorputDifferenceEstimateDecodeBHist
          (vanDerCorputDifferenceEstimateEventAtDefault 7 ef))
        (vanDerCorputDifferenceEstimateDecodeBHist
          (vanDerCorputDifferenceEstimateEventAtDefault 8 ef))
        (vanDerCorputDifferenceEstimateDecodeBHist
          (vanDerCorputDifferenceEstimateEventAtDefault 9 ef))
        (vanDerCorputDifferenceEstimateDecodeBHist
          (vanDerCorputDifferenceEstimateEventAtDefault 10 ef))
        (vanDerCorputDifferenceEstimateDecodeBHist
          (vanDerCorputDifferenceEstimateEventAtDefault 11 ef)))

private theorem VanDerCorputDifferenceEstimateTasteGate_single_carrier_alignment_round_trip :
    ∀ x : VanDerCorputDifferenceEstimateUp,
      vanDerCorputDifferenceEstimateFromEventFlow
        (vanDerCorputDifferenceEstimateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk A W S D Gamma M R E H C P N =>
      change
        some
          (VanDerCorputDifferenceEstimateUp.mk
            (vanDerCorputDifferenceEstimateDecodeBHist
              (vanDerCorputDifferenceEstimateEncodeBHist A))
            (vanDerCorputDifferenceEstimateDecodeBHist
              (vanDerCorputDifferenceEstimateEncodeBHist W))
            (vanDerCorputDifferenceEstimateDecodeBHist
              (vanDerCorputDifferenceEstimateEncodeBHist S))
            (vanDerCorputDifferenceEstimateDecodeBHist
              (vanDerCorputDifferenceEstimateEncodeBHist D))
            (vanDerCorputDifferenceEstimateDecodeBHist
              (vanDerCorputDifferenceEstimateEncodeBHist Gamma))
            (vanDerCorputDifferenceEstimateDecodeBHist
              (vanDerCorputDifferenceEstimateEncodeBHist M))
            (vanDerCorputDifferenceEstimateDecodeBHist
              (vanDerCorputDifferenceEstimateEncodeBHist R))
            (vanDerCorputDifferenceEstimateDecodeBHist
              (vanDerCorputDifferenceEstimateEncodeBHist E))
            (vanDerCorputDifferenceEstimateDecodeBHist
              (vanDerCorputDifferenceEstimateEncodeBHist H))
            (vanDerCorputDifferenceEstimateDecodeBHist
              (vanDerCorputDifferenceEstimateEncodeBHist C))
            (vanDerCorputDifferenceEstimateDecodeBHist
              (vanDerCorputDifferenceEstimateEncodeBHist P))
            (vanDerCorputDifferenceEstimateDecodeBHist
              (vanDerCorputDifferenceEstimateEncodeBHist N))) =
          some (VanDerCorputDifferenceEstimateUp.mk A W S D Gamma M R E H C P N)
      rw [VanDerCorputDifferenceEstimateTasteGate_single_carrier_alignment_decode_encode A,
        VanDerCorputDifferenceEstimateTasteGate_single_carrier_alignment_decode_encode W,
        VanDerCorputDifferenceEstimateTasteGate_single_carrier_alignment_decode_encode S,
        VanDerCorputDifferenceEstimateTasteGate_single_carrier_alignment_decode_encode D,
        VanDerCorputDifferenceEstimateTasteGate_single_carrier_alignment_decode_encode Gamma,
        VanDerCorputDifferenceEstimateTasteGate_single_carrier_alignment_decode_encode M,
        VanDerCorputDifferenceEstimateTasteGate_single_carrier_alignment_decode_encode R,
        VanDerCorputDifferenceEstimateTasteGate_single_carrier_alignment_decode_encode E,
        VanDerCorputDifferenceEstimateTasteGate_single_carrier_alignment_decode_encode H,
        VanDerCorputDifferenceEstimateTasteGate_single_carrier_alignment_decode_encode C,
        VanDerCorputDifferenceEstimateTasteGate_single_carrier_alignment_decode_encode P,
        VanDerCorputDifferenceEstimateTasteGate_single_carrier_alignment_decode_encode N]

private theorem VanDerCorputDifferenceEstimateTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : VanDerCorputDifferenceEstimateUp} :
    vanDerCorputDifferenceEstimateToEventFlow x =
      vanDerCorputDifferenceEstimateToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      vanDerCorputDifferenceEstimateFromEventFlow
          (vanDerCorputDifferenceEstimateToEventFlow x) =
        vanDerCorputDifferenceEstimateFromEventFlow
          (vanDerCorputDifferenceEstimateToEventFlow y) :=
    congrArg vanDerCorputDifferenceEstimateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (VanDerCorputDifferenceEstimateTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (VanDerCorputDifferenceEstimateTasteGate_single_carrier_alignment_round_trip y)))

instance vanDerCorputDifferenceEstimateBHistCarrier :
    BHistCarrier VanDerCorputDifferenceEstimateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := vanDerCorputDifferenceEstimateToEventFlow
  fromEventFlow := vanDerCorputDifferenceEstimateFromEventFlow

instance vanDerCorputDifferenceEstimateChapterTasteGate :
    ChapterTasteGate VanDerCorputDifferenceEstimateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      vanDerCorputDifferenceEstimateFromEventFlow
        (vanDerCorputDifferenceEstimateToEventFlow x) = some x
    exact VanDerCorputDifferenceEstimateTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (VanDerCorputDifferenceEstimateTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

def taste_gate : ChapterTasteGate VanDerCorputDifferenceEstimateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  vanDerCorputDifferenceEstimateChapterTasteGate

theorem VanDerCorputDifferenceEstimateTasteGate_single_carrier_alignment :
    (forall h : BHist,
      vanDerCorputDifferenceEstimateDecodeBHist
        (vanDerCorputDifferenceEstimateEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier VanDerCorputDifferenceEstimateUp) ∧
        Nonempty (ChapterTasteGate VanDerCorputDifferenceEstimateUp) ∧
          vanDerCorputDifferenceEstimateEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  exact
    ⟨VanDerCorputDifferenceEstimateTasteGate_single_carrier_alignment_decode_encode,
      ⟨⟨vanDerCorputDifferenceEstimateBHistCarrier⟩,
        ⟨vanDerCorputDifferenceEstimateChapterTasteGate⟩, rfl⟩⟩

end BEDC.Derived.VanDerCorputDifferenceEstimateUp
